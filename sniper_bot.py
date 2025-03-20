import asyncio
import aiohttp
import logging
import random
import re
import signal
import sys
import os
import json
import time
from typing import Any, Dict, List, Set, Optional
from logging.handlers import RotatingFileHandler
from solana.rpc.async_api import AsyncClient
from solana.rpc import commitment
from solana.rpc.types import TxOpts, TokenAccountOpts
from solders.keypair import Keypair
from solders.transaction import VersionedTransaction
from solders.signature import Signature
from solders.pubkey import Pubkey
from aiolimiter import AsyncLimiter
from prometheus_client import start_http_server, Counter, Gauge, Histogram
from aiohttp import WSMsgType, ClientTimeout, ClientResponseError
from backoff import expo, on_exception
import async_timeout

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from config.settings import settings
from bot.exceptions import SwapError
from bot.utils import (
    get_cached_data,
    calculate_congestion,
    validate_jupiter_quote,
    validate_raydium_response,
    validate_pubkey
)

# Константи
RAYDIUM_PROGRAM_ID = Pubkey.from_string("675kPX9MHTjS2zt1qfr1NYHuzeLXfQM9H24wFSUt1Mp8")
SOL_MINT = "So11111111111111111111111111111111111111112"
JUPITER_QUOTE_API = "https://quote-api.jup.ag/v6/quote"
JUPITER_SWAP_API = "https://quote-api.jup.ag/v6/swap"
BIRDEYE_API = "https://public-api.birdeye.so/defi/pool"
DEXSCREENER_API = "https://api.dexscreener.com/latest/dex/pairs/solana/"
RAYDIUM_ENDPOINTS = [
    "https://api.raydium.io/v2/sdk/liquidity/mainnet.json",
    "https://cache.jup.ag/raydium"
]
BLACKLIST_PATTERNS = [
    r'A[A-Za-z0-9]{8}AAAAAA',
    r'^[AQ]{5}',
    r'=+$',
    r'\.{3}',
    r'\[.*\]'
]
HEADERS = {
    "User-Agent": settings.USER_AGENT,
    "Accept": "application/json",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": "https://raydium.io/",
    "Origin": "https://raydium.io"
}

class TrailingStop:
    def __init__(self, initial_price: float, trail_percent: float):
        self.peak_price = initial_price
        self.trail_percent = trail_percent
        self.stop_price = initial_price * (1 - trail_percent / 100)

    def update(self, current_price: float) -> None:
        if current_price > self.peak_price:
            self.peak_price = current_price
        self.stop_price = current_price * (1 - self.trail_percent / 100)

class SniperBot:
    def __init__(self):
        self._init_logging()
        self.current_rpc_index = 0
        self.rpc_urls = settings.RPC_URLS
        self.client = self._create_rpc_client()
        self.wallet = Keypair.from_base58_string(settings.PRIVATE_KEY)
        self.limiters = self._init_limiters()
        self.semaphore = asyncio.Semaphore(settings.MAX_PARALLEL_TASKS)
        self.shutdown_flag = False
        self._sessions = []
        self.active_tasks: Set[asyncio.Task] = set()
        self.seen_pools: Set[str] = set()
        self.raydium_cache: Dict[str, Any] = {}
        self.raydium_last_request = 0.0
        self.loop = asyncio.get_event_loop()

        # Метрики
        self.swap_counter = Counter("sniper_swaps", "Total swaps performed")
        self.profit_gauge = Gauge("sniper_profit", "Current profit percentage")
        self.error_counter = Counter("sniper_errors", "Total errors", ["type"])
        self.api_latency = Histogram("api_latency", "API response latency", ["endpoint"])
        start_http_server(8000)

        signal.signal(signal.SIGINT, self.handle_shutdown)
        signal.signal(signal.SIGTERM, self.handle_shutdown)

    def _init_logging(self) -> None:
        handler = RotatingFileHandler(
            "sniper.log",
            maxBytes=10 * 1024 * 1024,
            backupCount=5
        )
        logging.basicConfig(
            level=getattr(logging, settings.DEBUG_LEVEL),
            format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
            handlers=[handler, logging.StreamHandler()]
        )
        self.logger = logging.getLogger(__name__)

    @staticmethod
    def _init_limiters() -> Dict[str, AsyncLimiter]:
        return {
            "jupiter": AsyncLimiter(settings.JUPITER_RATE_LIMIT, 1),
            "solscan": AsyncLimiter(settings.SOLSCAN_RATE_LIMIT, 1),
            "raydium": AsyncLimiter(settings.RAYDIUM_RATE_LIMIT, 60),
            "birdeye": AsyncLimiter(5, 1),
            "rpc": AsyncLimiter(settings.RPC_RATE_LIMIT, 1),
            "dexscreener": AsyncLimiter(settings.DEXSCREENER_RATE_LIMIT, 1)
        }

    def _create_rpc_client(self) -> AsyncClient:
        return AsyncClient(
            self.rpc_urls[self.current_rpc_index],
            timeout=settings.RPC_TIMEOUT,
            commitment=commitment.Confirmed
        )

    async def __aenter__(self) -> "SniperBot":
        await self.initialize()
        return self

    async def __aexit__(self, *exc) -> None:
        await self._cleanup_resources()

    async def _cleanup_resources(self) -> None:
        try:
            tasks = []
            if self.client:
                tasks.append(self.client.close())
            for session in self._sessions:
                if not session.closed:
                    tasks.append(session.close())
            if tasks:
                await asyncio.gather(*tasks)

            for task in self.active_tasks:
                task.cancel()
            await asyncio.gather(*self.active_tasks, return_exceptions=True)

            self.logger.info("Resource cleanup completed")
        except Exception as error:
            self.logger.error(f"Cleanup error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="cleanup").inc()

    async def initialize(self) -> None:
        try:
            await self.client.get_block_height()
            self._sessions.append(aiohttp.ClientSession(
                timeout=ClientTimeout(total=settings.HTTP_TIMEOUT)
            ))
            self.logger.info("Initialization completed")
        except Exception as error:
            await self._cleanup_resources()
            self.error_counter.labels(type="init").inc()
            raise RuntimeError(f"Initialization failed: {error}") from error

    async def _rotate_rpc(self):
        self.current_rpc_index = (self.current_rpc_index + 1) % len(self.rpc_urls)
        await self.client.close()
        self.client = self._create_rpc_client()
        self.logger.info(f"Rotated to RPC: {self.rpc_urls[self.current_rpc_index]}")

    @on_exception(expo, Exception, max_tries=3)
    async def get_account_info_with_retry(self, pubkey: Pubkey) -> Optional[Any]:
        for _ in range(settings.MAX_RETRIES):
            try:
                async with self.limiters["rpc"]:
                    return await self.client.get_account_info(pubkey)
            except Exception as error:
                self.logger.warning(f"RPC error: {error}, rotating...")
                self.error_counter.labels(type="rpc").inc()
                await self._rotate_rpc()
                await asyncio.sleep(1)
        return None

    def handle_shutdown(self, _signum: int, _frame: Any) -> None:
        self.logger.warning("Shutdown signal received!")
        self.shutdown_flag = True

    async def check_balance(self) -> float:
        try:
            balance = (await self.client.get_balance(self.wallet.pubkey())).value / 1e9
            self.logger.info(f"💰 Current balance: {balance:.4f} SOL")
            return balance
        except Exception as error:
            self.logger.error(f"Balance check error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="balance").inc()
            return 0.0

    async def get_token_balance(self, token_address: str) -> float:
        try:
            async with self.limiters["rpc"]:
                mint = Pubkey.from_string(token_address)
                accounts = await self.client.get_token_accounts_by_owner(
                    self.wallet.pubkey(),
                    TokenAccountOpts(mint)
                )
                if not accounts.value:
                    return 0.0
                balance = await self.client.get_token_account_balance(accounts.value[0].pubkey)
                return balance.value.ui_amount
        except Exception as error:
            self.logger.error(f"Token balance check error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="token_balance").inc()
            return 0.0

    async def monitor_new_pools(self) -> None:
        while not self.shutdown_flag:
            session = aiohttp.ClientSession()
            self._sessions.append(session)

            try:
                ws_url = self.rpc_urls[self.current_rpc_index].replace("https", "wss", 1)
                self.logger.info(f"Attempting to connect to WebSocket: {ws_url}")
                async with session.ws_connect(
                        ws_url,
                        heartbeat=30,
                        timeout=ClientTimeout(total=120)
                ) as ws:
                    self.logger.info("WebSocket connected")
                    await self._handle_websocket(ws)
            except Exception as error:
                self.logger.error(f"WebSocket error: {str(error)}, reconnecting in {settings.WS_RECONNECT_DELAY}s", exc_info=True)
                self.error_counter.labels(type="websocket").inc()
                await session.close()
                await asyncio.sleep(settings.WS_RECONNECT_DELAY)
                await self._rotate_rpc()
            finally:
                await session.close()

    async def _handle_websocket(self, ws: aiohttp.ClientWebSocketResponse) -> None:
        await ws.send_json({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "logsSubscribe",
            "params": [{"mentions": [str(RAYDIUM_PROGRAM_ID)]}]
        })

        try:
            async for msg in ws:
                if self.shutdown_flag:
                    break
                if msg.type == WSMsgType.TEXT:
                    await self._process_ws_message(json.loads(msg.data))
                elif msg.type == WSMsgType.CLOSED:
                    self.logger.warning("WebSocket connection closed")
                    break
                elif msg.type == WSMsgType.ERROR:
                    self.logger.error(f"WebSocket error: {msg.data}", exc_info=True)
                    self.error_counter.labels(type="websocket").inc()
        except asyncio.CancelledError:
            await ws.close(code=1000)
        except Exception as error:
            self.logger.error(f"WebSocket error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="websocket").inc()

    async def _process_ws_message(self, data: Dict) -> None:
        try:
            if data.get("method") == "logsNotification":
                logs = data["params"]["result"]["value"]["logs"]
                self.logger.debug(f"Processing WebSocket logs: {logs[:200]}")
                await self._detect_new_pool(logs)
            else:
                self.logger.debug(f"Ignoring non-logsNotification message: {data.get('method')}")
        except KeyError as error:
            self.logger.error(f"Invalid message format: {str(error)}", exc_info=True)
            self.error_counter.labels(type="message_format").inc()

    async def _detect_new_pool(self, logs: List[str]) -> None:
        found_pools = set()

        for log in logs:
            if "initialize" in log.lower():
                possible_keys = re.findall(r'[1-9A-HJ-NP-Za-km-z]{32,44}', log)
                for key in possible_keys:
                    if validate_pubkey(key):
                        found_pools.add(key)

        new_pools = [p for p in found_pools if p not in self.seen_pools]
        if not new_pools:
            return

        self.logger.info(f"🔍 Found {len(new_pools)} new pools: {new_pools}")

        for pool_address in new_pools:
            self.seen_pools.add(pool_address)
            task = asyncio.create_task(self._process_pool(pool_address))
            self.active_tasks.add(task)
            task.add_done_callback(lambda t: self.active_tasks.remove(t))
            await asyncio.sleep(0.5)

    async def _process_pool(self, pool_address: str) -> None:
        try:
            account_info = await self.get_account_info_with_retry(Pubkey.from_string(pool_address))
            if not account_info or not account_info.value:
                self.logger.warning(f"❌ RPC: Pool {pool_address} does not exist")
                return

            if not await self._check_raydium_pool(pool_address):
                self.logger.warning(f"⚠️ Raydium: Pool {pool_address} not found")
                return

            if not await self._check_solscan_pool(pool_address):
                self.logger.warning(f"🔴 Solscan: Pool {pool_address} not found")
                return

            if not await self._check_birdeye_pool(pool_address):
                self.logger.warning(f"⚠️ Birdeye: Pool {pool_address} not found")
                return

            await self._analyze_and_swap(pool_address)
        except Exception as error:
            self.logger.error(f"Pool processing error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="pool_processing").inc()

    async def _check_raydium_pool(self, pool_address: str) -> bool:
        for endpoint in RAYDIUM_ENDPOINTS:
            try:
                if self.shutdown_flag:
                    return False

                if time.time() - self.raydium_last_request < 5.0:
                    await asyncio.sleep(5.0)

                start_time = time.time()
                async with async_timeout.timeout(10):
                    async with self.limiters["raydium"]:
                        self.raydium_last_request = time.time()
                        async with self._sessions[0].get(
                                endpoint,
                                headers=HEADERS,
                                timeout=ClientTimeout(total=10.0)
                        ) as response:

                            self.api_latency.labels(endpoint=endpoint).observe(time.time() - start_time)

                            if response.status == 403:
                                self.logger.error("Cloudflare block detected, rotating endpoint")
                                continue

                            if response.status >= 500:
                                self.logger.warning(f"Server error {response.status}, trying next endpoint")
                                continue

                            if response.status == 429:
                                retry_after = int(response.headers.get("Retry-After", 30))
                                self.logger.warning(f"Rate limit hit. Retrying in {retry_after}s")
                                await asyncio.sleep(retry_after)
                                return await self._check_raydium_pool(pool_address)

                            content_type = response.headers.get("Content-Type", "")
                            if "application/json" not in content_type:
                                text = await response.text()
                                self.logger.error(f"Invalid response: {text[:200]}")
                                continue

                            data = await response.json()
                            validate_raydium_response(data)

                            result = any(p["id"] == pool_address for p in data["official"])
                            self.raydium_cache[endpoint] = {
                                "timestamp": time.time(),
                                "result": result
                            }
                            return result

            except asyncio.TimeoutError:
                self.logger.warning(f"Timeout connecting to {endpoint}")
                continue
            except Exception as error:
                self.logger.error(f"Raydium API error ({endpoint}): {str(error)}", exc_info=True)
                self.error_counter.labels(type="raydium_api").inc()
                continue

        return False

    async def _check_solscan_pool(self, pool_address: str) -> bool:
        for attempt in range(settings.MAX_RETRIES):
            try:
                async with self.limiters["solscan"]:
                    resp = await self._sessions[0].get(
                        f"https://api.solscan.io/amm/pool?id={pool_address}",
                        headers={"Authorization": f"Bearer {settings.SOLSCAN_API_KEY}"}
                    )

                    if resp.status == 200:
                        return True

                    if resp.status == 429:
                        retry_after = int(resp.headers.get("Retry-After", 30))
                        self.logger.warning(f"Solscan rate limit. Retry in {retry_after}s")
                        await asyncio.sleep(retry_after)
                        continue

                    await asyncio.sleep(settings.RETRY_DELAYS[attempt])
            except Exception as error:
                self.logger.error(f"Solscan check error: {str(error)}", exc_info=True)
                self.error_counter.labels(type="solscan").inc()
        return False

    async def _check_birdeye_pool(self, pool_address: str) -> bool:
        try:
            async with self.limiters["birdeye"]:
                async with self._sessions[0].get(
                        f"{BIRDEYE_API}?address={pool_address}"
                ) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        return data.get("data", {}).get("address") == pool_address
        except Exception as error:
            self.logger.error(f"Birdeye check error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="birdeye").inc()
        return False

    async def _analyze_and_swap(self, pool_address: str) -> None:
        async with self.semaphore:
            try:
                if await self._is_valid_pool(pool_address):
                    await self._swap(pool_address)
            except SwapError as error:
                self.logger.error(f"Swap error: {str(error)}", exc_info=True)
                self.error_counter.labels(type="swap").inc()

    async def _is_valid_pool(self, address: str) -> bool:
        try:
            async with self.limiters["dexscreener"]:
                dexscreener_data = await get_cached_data(
                    self._sessions[0],
                    f"{DEXSCREENER_API}{address}"
                )

                if not dexscreener_data.get("pair"):
                    self.logger.warning("DexScreener: Pool not found")
                    return False

                created_at = dexscreener_data["pair"].get("createdAt")
                if created_at and (time.time() - created_at / 1000 > settings.MAX_POOL_AGE_HOURS * 3600):
                    self.logger.info(f"Pool is too old (> {settings.MAX_POOL_AGE_HOURS} hours)")
                    return False

            raydium_data, holders_data = await asyncio.gather(
                get_cached_data(
                    self._sessions[0],
                    "https://api.raydium.io/v2/sdk/liquidity/mainnet.json"
                ),
                get_cached_data(
                    self._sessions[0],
                    f"https://api.solscan.io/token/holders?token={address}"
                ),
                return_exceptions=True
            )

            if isinstance(raydium_data, Exception):
                self.logger.error(f"Raydium API error: {str(raydium_data)}", exc_info=True)
                return False
            if isinstance(holders_data, Exception):
                self.logger.error(f"Solscan API error: {str(holders_data)}", exc_info=True)
                return False

            validate_raydium_response(raydium_data)

            pool_info = next(
                (p for p in raydium_data["official"]
                 if p["id"] == address and p["programId"] == str(RAYDIUM_PROGRAM_ID)),
                None
            )

            if not pool_info:
                self.logger.warning("Pool not found in Raydium official list")
                return False

            liquidity = pool_info.get("liquidity", {}).get("sol", 0)
            holders = holders_data.get("data", {}).get("total", 0)
            price_impact = await self._get_price_impact(address)

            self.logger.info(
                f"📊 Pool analysis:\n"
                f"  Liquidity: {liquidity} SOL (min {settings.MIN_LIQUIDITY})\n"
                f"  Holders: {holders} (min {settings.MIN_HOLDERS})\n"
                f"  Price Impact: {price_impact:.2f}% (max {settings.MAX_TAX_FEE}%)"
            )

            return all([
                liquidity >= settings.MIN_LIQUIDITY,
                holders >= settings.MIN_HOLDERS,
                price_impact < settings.MAX_TAX_FEE
            ])

        except Exception as error:
            self.logger.error(f"Pool analysis error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="analysis").inc()
            return False

    async def _get_price_impact(self, address: str) -> float:
        try:
            async with self.limiters["jupiter"]:
                quote = await get_cached_data(
                    self._sessions[0],
                    f"{JUPITER_QUOTE_API}?inputMint={SOL_MINT}&outputMint={address}&amount=100000000"
                )
                validate_jupiter_quote(quote)
                return quote.get("priceImpactPct", 1.0) * 100
        except Exception as error:
            self.logger.error(f"Price impact check error: {str(error)}", exc_info=True)
            return float('inf')

    async def _swap(self, token_address: str) -> None:
        if settings.TEST_MODE:
            self.logger.info("🛑 Test mode: swap simulated")
            return

        try:
            balance = await self.check_balance()
            required = settings.MAX_BUY_AMOUNT * 1.1
            if balance < required:
                raise SwapError(f"Insufficient SOL: {balance:.2f} < {required:.2f}")

            token_balance = await self.get_token_balance(token_address)
            if token_balance < required:
                raise SwapError(f"Insufficient token balance: {token_balance} < {required}")

            delay = random.uniform(*settings.ANTI_FRONT_RUN_DELAY)
            self.logger.info(f"⏳ Anti-frontrun delay: {delay:.2f}s")
            await asyncio.sleep(delay)

            current_balance = await self.check_balance()
            if current_balance < required:
                raise SwapError(f"Balance changed: {current_balance:.2f} < {required:.2f}")

            compute_price = await self._get_priority_fee()
            self.logger.info(f"⚡ Using priority fee: {compute_price} micro-lamports")

            quote_params = {
                "inputMint": SOL_MINT,
                "outputMint": token_address,
                "amount": int(settings.MAX_BUY_AMOUNT * 1e9),
                "slippage": settings.BASE_SLIPPAGE,
                "computeUnitPriceMicroLamports": compute_price
            }

            async with self.limiters["jupiter"]:
                quote = await get_cached_data(
                    self._sessions[0],
                    JUPITER_QUOTE_API,
                    params=quote_params
                )
                validate_jupiter_quote(quote)

            if float(quote['priceImpactPct']) * 100 > settings.MAX_TAX_FEE:
                raise SwapError(f"Price impact {float(quote['priceImpactPct']) * 100:.2f}% exceeds limit")

            async with self._sessions[0].post(
                    JUPITER_SWAP_API,
                    json={
                        "route": quote,
                        "userPublicKey": str(self.wallet.pubkey()),
                        "wrapUnwrapSOL": True,
                        "computeUnitPriceMicroLamports": compute_price
                    }
            ) as response:
                response.raise_for_status()
                swap_data = await response.json()

            tx = VersionedTransaction.from_bytes(bytes.fromhex(swap_data["swapTransaction"]))
            opts = TxOpts(
                skip_preflight=settings.SKIP_PREFLIGHT,
                preflight_commitment=commitment.Confirmed,
                max_retries=settings.TX_RETRIES,
            )

            txid = (await self.client.send_transaction(tx, opts=opts)).value
            self.logger.info(f"📤 Transaction sent: {txid}")

            await self._wait_for_confirmation(txid)

            self.swap_counter.inc()
            self.logger.info(f"🎉 Swap successful: https://solscan.io/tx/{txid}")
            await self._manage_profit(token_address, settings.MAX_BUY_AMOUNT)

        except ClientResponseError as error:
            self.logger.error(f"HTTP error {error.status}: {error.message}", exc_info=True)
            raise SwapError(f"HTTP error: {error.message}") from error
        except asyncio.TimeoutError:
            self.logger.error("Request timeout", exc_info=True)
            raise SwapError("Request timeout") from None
        except Exception as error:
            self.logger.error(f"Swap error: {str(error)}", exc_info=True)
            raise SwapError(str(error)) from error

    async def _get_priority_fee(self) -> int:
        try:
            congestion = await calculate_congestion(self._sessions[0])

            recent_fees_response = await self.client._provider.make_request(
                "getRecentPrioritizationFees",
                []
            )

            if recent_fees_response.error:
                raise ValueError(f"RPC Error: {recent_fees_response.error}")

            recent_fees = [fee["prioritizationFee"] for fee in recent_fees_response.result[:3]]
            avg_fee = sum(recent_fees) / 3 if recent_fees else 0

            dynamic_fee = max(
                int(settings.BASE_PRIORITY_FEE * (1 + congestion)),
                int(avg_fee * settings.PRIORITY_FEE_MULTIPLIER)
            )
            return min(dynamic_fee, settings.MAX_PRIORITY_FEE)
        except Exception as error:
            self.logger.error(f"Fee calculation error: {str(error)}", exc_info=True)
            return settings.BASE_PRIORITY_FEE

    async def _wait_for_confirmation(self, txid: Signature) -> None:
        for attempt in range(settings.TX_CONFIRMATION_ATTEMPTS):
            try:
                status = (await self.client.get_signature_statuses([txid])).value[0]
                if status:
                    if status.confirmation_status == "finalized":
                        self.logger.info("✅ Transaction finalized")
                        return
                    if status.err:
                        raise SwapError(f"Transaction failed: {status.err}")
                await asyncio.sleep(settings.TX_CONFIRMATION_DELAY)
            except Exception as error:
                self.logger.warning(f"Confirmation attempt {attempt + 1} failed: {str(error)}", exc_info=True)

        raise TimeoutError("Transaction not confirmed after maximum attempts")

    async def _manage_profit(self, token_address: str, amount: float) -> None:
        try:
            buy_price = await self._get_price(token_address)
            trailing_stop = TrailingStop(buy_price, settings.TRAILING_STOP_PERCENT)
            target_price = buy_price * (1 + settings.TAKE_PROFIT_PERCENT / 100)

            while not self.shutdown_flag:
                current_price = await self._get_price(token_address)
                trailing_stop.update(current_price)

                if current_price >= target_price or current_price <= trailing_stop.stop_price:
                    self.logger.info("🔔 Exit conditions met")
                    await self._sell(token_address, amount)
                    break

                await asyncio.sleep(settings.TAKE_PROFIT_CHECK_INTERVAL)

        except Exception as error:
            self.logger.error(f"Profit management error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="profit_management").inc()

    async def _sell(self, token_address: str, amount: float) -> None:
        try:
            for i in range(settings.BATCH_SELL_COUNT):
                self.logger.info(f"💸 Selling batch {i + 1}/{settings.BATCH_SELL_COUNT}")
                await self._execute_sell(token_address, amount / settings.BATCH_SELL_COUNT)
                await asyncio.sleep(settings.BATCH_SELL_DELAY)
        except Exception as error:
            self.logger.error(f"Sell error: {str(error)}", exc_info=True)
            self.error_counter.labels(type="sell").inc()

    async def _execute_sell(self, token_address: str, amount: float) -> None:
        try:
            compute_price = await self._get_priority_fee()

            quote = await get_cached_data(
                self._sessions[0],
                f"{JUPITER_QUOTE_API}?inputMint={token_address}&outputMint={SOL_MINT}&amount={int(amount * 1e9)}",
                params={"computeUnitPriceMicroLamports": compute_price}
            )
            validate_jupiter_quote(quote)

            async with self._sessions[0].post(
                    JUPITER_SWAP_API,
                    json={
                        "route": quote,
                        "userPublicKey": str(self.wallet.pubkey()),
                        "wrapUnwrapSOL": True,
                        "computeUnitPriceMicroLamports": compute_price
                    }
            ) as response:
                swap_data = await response.json()

            tx = VersionedTransaction.from_bytes(bytes.fromhex(swap_data["swapTransaction"]))
            txid = (await self.client.send_transaction(tx, opts=TxOpts(skip_preflight=True))).value
            self.logger.info(f"✅ Sell executed: https://solscan.io/tx/{txid}")

        except Exception as error:
            self.logger.error(f"Sell execution error: {str(error)}", exc_info=True)
            raise

    async def _get_price(self, token_address: str) -> float:
        try:
            data = await get_cached_data(
                self._sessions[0],
                f"{DEXSCREENER_API}{token_address}"
            )
            return float(data["pairs"][0]["priceUsd"])
        except Exception as error:
            self.logger.error(f"Price check error: {str(error)}", exc_info=True)
            return 0.0

    async def start(self) -> None:
        try:
            self.logger.info("🚀 Starting sniper bot...")
            async with self:
                while not self.shutdown_flag:
                    await self.monitor_new_pools()
                    await self._periodic_balance_check()
        except asyncio.CancelledError:
            self.logger.info("Bot stopped")
        except Exception as error:
            self.logger.error(f"Critical error: {str(error)}", exc_info=True)
        finally:
            await self._cleanup_resources()

    async def _periodic_balance_check(self) -> None:
        await asyncio.sleep(settings.BALANCE_CHECK_INTERVAL)
        await self.check_balance()

async def main():
    async with SniperBot() as bot:
        await bot.start()

if __name__ == "__main__":
    asyncio.run(main())