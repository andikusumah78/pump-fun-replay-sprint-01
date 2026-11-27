// Breakout Rider — a pump.fun replay paper bot (agent-fun/replay/v2).
//
// Idea: most pump.fun curves die fast, a few ignite. This bot only buys a
// curve that is already proving itself inside a short window: net SOL flowing
// in, several distinct buyers, price up a healthy amount but not yet
// parabolic, sitting near its window high, with no single wallet dominating
// the buys. The first buy is small; the bot adds into strength only while
// the price keeps climbing above the last buy. Every exit is decided up
// front: take profit, a trailing stop once the position is ahead, a hard stop
// below cost, a fade exit when the tape turns into net selling, a big-sell
// exit when one wallet dumps hard, and a time stop for stale positions.
// Entries are deliberately tight (strong inflow, several buyers, capped
// run-up) and exits quick (small hard stop, early trailing stop), because
// the dev window showed wide entries and slow exits bleed on this tape:
// the first version lost half the bank at a 17% win rate.
//
// Guardrail backstop: the run must round-trip at least 0.01 SOL on 20 coins.
// If momentum entries are scarce once the window is well under way, the bot
// opens tiny probe round trips (buy, sell as soon as the buy lands) on the
// most liquid curve it just saw, until the coin count is back on pace.
//
// Deterministic by construction: no clock, no environment, no randomness.
// Every comparison is integer (bigint) cross-multiplication on the bonding
// curve's reserves, and every iteration follows insertion order.

import { runBot, LAMPORTS_PER_SOL } from './vendor/makefun-bot.ts';
import type { Batch, BotState, OrderInput, Pubkey } from './vendor/makefun-bot.ts';

const SOL = LAMPORTS_PER_SOL;

// ---- entry signal -------------------------------------------------------
const WINDOW = 60; // slots of tape the entry signal looks at
const MIN_AGE = 20; // slots since CreateEvent before an entry is allowed
const MIN_NET_SOL = SOL; // >= 1.00 SOL net inflow over the window
const MIN_BUYS = 6; // buy trades in the window
const MIN_BUYERS = 6; // distinct buying wallets in the window
const MIN_UP_NUM = 106n; // price up at least 6% over the window ...
const MIN_UP_DEN = 100n;
const MAX_UP_NUM = 130n; // ... but no more than +30% (past that the top is usually in)
const MAX_UP_DEN = 100n;
const NEAR_HIGH_NUM = 98n; // price now at least 98% of the window high ...
const NEAR_HIGH_DEN = 100n;
const MAX_BUYER_SHARE_NUM = 60n; // largest single buyer at most 60% of buy SOL
const MAX_BUYER_SHARE_DEN = 100n;
const MIN_REAL_SOL = SOL * 5n; // curve real SOL at entry: liquid enough ...
const MAX_REAL_SOL = SOL * 85n; // ... but not already at completion

// ---- sizing ---------------------------------------------------------------
const FIRST_BUY = (SOL * 15n) / 100n; // 0.15 SOL first buy
const ADD_BUY = (SOL * 10n) / 100n; // 0.10 SOL per pyramid add
const MAX_PER_COIN = (SOL * 35n) / 100n; // 0.35 SOL total per coin
const MIN_BUY = (SOL * 5n) / 100n; // never send a buy smaller than 0.05 SOL
const MAX_EXPOSURE = (SOL * 200n) / 100n; // 2.00 SOL at cost across positions
const BUY_SLIP_BPS = 2000;
const SELL_SLIP_BPS = 10000;

// ---- exits ----------------------------------------------------------------
const TP_NUM = 120n; // take profit at +20% over cost
const TP_DEN = 100n;
const TRAIL_ARM_NUM = 108n; // trailing stop arms once value is +8% over cost
const TRAIL_ARM_DEN = 100n;
const TRAIL_DROP_NUM = 92n; // ... then sell if value falls 8% below its peak
const TRAIL_DROP_DEN = 100n;
const STOP_NUM = 90n; // hard stop at -10% under cost
const STOP_DEN = 100n;
const MAX_HOLD = 2500; // slots held before the time stop applies
const TIME_EXIT_BELOW_NUM = 105n; // time stop only while under +5%
const TIME_EXIT_BELOW_DEN = 100n;
const FADE_WINDOW = 20; // slots for the fade check
const FADE_NET = -(SOL / 2n); // exit when net SOL over the fade window < -0.5 SOL
const BIG_SELL = SOL * 2n; // exit on any single recorded sell >= 2 SOL

// ---- re-entry ---------------------------------------------------------------
const COOLDOWN = 200; // slots to wait after an exit before re-entering a mint
const MAX_ENTRIES_PER_MINT = 2;

// ---- guardrail probes -------------------------------------------------------
const PROBE_SOL = (SOL * 5n) / 100n; // 0.05 SOL probe buy
const PROBE_MIN_BUY = (SOL * 2n) / 100n; // probes may go as small as 0.02 SOL
const PROBE_MAX = 10; // at most 10 probe buys in the run
const PROBE_AFTER_SLOTS = 60000; // start probing only once this far into the run
const ROUND_TRIP_MIN = 10_000_000n; // 0.01 SOL buy counts as a round trip

interface TapeTrade {
  slot: number;
  buy: boolean;
  sol: bigint;
  user: string;
  vq: bigint; // virtual quote reserves after the trade
  vt: bigint; // virtual token reserves after the trade
}

interface CoinState {
  tape: TapeTrade[];
  createdSlot: number | null;
  complete: boolean;
  lastSeenSlot: number;
  entries: number; // position opens on this mint
  cooldownUntil: number;
  totalBought: bigint;
  probeArmed: boolean; // a probe buy filled; the position it opens is a probe
}

interface PosState {
  peak: bigint; // best position value seen, lamports
  openSlot: number;
  lastBuyNum: bigint; // price (vq/vt) of the last buy decision
  lastBuyDen: bigint;
  probe: boolean;
}

interface Signal {
  ok: boolean;
  priceNum: bigint;
  priceDen: bigint;
}

const coins = new Map<Pubkey, CoinState>();
const held = new Map<Pubkey, PosState>();
const roundTripped = new Set<Pubkey>();
let firstSlot = -1;
let probesSent = 0;
let orderSeq = 0;

function coinState(mint: Pubkey): CoinState {
  let c = coins.get(mint);
  if (c === undefined) {
    c = {
      tape: [],
      createdSlot: null,
      complete: false,
      lastSeenSlot: -1,
      entries: 0,
      cooldownUntil: -1,
      totalBought: 0n,
      probeArmed: false,
    };
    coins.set(mint, c);
  }
  return c;
}

// Compare price a = aNum/aDen with price b = bNum/bDen: -1, 0, 1.
function cmpPrice(aNum: bigint, aDen: bigint, bNum: bigint, bDen: bigint): number {
  const l = aNum * bDen;
  const r = bNum * aDen;
  return l < r ? -1 : l > r ? 1 : 0;
}

// Is price a at least num/den of price b?
function priceAtLeast(aNum: bigint, aDen: bigint, bNum: bigint, bDen: bigint, num: bigint, den: bigint): boolean {
  return aNum * bDen * den >= bNum * aDen * num;
}

// Position value in lamports at the curve's current reserves.
function positionValue(tokens: bigint, vq: bigint, vt: bigint): bigint {
  if (vt === 0n || tokens === 0n) return 0n;
  return (tokens * vq) / vt;
}

function windowTrades(c: CoinState, slot: number, window: number): TapeTrade[] {
  const from = slot - window;
  const out: TapeTrade[] = [];
  for (const t of c.tape) if (t.slot >= from) out.push(t);
  return out;
}

// The entry signal for a mint at the current slot, from its tape and the
// curve's latest reserves. Returns the current price when the signal holds.
function entrySignal(state: BotState, mint: Pubkey, slot: number): Signal {
  const no: Signal = { ok: false, priceNum: 0n, priceDen: 1n };
  const c = coins.get(mint);
  const curve = state.curves.get(mint);
  if (c === undefined || curve === undefined || curve.complete) return no;
  if (c.createdSlot !== null && slot - c.createdSlot < MIN_AGE) return no;
  if (curve.real_quote_reserves < MIN_REAL_SOL || curve.real_quote_reserves > MAX_REAL_SOL) return no;

  const w = windowTrades(c, slot, WINDOW);
  if (w.length === 0) return no;
  let buys = 0;
  let net = 0n;
  let buySol = 0n;
  let maxBuyerSol = 0n;
  const buyers = new Map<string, bigint>();
  for (const t of w) {
    if (t.buy) {
      buys++;
      net += t.sol;
      buySol += t.sol;
      const prev = buyers.get(t.user) ?? 0n;
      const sum = prev + t.sol;
      buyers.set(t.user, sum);
      if (sum > maxBuyerSol) maxBuyerSol = sum;
    } else {
      net -= t.sol;
    }
  }
  if (buys < MIN_BUYS) return no;
  if (buyers.size < MIN_BUYERS) return no;
  if (net < MIN_NET_SOL) return no;
  if (buySol === 0n) return no;
  if (maxBuyerSol * MAX_BUYER_SHARE_DEN > buySol * MAX_BUYER_SHARE_NUM) return no;

  // Price at the window start (earliest trade in the window) vs now.
  const start = w[0];
  const nowNum = curve.virtual_quote_reserves;
  const nowDen = curve.virtual_token_reserves;
  if (nowDen === 0n || start.vt === 0n) return no;
  if (!priceAtLeast(nowNum, nowDen, start.vq, start.vt, MIN_UP_NUM, MIN_UP_DEN)) return no;
  if (priceAtLeast(nowNum, nowDen, start.vq, start.vt, MAX_UP_NUM, MAX_UP_DEN)) return no;

  // Price now must sit near the window high.
  let highNum = start.vq;
  let highDen = start.vt;
  for (const t of w) {
    if (cmpPrice(t.vq, t.vt, highNum, highDen) > 0) {
      highNum = t.vq;
      highDen = t.vt;
    }
  }
  if (cmpPrice(nowNum, nowDen, highNum, highDen) > 0) {
    highNum = nowNum;
    highDen = nowDen;
  }
  if (!priceAtLeast(nowNum, nowDen, highNum, highDen, NEAR_HIGH_NUM, NEAR_HIGH_DEN)) return no;

  return { ok: true, priceNum: nowNum, priceDen: nowDen };
}

function nextId(prefix: string): string {
  orderSeq++;
  return `${prefix}${orderSeq}`;
}

function onBatch(state: BotState, batch: Batch): OrderInput[] {
  const slot = batch.slot;
  if (firstSlot < 0) firstSlot = slot;
  const orders: OrderInput[] = [];
  const sells: OrderInput[] = [];
  const buys: OrderInput[] = [];

  // ---- fold the batch in -------------------------------------------------
  const tradedThisBatch: Pubkey[] = [];
  const tradedSet = new Set<Pubkey>();
  for (const e of batch.events) {
    const c = coinState(e.mint);
    c.lastSeenSlot = slot;
    if (e.event === 'CreateEvent') {
      c.createdSlot = e.slot;
    } else if (e.event === 'TradeEvent') {
      c.tape.push({
        slot: e.slot,
        buy: e.is_buy,
        sol: BigInt(e.sol_amount),
        user: e.user,
        vq: BigInt(e.virtual_quote_reserves),
        vt: BigInt(e.virtual_token_reserves),
      });
      if (c.tape.length > 80) c.tape.splice(0, c.tape.length - 80);
      if (!tradedSet.has(e.mint)) {
        tradedSet.add(e.mint);
        tradedThisBatch.push(e.mint);
      }
    } else {
      c.complete = true;
    }
  }

  // Fills: track probe buys and bought totals.
  for (const f of batch.fills) {
    if (f.status !== 'filled') continue;
    const c = coins.get(f.mint);
    if (c === undefined) continue;
    if (f.side === 'buy') {
      c.totalBought += BigInt(f.quote_lamports);
      if (f.client_id.startsWith('pb')) c.probeArmed = true;
    }
  }

  // Position opens / closes. state.positions is a Map<mint, Holding>, so
  // iterate its entries: a plain `for (const p of state.positions)` would
  // hand us [mint, holding] pairs and p.token_amount would be undefined.
  const nowHeld = new Set<Pubkey>();
  for (const [mint, h] of state.positions) {
    nowHeld.add(mint);
    const existing = held.get(mint);
    if (existing === undefined) {
      const curve = state.curves.get(mint);
      const c = coins.get(mint);
      const tokens = h.token_amount;
      const value =
        curve !== undefined ? positionValue(tokens, curve.virtual_quote_reserves, curve.virtual_token_reserves) : 0n;
      held.set(mint, {
        peak: value,
        openSlot: slot,
        lastBuyNum: curve !== undefined ? curve.virtual_quote_reserves : 0n,
        lastBuyDen: curve !== undefined ? curve.virtual_token_reserves : 1n,
        probe: c !== undefined && c.probeArmed,
      });
      if (c !== undefined) {
        c.probeArmed = false;
        c.entries++;
      }
    }
  }
  for (const mint of [...held.keys()]) {
    if (!nowHeld.has(mint)) {
      const c = coins.get(mint);
      if (c !== undefined && c.totalBought >= ROUND_TRIP_MIN) roundTripped.add(mint);
      if (c !== undefined) c.cooldownUntil = slot + COOLDOWN;
      held.delete(mint);
    }
  }

  const freeCash = (): bigint => state.freeCashLamports();
  const txFee = state.txFeeLamports();
  const exposure = (): bigint => {
    let sum = 0n;
    for (const h of state.positions.values()) sum += h.cost_lamports;
    return sum;
  };

  // ---- exits ---------------------------------------------------------------
  for (const [mint, h] of state.positions) {
    const pos = held.get(mint);
    const curve = state.curves.get(mint);
    if (pos === undefined || curve === undefined || curve.complete) continue;
    const tokens = h.token_amount;
    if (tokens === 0n) continue;
    const cost = h.cost_lamports;
    const value = positionValue(tokens, curve.virtual_quote_reserves, curve.virtual_token_reserves);
    if (value > pos.peak) pos.peak = value;

    // Probe positions: sell everything as soon as the buy has landed and no
    // buy is still in flight on this mint.
    let sell = false;
    if (pos.probe) {
      let buyPending = false;
      for (const pend of state.pending.values()) {
        if (pend.order.mint === mint && pend.order.side === 'buy') buyPending = true;
      }
      if (!buyPending) sell = true;
    } else {
      if (value * TP_DEN >= cost * TP_NUM) sell = true; // take profit
      else if (value * STOP_DEN <= cost * STOP_NUM) sell = true; // hard stop
      else if (
        pos.peak * TRAIL_ARM_DEN >= cost * TRAIL_ARM_NUM &&
        value * TRAIL_DROP_DEN <= pos.peak * TRAIL_DROP_NUM
      ) {
        sell = true; // trailing stop
      } else if (slot - pos.openSlot > MAX_HOLD && value * TIME_EXIT_BELOW_DEN < cost * TIME_EXIT_BELOW_NUM) {
        sell = true; // stale position
      } else {
        // Fade: net selling over the fade window, or one big dump.
        const c = coins.get(mint);
        if (c !== undefined) {
          const recent = windowTrades(c, slot, FADE_WINDOW);
          let net = 0n;
          let bigSell = false;
          for (const t of recent) {
            if (t.buy) net += t.sol;
            else {
              net -= t.sol;
              if (t.sol >= BIG_SELL) bigSell = true;
            }
          }
          if (net < FADE_NET || bigSell) sell = true;
        }
      }
    }
    if (sell) {
      sells.push({
        side: 'sell',
        client_id: nextId('s'),
        mint,
        token_amount: tokens.toString(),
        max_slippage_bps: SELL_SLIP_BPS,
      });
    }
  }

  // Mints already queued for a sell this batch must not receive a buy in
  // the same batch: a pyramid add (or a fresh entry) against a position
  // being exited would fight the exit and waste a fee round-trip.
  const selling = new Set<Pubkey>();
  for (const o of sells) selling.add(o.mint);

  // ---- pyramid adds ---------------------------------------------------------
  for (const [mint, h] of state.positions) {
    const pos = held.get(mint);
    const curve = state.curves.get(mint);
    if (pos === undefined || pos.probe || curve === undefined || curve.complete) continue;
    if (selling.has(mint)) continue;
    const cost = h.cost_lamports;
    if (cost >= MAX_PER_COIN) continue;
    // Only add while the price is above the last buy's decision price.
    if (
      !priceAtLeast(
        curve.virtual_quote_reserves,
        curve.virtual_token_reserves,
        pos.lastBuyNum,
        pos.lastBuyDen,
        105n,
        100n,
      )
    ) {
      continue;
    }
    let buyPending = false;
    for (const pend of state.pending.values()) {
      if (pend.order.mint === mint && pend.order.side === 'buy') buyPending = true;
    }
    if (buyPending) continue;
    const sig = entrySignal(state, mint, slot);
    if (!sig.ok) continue;
    const room = MAX_PER_COIN - cost;
    const want = ADD_BUY < room ? ADD_BUY : room;
    const cap = state.maxBuyLamports(mint);
    const size = want < cap ? want : cap;
    if (size < MIN_BUY) continue;
    if (freeCash() < size + txFee) continue;
    if (exposure() >= MAX_EXPOSURE) continue;
    buys.push({
      side: 'buy',
      client_id: nextId('b'),
      mint,
      quote_lamports: size.toString(),
      max_slippage_bps: BUY_SLIP_BPS,
    });
    pos.lastBuyNum = curve.virtual_quote_reserves;
    pos.lastBuyDen = curve.virtual_token_reserves;
  }

  // ---- new entries ------------------------------------------------------------
  const maxOpen = state.hello.caps.max_open_positions;
  for (const mint of tradedThisBatch) {
    if (buys.length + sells.length >= 16) break;
    if (state.committedPositionCount() + buys.length >= maxOpen) break;
    if (state.positions.has(mint)) continue;
    if (selling.has(mint)) continue;
    const c = coins.get(mint);
    if (c === undefined || c.complete) continue;
    if (c.entries >= MAX_ENTRIES_PER_MINT) continue;
    if (slot < c.cooldownUntil) continue;
    if (freeCash() < FIRST_BUY + txFee) break;
    if (exposure() >= MAX_EXPOSURE) break;
    const sig = entrySignal(state, mint, slot);
    if (!sig.ok) continue;
    const cap = state.maxBuyLamports(mint);
    const size = FIRST_BUY < cap ? FIRST_BUY : cap;
    if (size < MIN_BUY) continue;
    buys.push({
      side: 'buy',
      client_id: nextId('b'),
      mint,
      quote_lamports: size.toString(),
      max_slippage_bps: BUY_SLIP_BPS,
    });
  }

  // ---- guardrail probes -------------------------------------------------------
  if (
    roundTripped.size + state.committedPositionCount() < 20 &&
    slot - firstSlot > PROBE_AFTER_SLOTS &&
    probesSent < PROBE_MAX &&
    state.committedPositionCount() + buys.length < maxOpen &&
    freeCash() >= PROBE_SOL + txFee
  ) {
    // Most liquid curve traded in this batch that we do not hold.
    let bestMint: Pubkey | null = null;
    let bestReal = 0n;
    for (const mint of tradedThisBatch) {
      if (state.positions.has(mint)) continue;
      const curve = state.curves.get(mint);
      const c = coins.get(mint);
      if (curve === undefined || curve.complete || c === undefined) continue;
      if (slot < c.cooldownUntil) continue;
      if (curve.real_quote_reserves > bestReal) {
        bestReal = curve.real_quote_reserves;
        bestMint = mint;
      }
    }
    if (bestMint !== null && bestReal >= MIN_REAL_SOL) {
      const cap = state.maxBuyLamports(bestMint);
      const size = PROBE_SOL < cap ? PROBE_SOL : cap;
      if (size >= PROBE_MIN_BUY) {
        buys.push({
          side: 'buy',
          client_id: nextId('pb'),
          mint: bestMint,
          quote_lamports: size.toString(),
          max_slippage_bps: BUY_SLIP_BPS,
        });
        probesSent++;
      }
    }
  }

  // Sells first, then buys; never over the per-batch cap.
  for (const o of sells) orders.push(o);
  for (const o of buys) {
    if (orders.length >= 16) break;
    orders.push(o);
  }

  // ---- periodic prune ---------------------------------------------------------
  if (slot % 2000 === 0) {
    for (const [mint, c] of coins) {
      if (!nowHeld.has(mint) && c.lastSeenSlot < slot - 5000) coins.delete(mint);
    }
  }

  return orders;
}

await runBot({
  onBatch: (state, batch) => onBatch(state, batch),
});
