# NAND Recovery/Prevention — v1 Algorithm Detail Design

**Status:** detail design (2026-07-19). Scope: the v1 recovery + prevention
algorithm set for `examples/09_embedded/simpleos_nvme_fw`, validated against the
`src/lib/hardware/nand_emu` Vt model.

This document is the DETAIL DESIGN that implements the architecture
`doc/04_architecture/hardware/nand_recovery/reliability_engine_architecture.md`.
It is concrete enough that an implementation agent can code each `rel_*` module
without re-deriving decisions. It **must** use the module split, type names, and
fn names fixed by the architecture; nothing here renames or restructures them.

Ground-truth inputs (facts cited, not re-derived):
- Taxonomy `doc/01_research/hardware/nand_recovery/nand_ssd_recovery_prevention_taxonomy.md`
  (scheme names + section numbers cited below; no other literature invented).
- Gap analysis `doc/01_research/hardware/nand_recovery/nand_recovery_gap_analysis_local.md`
  (ranked opportunities #1–#10; the coarse 0/1/2+ ECC-signal constraint, §gap-2.4/3.11).
- Inventory `reliability_inventory.md` (file:line facts A1–A10, B1–B3, C).
- Emu research `doc/01_research/hardware/nand_emu/nand_emu_fpga_riscv_emulator.md`
  (§3 Vt model, §8 scenarios 1–20, Appendix B coefficients + the 2026-07-18
  calibration note).

---

## 0. Conventions and language landmines (apply to every module below)

The `rel_*` family is a **pure-policy leaf**: each module does `use nvme_types.*`
only (like `fil_ecc`, `fil_badblock`, `hooks`), so both `fil.spl` and `ftl.spl`
may import it without a cycle (inventory C). No module holds a `Fil`/`Ftl`
handle — policies are pure functions over narrow observation structs returning a
`RelAction` verdict; the mounting layer actuates.

Landmine rules baked into the pseudocode:

- **i64-first.** Every field is `i64` even where the emu meta uses `u8/u16`
  (`NePageMeta`/`NeBlockMeta`). Sizes below assume 8 B/`i64`.
- **Return-the-object.** Arrays/structs are value types (passed by copy). Every
  mutator RETURNS the updated struct and the caller reassigns. Named
  `..._on_erase`/`..._calibrate`/`..._note_read` fns, never in-place mutation
  observed by a caller.
- **No `Dict.get`-as-Option.** No policy uses a `Dict`; all per-block state is a
  dense `[i64]` array of length `NUM_BLOCKS` (= 64, `nvme_types.spl:37`), indexed
  by physical block. (`d.get(k)` returning bare value/`nil` is thereby avoided.)
- **`Rel` prefix on every public type** (interpreter global-registry collision
  guard, mirrors the emu's `Ne` prefix).
- **Constant tables are `fn`-returning literals** (`rel_vref_table_at(i)`), never
  module-level collection initializers — freestanding-safe, matches the emu
  convention and the fw_rv32 no-module-init rule.
- **Named-struct returns only.** `rel_ladder_step` returns a named `RelLadderStep`
  struct, never an anonymous tuple (cross-module tuple decay).
- **`RelAction` is a tagged struct `{kind:i64, arg:i64}`**, not an
  enum-with-payload — the architecture's detail-design gate (§3 interpreter note):
  payload enums can decay across the `rel_ladder`→mount boundary; the tagged
  struct round-trips identically with no caller-interface change.
- Module-level `var` read stale from spec `it` blocks — expose accessor fns; specs
  never assert on a module-level `var`.

---

## 1. `rel_types.spl` — shared structs, verdict, mounts (owned leaf)

### 1.1 The verdict — `RelAction` tagged struct

```
struct RelAction:
    kind: i64      # one of the rel_act_* codes below
    arg:  i64      # block index or Vref offset, per kind

# kind codes — fn-returning constants (freestanding-safe)
fn rel_act_accept()        -> i64: 0   # data good / no action
fn rel_act_retry()         -> i64: 1   # arg = signed Vref offset; FIL re-sense
fn rel_act_calibrate()     -> i64: 2   # arg = blk; FIL persist winning offset (ROR)
fn rel_act_refresh()       -> i64: 3   # arg = blk; FTL enqueue age/error rewrite (FCR/DEAR)
fn rel_act_reclaim()       -> i64: 4   # arg = blk; FTL reclaim_block (disturb/wear)
fn rel_act_quarantine()    -> i64: 5   # arg = blk; FTL retire + alloc_spare
fn rel_act_uncorrectable() -> i64: 6   # arg = blk; ladder exhausted → host NAND_ECC_FAIL

fn rel_action(kind: i64, arg: i64) -> RelAction:
    RelAction(kind: kind, arg: arg)
```

These are exactly the seven `RelAction` variants named in architecture §3, encoded
as the fallback tagged struct the architecture mandates confirming.

### 1.2 Observation structs (narrow, pure inputs)

```
struct RelReadObs:          # one sense result, fed to rel_ladder_step
    code:      i64          # ECC_OK (0) | NAND_ECC_FAIL (nvme_types constant)
    corrected: i64          # coarse 0 / 1 / 2  (2 = uncorrectable) — see §note-coarse
    offset:    i64          # signed Vref offset this sense used (vref = 128 + offset)
    depth:     i64          # rung index of this observation

struct RelBlockObs:         # per-block snapshot, fed to FTL policies
    blk:              i64
    erase_count:      i64   # from Fil.erase_count
    rd_disturb:       i64   # EXISTING ftl.spl:29 counter (source of truth, not copied)
    corrected_events: i64   # from RelHealth (count of reads with corrected>=1)
    last_prog_seq:    i64   # RelRefreshState
    cur_seq:          i64   # ftl next_seq (logical clock, §4 age proxy)

fn rel_read_obs(code: i64, corrected: i64, offset: i64, depth: i64) -> RelReadObs:
    RelReadObs(code: code, corrected: corrected, offset: offset, depth: depth)
```

`RelReadObs` is consumed directly by `rel_ladder_step` (§2). `RelBlockObs` is the
**caller-assembled per-block snapshot** the FTL layer builds each tick from its own
handles (`Fil.erase_count`, `ftl.rd_disturb[blk]`, `RelHealth`, `RelRefreshState`,
`next_seq`); the FTL decision fns `rel_refresh_due`/`rel_disturb_due`/`rel_wear_due`
take the **unpacked scalar fields** of that snapshot rather than the struct itself,
so the pure fns stay minimal and interpreter-safe (no cross-module struct decay on
the hot decision path). The layer unpacks `RelBlockObs` → scalars at the call site.

> **§note-coarse (the ECC-signal constraint).** `fil_ecc.ecc_decode` is Hamming
> SECDED over a modeled payload window: it yields a **coarse 0 / 1 / 2+** bucket
> (0 = clean, 1 = one bit corrected, 2 = uncorrectable), NOT a rich per-bit
> corrected count (gap analysis §gap-3.11; `injected_flips` is a fault-injection
> input, not a decoder syndrome). Every trigger below is designed to work on this
> three-value signal only — no algorithm assumes a real corrected-bit magnitude.

### 1.3 Per-policy state structs (all `[i64]`, length `NUM_BLOCKS` = 64)

Sizes are per-array `64 × 8 B = 512 B`.

```
struct RelLadderState:  blk,depth,table_idx,best_offset,best_corrected,phase : i64  # scalars, one live per read
struct RelVrefCache:    offset:[i64]  valid:[i64]  gen:[i64]                         # 3 × 512 B = 1.5 KB
struct RelRefreshState: last_prog_seq:[i64]  marked:[i64]                            # 1.0 KB
struct RelDisturbState: hot_page:[i64]  hot_count:[i64]                              # 1.0 KB
struct RelWearState:    last_global_erase:[i64]                                      # 0.5 KB
struct RelHealth:       reads:[i64] corrected_sum:[i64] corrected_events:[i64] \
                        retry_depth_max:[i64] refresh_cause:[i64]                    # 5 × 512 B = 2.5 KB
```

### 1.4 Mount bundles (pure state, composed by the layer — no handle)

```
struct RelFilMount:  vref: RelVrefCache   health: RelHealth   ladder: RelLadderState
struct RelFtlMount:  refresh: RelRefreshState  disturb: RelDisturbState \
                     wear: RelWearState   health: RelHealth
```

**Health sink discipline (architecture §5 + detail-design decision).**
`RelFtlMount.health` is the **durable sink**. `RelFilMount.health` is a
**transient** in-loop copy for the read currently in flight; on read completion the
FIL/FTL read result carries `(corrected, retry_depth)` up to `ftl.read`, which
folds them into the durable `RelFtlMount.health` via `rel_health_note_read`. This
resolves the "health in both mounts" ambiguity: the FIL copy never accumulates
across reads.

---

## 2. Algorithm 1 — Recovery ladder (`rel_ladder.spl`)

**Taxonomy lineage.** Taxonomy §1 (the normal NAND recovery ladder: hard read →
decode → change Vref and retry → … → RAID/RAIN reconstruct → rewrite → retire →
uncorrectable) + §2.1 fixed/table-based read retry. Gap analysis ranked #2. v1 is
hard-decision only — soft-LDPC rungs (§1 steps 4–5) are v2.

**v1 ladder rungs (the escalation this state machine drives):**

0. Hard read at offset 0 → SECDED decode. *(Done by the caller's `fil.read`; the
   ladder is entered only on `NAND_ECC_FAIL`.)*
1. **Calibrated-seed retry** — try the block's cached ROR offset first
   (`rel_vref_lookup`), if any. *(Architecture diagram `ecc_fail_ladder`:
   `seed offset ◄ lookup(blk)` before the sweep — **calibrated-seed-first**. This
   reconciles the task's listed order "table walk → calibrated": the calibrated
   offset is the SEED on re-encounter, and calibration/memoization is what happens
   AFTER the table walk succeeds on first encounter. Both coexist; no deviation.)*
2. **Bounded Vref retry-table walk** — the fixed 7-entry table (`rel_vref`, §3),
   one offset per step, bounded by the table length (step budget).
3. On the first offset that decodes → emit `CalibrateBlock` (persist winner) then
   the read is good.
4. **Table exhausted → `Uncorrectable`.** The pure ladder stops here. RAIN
   reconstruct and Quarantine are actuated by the **FTL caller of `fil.read`**
   (`ftl.read`), not by the ladder or the FIL mount — `fil` never imports `ftl`,
   so escalation flows UP the return path, not sideways.

**State struct** (`RelLadderState`, one live instance per in-flight read):

| field | type | meaning |
|---|---|---|
| `blk` | i64 | physical block under recovery |
| `depth` | i64 | rungs consumed (0 = clean; observability retry-depth) |
| `table_idx` | i64 | next `rel_vref` table entry to try |
| `best_offset` | i64 | winning offset (for `CalibrateBlock`) |
| `best_corrected` | i64 | coarse corrected count at the winner |
| `phase` | i64 | `rel_phase_seed`(0) → `rel_phase_table`(1) → `rel_phase_done`(2)/`rel_phase_fail`(3) |

```
fn rel_phase_seed()  -> i64: 0
fn rel_phase_table() -> i64: 1
fn rel_phase_done()  -> i64: 2
fn rel_phase_fail()  -> i64: 3

fn rel_ladder_state_new(blk: i64) -> RelLadderState:
    RelLadderState(blk: blk, depth: 0, table_idx: 0,
                   best_offset: 0, best_corrected: 0, phase: rel_phase_seed())

struct RelLadderStep:            # named-struct return (no tuple decay)
    state:  RelLadderState
    action: RelAction
```

**Decision function** (pure; `seed` = `rel_vref_lookup(cache, blk)`):

```
fn rel_ladder_step(st: RelLadderState, obs: RelReadObs, seed: i64) -> RelLadderStep:
    var s = st
    # rung 3: any sense that decoded ends the ladder
    if obs.code == ECC_OK:
        s.best_offset = obs.offset
        s.best_corrected = obs.corrected
        s.phase = rel_phase_done()
        if obs.offset != 0:
            return RelLadderStep(state: s, action: rel_action(rel_act_calibrate(), s.blk))
        return RelLadderStep(state: s, action: rel_action(rel_act_accept(), 0))
    # still failing → escalate one rung
    s.depth = st.depth + 1
    # rung 1: calibrated-seed-first
    if st.phase == rel_phase_seed():
        s.phase = rel_phase_table()
        if seed != 0:
            s.table_idx = 0
            return RelLadderStep(state: s, action: rel_action(rel_act_retry(), seed))
        s.table_idx = 1
        return RelLadderStep(state: s, action: rel_action(rel_act_retry(), rel_vref_table_at(0)))
    # rung 2: fixed retry-table walk (one entry per step = step budget)
    if st.table_idx < rel_vref_table_len():
        val k: i64 = rel_vref_table_at(st.table_idx)
        s.table_idx = st.table_idx + 1
        return RelLadderStep(state: s, action: rel_action(rel_act_retry(), k))
    # rung 4: exhausted → Uncorrectable (FTL caller escalates to RAIN/Quarantine)
    s.phase = rel_phase_fail()
    return RelLadderStep(state: s, action: rel_action(rel_act_uncorrectable(), s.blk))
```

**Mount adapter** (documented, lives at the FIL read path; owns the `Fil` handle
and the loop — pure module stays pure):

```
fn fil_read_with_ladder(m0: RelFilMount, ppn: i64, blk: i64) -> RelReadResult:
    var m  = m0
    var rd = fil.read(ppn)                                   # hard read, offset 0
    var st = rel_ladder_state_new(blk)
    var obs = rel_read_obs(rd.code, rd.corrected, 0, 0)      # rd.corrected = seam #1
    while true:
        val stp = rel_ladder_step(st, obs, rel_vref_lookup(m.vref, blk))
        st = stp.state
        val a = stp.action
        if a.kind == rel_act_accept():
            fil.set_vref_offset(0)                           # restore GLOBAL knob
            return rel_read_result_ok(rd.data, st.depth, obs.corrected)
        if a.kind == rel_act_calibrate():
            m.vref = rel_vref_calibrate(m.vref, blk, st.best_offset)
            fil.set_vref_offset(0)
            return rel_read_result_ok(rd.data, st.depth, obs.corrected)
        if a.kind == rel_act_retry():
            fil.set_vref_offset(a.arg)                       # chip-GLOBAL vref = 128 + a.arg
            rd  = fil.read_at_vref(ppn, a.arg)               # seam #2 (non-terminal sense)
            obs = rel_read_obs(rd.code, rd.corrected, a.arg, st.depth)
            continue
        # rel_act_uncorrectable
        fil.set_vref_offset(0)
        return rel_read_result_fail(st.depth)                # ftl.read → RAIN/Quarantine
```
`ftl.read`, on `rel_read_result_ok`, folds `(corrected, depth)` into
`RelFtlMount.health` (durable). On `rel_read_result_fail` it attempts
`rain_recover_channel`; parity failure → `Quarantine` → retire + `alloc_spare`.

**Constants:**

| name | default | rationale |
|---|---|---|
| `rel_vref_table_len()` | 7 | step budget = fixed 7-entry table (§3); bounds worst-case retries per read. |
| max rungs | 8 | 1 calibrated seed + 7 table entries; `depth` observability caps here. |

**Mount point:** **FIL** (placement table: decision inputs physical → placeable;
actuation re-sense at Vref → FIL). Movable to FTL over a `read_raw`, but every
read site would have to opt in (architecture §2 "ladder default = FIL, honest
cost"). Mounting at `fil.read` closes gap A2 for the internal GC/scrub/RAIN reads
for free.

**Validation scenario (nand_emu).** Emu drivers: `set_block_wear(blk, 5000)` +
`advance_time_s` to induce retention drift, `set_vref_offset` is the actuator the
mount drives, per-page `read_page` for the sense.
- **Drift regime = ~5 K P/E, NOT 30 K/1 yr.** Per the emu calibration note
  (research doc, 2026-07-18): with the implemented log10 model + Appendix-B
  defaults a 30 K-P/E block held one year *saturates to total charge loss*
  (uncorrectable), so the correctable-then-recoverable signature only appears at
  ~5 K P/E. §8 scenario #1 nominally says 30 K — the spec must pin 5 K and note
  the honest discrepancy.
- **Primary oracle (runnable today, re-export-independent):** program a page with
  known bytes; a plain read at offset 0 returns `NAND_ECC_FAIL` (or wrong bytes);
  `fil_read_with_ladder` returns the EXACT programmed bytes at `depth` 2–3
  (scenario #1 "correctable at retry level 2–3").
- **Secondary oracle (gated on seam #3):** `vt_histogram(page)` confirms the
  valley moved in the winning offset's direction; `read_margin(page)` at the
  winner > at offset 0.
- **§8 #2 (deep retention) = the Uncorrectable branch, not recovery.** v1
  hard-decision cannot do #2's "recovered by soft-decision read". The spec asserts
  the ladder correctly *exhausts* the table → emits `Uncorrectable` → `ftl.read`
  escalates to RAIN/Quarantine. Listed in the matrix as the exhaustion path.

**Does NOT do in v1:** hard-decision Vref sweep only — no soft-info/LLR
multi-read (taxonomy §1 steps 4–5, v2); and it calibrates to the *first-decoding*
offset, not the valley-center min-RBER offset (coarse 0/1/2+ signal + step budget
preclude margin optimization).

---

## 3. Algorithm 2 — Retry table + ROR-lite per-block vref calibration (`rel_vref.spl`)

**Taxonomy lineage.** §2.1 table-based / fixed read retry (the 7-entry table) +
§2.2 ROR — Retention Optimized Reading (learn the block's optimal reference and
reuse it). Gap analysis ranked #3.

**Fixed 7-entry retry table** (fn-returning literals; retention-biased order —
retention charge loss shifts the programmed lobe DOWN so negative offsets
dominate, `ne_retention_delta` is negative-only for vt>128; disturb shifts UP so
positive offsets are interleaved):

```
fn rel_vref_table_len() -> i64: 7
fn rel_vref_table_at(i: i64) -> i64:
    if i == 0: return -8
    if i == 1: return -16
    if i == 2: return  8
    if i == 3: return -24
    if i == 4: return  16
    if i == 5: return -32
    if i == 6: return  24
    return 0
```

**State struct** `RelVrefCache` (per-block, `[i64]` length `NUM_BLOCKS`):

| field | type | size | meaning |
|---|---|---|---|
| `offset` | `[i64]` | 512 B | calibrated Vref offset per block (0 = none) |
| `valid` | `[i64]` | 512 B | 1 = calibrated, 0 = not/expired |
| `gen` | `[i64]` | 512 B | erase generation at calibration (audit / optional gen-guard) |

**Decision / mutator functions** (all return-the-object):

```
fn rel_vref_lookup(c: RelVrefCache, blk: i64) -> i64:
    if c.valid[blk] == 1:
        return c.offset[blk]
    return 0                                   # 0 = "no seed", ladder falls to table

fn rel_vref_calibrate(c: RelVrefCache, blk: i64, off: i64) -> RelVrefCache:
    var out = c
    out.offset[blk] = off
    out.valid[blk]  = 1
    return out                                 # persist winner post-success (ROR)

fn rel_vref_decay_on_erase(c: RelVrefCache, blk: i64) -> RelVrefCache:
    var out = c
    out.valid[blk]  = 0                         # erased block: retention offset void
    out.offset[blk] = 0
    return out
```

Called from the erase path (`Fil.erase_block` / reclaim) so a recycled block never
reuses a stale retention offset. (`gen` supports an optional lookup-time
gen-guard — auto-expire if `gen[blk] != current_erase_count` — as a belt-and-
suspenders; the explicit `decay_on_erase` call is the primary mechanism.)

**Constants:**

| name | default | rationale |
|---|---|---|
| table entries | `[-8,-16,+8,-24,+16,-32,+24]` | retention-biased, alternating sign, growing magnitude; covers charge-loss (dominant) and disturb (secondary) in ≤7 senses. |
| `REL_VREF_MAX_ABS` | 32 | table max |offset|; keeps vref = 128±32 inside the 0..255 code range with headroom. |

**Mount point:** **FIL** (with the ladder — device-near calibration keyed by
physical block; never sees L2P).

**Validation scenario (nand_emu).** Emu drivers: same drift setup as §2
(`set_block_wear(5000)` + `advance_time_s`), `set_vref_offset`.
- **Primary oracle:** after the ladder recovers block B at offset k, assert
  `rel_vref_lookup(cache, B) == k`; a SECOND read of B decodes at the calibrated
  seed with `depth <= 1` (seed hit, no full table walk). After erasing B,
  `rel_vref_lookup(cache, B) == 0` (decay proven).
- **Secondary oracle (seam #3):** the learned k lies at/near the offset that
  maximizes `read_margin(page)` across the swept offsets — i.e., ROR converges
  toward the emu's own drift-implied optimum.

**Does NOT do in v1:** single scalar offset per block — no age/temperature model
(ReMAR/HeatWatch, v2), no per-page/per-wordline calibration (meaningless on SLC,
§gap-2.2); decay is a binary invalidate-on-erase, not a modeled expiry curve.

---

## 4. Algorithm 3 — FCR/DEAR-lite refresh (`rel_refresh.spl`)

**Taxonomy lineage.** §3.3 FCR — Flash Correct-and-Refresh (read, correct, rewrite
before errors exceed ECC) + DEAR — Dynamic Error-Aware Refresh (runtime
error-behavior-triggered) + §3.11 ECC-correction-count-triggered refresh. Gap
analysis ranked #5.

**Three triggers, all working on the coarse 0/1/2+ signal and a firmware-side
clock proxy:**

1. **Retry-success (DEAR).** If a read needed a Vref retry (`needed_retry == 1`,
   i.e. ladder `depth > 0`), the block is actively drifting → refresh now. This is
   the strongest early signal and is retry-depth-derived (see seam #1 below —
   retry depth must ride up the read result alongside `corrected`).
2. **Corrected-event trend (FCR).** Accumulate, per block, the count of reads with
   `corrected >= 1` (from `RelHealth.corrected_events`). Trigger at
   `REL_REFRESH_ERR_EVENTS`. Designed within the coarse constraint: we cannot
   count corrected *bits*, so we count corrected *reads* — refresh well before the
   block accumulates enough drift for a 2-bit uncorrectable word.
3. **Age proxy (fixed-interval, no wall clock).** The FTL has no wall clock
   (inventory A10) — only a monotonic `next_seq`. Use `age = cur_seq -
   last_prog_seq[blk]` as a **workload-relative** retention proxy: how much host
   write traffic has elapsed since this block was written. Trigger at
   `REL_REFRESH_AGE_SEQ`. **Justification + honest limit:** `seq` advances per
   program op, so this approximates dwell-under-workload, NOT elapsed wall-time; a
   drive idle for a year with no writes shows zero seq-age. It is the only
   clock-free age signal available and is marked phenomenological.

**State struct** `RelRefreshState`:

| field | type | size | meaning |
|---|---|---|---|
| `last_prog_seq` | `[i64]` | 512 B | `next_seq` snapshot at the block's last (re)write |
| `marked` | `[i64]` | 512 B | 1 = already queued for refresh (dedupe) |

**Decision function** (`corrected_events` from `RelHealth`; `needed_retry` from the
read result):

```
fn rel_refresh_due(st: RelRefreshState, blk: i64, cur_seq: i64,
                   corrected_events: i64, needed_retry: i64) -> RelAction:
    if st.marked[blk] == 1:
        return rel_action(rel_act_accept(), 0)             # already queued
    if needed_retry == 1:                                   # (1) DEAR
        return rel_action(rel_act_refresh(), blk)
    if corrected_events >= REL_REFRESH_ERR_EVENTS():        # (2) FCR error trend
        return rel_action(rel_act_refresh(), blk)
    if (cur_seq - st.last_prog_seq[blk]) >= REL_REFRESH_AGE_SEQ():   # (3) age proxy
        return rel_action(rel_act_refresh(), blk)
    return rel_action(rel_act_accept(), 0)

fn rel_refresh_on_write(st: RelRefreshState, blk: i64, cur_seq: i64) -> RelRefreshState:
    var out = st
    out.last_prog_seq[blk] = cur_seq
    out.marked[blk] = 0                                     # fresh data: clear
    return out

fn rel_refresh_enqueue(st: RelRefreshState, blk: i64) -> RelRefreshState:
    var out = st
    out.marked[blk] = 1
    return out
```

**Constants:**

| name | default | rationale |
|---|---|---|
| `REL_REFRESH_ERR_EVENTS()` | 3 | With SECDED (1-bit correct / 2-bit fail), 3 distinct corrected-reads is a conservative early trigger — refresh long before drift produces a 2-bit uncorrectable word. |
| `REL_REFRESH_AGE_SEQ()` | 100000 | Workload-relative; sized so the age trigger fires on genuinely stale blocks, not hot ones (a hot block is rewritten — `last_prog_seq` resets — long before 100 K seq elapse). Phenomenological; re-fit against emu drift. |

**Mount point:** **FTL** (decision placeable; actuation = rewrite to fresh block
needs the map → FTL-pinned). Drains into the tick round-robin slot 2 (§7).

**Validation scenario (nand_emu).** Emu drivers: `set_block_wear(5000)` +
`advance_time_s` (correctable regime), per-block reads.
- **Primary oracle:** advance drift until reads of block B start returning
  `corrected >= 1` (coarse) or `needed_retry`; assert `rel_refresh_due(B)` returns
  `MarkForRefresh` **before** a plain read of B ever returns `NAND_ECC_FAIL` — i.e.
  refresh precedes uncorrectability (FCR's whole point). Assert the age trigger
  independently by advancing `cur_seq` past `REL_REFRESH_AGE_SEQ` with a stale
  `last_prog_seq`.
- **Secondary oracle (seam #3):** at the refresh-fire point, `read_margin(B) > 0`
  (still in the correctable regime), proving refresh is not late.
- §8 scenario **#1** ("page marked for refresh").

**Does NOT do in v1:** coarse-signal only (event-count, not bit-count trend); the
age proxy is workload-relative, not wall-clock (no true retention timer); no
temperature-triggered refresh (HeatWatch, v2); no per-page-type (LSB/MSB) policy
(SLC has one page type).

---

## 5. Algorithm 4 — STRAW-lite read-disturb reclaim (`rel_disturb.spl`)

**Taxonomy lineage.** §3.4 STRAW (track accumulated read-disturb stress and
reclaim the most-disturbed unit rather than blindly refreshing whole blocks). Gap
analysis ranked #4. v1 is block-granular + a hottest-page estimate; true
per-wordline STRAW is v2 (no wordline model, §gap-3.4).

**Extends, does not duplicate, the existing counter.** The FW already bumps
`rd_disturb[blk]` per read (`ftl.spl:109,117,347-352`) and it gates the existing
`scrub_once` at `READ_DISTURB_THRESHOLD = 50`. `rel_disturb` consumes that counter
as an *observation* (source of truth) and adds ONLY a hottest-page estimate — a
parallel stress counter would diverge from `rd_disturb`. The hottest page is
tracked with a **Boyer-Moore majority candidate** (O(1), no `Dict`, no per-page
array): a cheap proxy for "one wordline is taking most of the stress" using the
page index the FTL read path already knows.

**State struct** `RelDisturbState`:

| field | type | size | meaning |
|---|---|---|---|
| `hot_page` | `[i64]` | 512 B | Boyer-Moore majority candidate page per block |
| `hot_count` | `[i64]` | 512 B | its running majority count |

```
fn rel_disturb_observe(st: RelDisturbState, blk: i64, page: i64) -> RelDisturbState:
    var out = st
    if out.hot_count[blk] == 0:
        out.hot_page[blk]  = page
        out.hot_count[blk] = 1
    elif out.hot_page[blk] == page:
        out.hot_count[blk] = out.hot_count[blk] + 1
    else:
        out.hot_count[blk] = out.hot_count[blk] - 1
    return out                                    # return-the-object

# rd_disturb_blk = EXISTING ftl.spl rd_disturb[blk] (not copied into this module)
fn rel_disturb_due(st: RelDisturbState, blk: i64, rd_disturb_blk: i64) -> RelAction:
    if rd_disturb_blk > READ_DISTURB_THRESHOLD:            # block gate (existing behavior)
        return rel_action(rel_act_reclaim(), blk)
    if st.hot_count[blk] > REL_DISTURB_HOTPAGE_MIN():      # finer: one page dominates
        return rel_action(rel_act_reclaim(), blk)
    return rel_action(rel_act_accept(), 0)

fn rel_disturb_clear(st: RelDisturbState, blk: i64) -> RelDisturbState:
    var out = st
    out.hot_page[blk]  = 0
    out.hot_count[blk] = 0
    return out                                    # on erase/reclaim
```

**Constants:**

| name | default | rationale |
|---|---|---|
| `READ_DISTURB_THRESHOLD` | 50 (existing `nvme_types.spl:43`) | reused unchanged — preserves current block-level scrub behavior exactly. |
| `REL_DISTURB_HOTPAGE_MIN()` | 40 | fires before the block-wide count reaches 50 when a single page dominates — concentrates reclaim on an actually-stressed block earlier without churning evenly-read blocks. |

**Mount point:** **FTL** (decision placeable via read count; actuation
`ReclaimNow` → `scrub_once` needs the map → FTL). `rel_disturb_observe` is called
from the FTL read path.

**Validation scenario (nand_emu).** Emu drivers: repeated `read_page` on one page
+ `erase_block`/reclaim clears the counter; per-page reads.
- **Primary oracle (cheap, physics-independent):** read one page > 50 times (or
  until `hot_count > 40`); assert `rel_disturb_due` returns `ReclaimNow`; run
  `scrub_once`; assert `rd_disturb[blk]` reset to 0 and the block reclaimed. All
  FW-observable, no emu physics needed.
- **Secondary oracle (seam #3 + seam #4):** after reclaim, `read_margin(page±1)`
  recovers vs. its pre-reclaim narrowed value — requires a bulk read-disturb
  injection on the wrapper (seam #4) so the emu's `rd_count` physics actually
  degrades the margin without looping 200 K real reads.
- §8 scenario **#3** ("read counter triggers block refresh before UECC").

**Does NOT do in v1:** block-granular + single-hottest-page estimate only — NOT
true per-wordline STRAW (no wordline model); the majority-vote hottest page is an
estimate that can miss multi-hot-page patterns; only reclaim, no read
leveling/scattering/caching (§3.4 basic techniques, out of v1).

---

## 6. Algorithm 5 — SREA-lite dwell-aware static wear leveling (`rel_wear.spl`)

**Taxonomy lineage.** §3.7 static wear leveling + SREA (include self-recovery /
dwell effects in wear-leveling decisions). Gap analysis ranked #6. Wired to the
existing `wear_level_once` mechanism.

**Dwell proxy without a clock.** SREA wants "idle recovery time since last erase";
the emu has `last_erase_time` but the FW does not (inventory A10). Proxy: the
**global-erase-count delta** — `dwell = total_erases - last_global_erase[blk]`, how
many P/E cycles happened *elsewhere* since this block was last erased. A large
delta means the block has sat idle (its physics-model wear-widening term is not
freshly maximal), so its cold data can be relocated and the block cycled; a small
delta means it was just erased → defer (SREA deferral avoids premature churn).

**State struct** `RelWearState`:

| field | type | size | meaning |
|---|---|---|---|
| `last_global_erase` | `[i64]` | 512 B | `total_erases` snapshot when this block was last erased |

```
fn rel_wear_on_erase(st: RelWearState, blk: i64, total_erases: i64) -> RelWearState:
    var out = st
    out.last_global_erase[blk] = total_erases
    return out                                    # return-the-object

# cold_blk = min-erase victim from ftl_gc.spl:15-27; erase_min/max from ftl aggregates
fn rel_wear_due(st: RelWearState, cold_blk: i64, erase_min: i64,
                erase_max: i64, total_erases: i64) -> RelAction:
    if (erase_max - erase_min) <= WL_THRESHOLD:
        return rel_action(rel_act_accept(), 0)            # spread acceptable
    val dwell: i64 = total_erases - st.last_global_erase[cold_blk]
    if dwell >= REL_WL_DWELL_MIN():                        # cold block has rested → cycle it
        return rel_action(rel_act_reclaim(), cold_blk)    # static WL: relocate cold data off it
    return rel_action(rel_act_accept(), 0)                # SREA deferral: not dwelled enough
```

**Constants:**

| name | default | rationale |
|---|---|---|
| `WL_THRESHOLD` | 2 (existing `nvme_types.spl:42`) | reused unchanged — preserves the existing static-WL trigger. |
| `REL_WL_DWELL_MIN()` | 8 | require the cold block to have sat through ≥8 P/E cycles elsewhere before churning it — a phenomenological dwell floor that prevents WL thrash on a just-erased block. |

**Mount point:** **FTL** (erase spread placeable, but victim selection is
cold/hot-adjacent — borderline; actuation `wear_level_once` needs the map → FTL).
Tick round-robin slot 4 (§7).

**Validation scenario (nand_emu).** Emu drivers: `set_block_wear(blk, pe)` /
per-block `erase_count` to create a spread; drive erases elsewhere to build dwell.
- **Primary oracle:** set one block low-P/E and others high so `erase_max -
  erase_min > 2`; snapshot dwell; assert `rel_wear_due` returns `ReclaimNow` on the
  dwelled cold block and that `wear_level_once` **narrows** `erase_max - erase_min`
  afterward. Assert the **deferral**: with `dwell < 8`, `rel_wear_due` returns
  `Accept` (no premature churn).
- **Secondary oracle (seam #3):** `vt_histogram` σ of the relocated block's data on
  its new home is tighter than the pre-move drifted source.
- §8 scenario **#11** ("wear leveling should have prevented the concentration").

**Does NOT do in v1:** dwell is an erase-count-delta proxy, NOT modeled idle-time
self-recovery physics (phenomenological); no per-layer/wordline wear (SLC single
plane); no logical hot/cold data separation on the write path (that decision needs
L2P → FTL-pinned, v2).

---

## 7. Algorithm 6 — Wiring pass (service-tick round-robin + event-driven spare)

**Taxonomy lineage.** Architecture §4 (wire the four unwired mechanisms) — gap
analysis ranked #1 (pure wiring, no new algorithm). Overlaps FCR (§3.3), STRAW
(§3.4), static WL (§3.7), spare substitution (§3.10). Includes the `rel_health`
observability sink.

**The budget invariant (critical).** `gc_once`, a refresh rewrite, `scrub_once`,
and `wear_level_once` ALL drain the shared `GC_RESERVE = 2` blocks via
`reclaim_block`. Firing several per tick can exhaust the reserve and thrash. The
faithful extension is therefore **one reclaim-class step per tick, total**, chosen
by fixed priority among gated candidates (architecture §4 table):

```
fn rel_step_none()    -> i64: 0
fn rel_step_gc()      -> i64: 1
fn rel_step_refresh() -> i64: 2
fn rel_step_scrub()   -> i64: 3
fn rel_step_wl()      -> i64: 4

fn rel_tick_select(free_blocks: i64, low_wm: i64, refresh_pending: i64,
                   worst_disturb: i64, disturb_thr: i64,
                   erase_spread: i64, wl_thr: i64) -> i64:
    if free_blocks < low_wm:        return rel_step_gc()       # 1
    if refresh_pending > 0:         return rel_step_refresh()  # 2
    if worst_disturb > disturb_thr: return rel_step_scrub()    # 3
    if erase_spread > wl_thr:       return rel_step_wl()       # 4
    return rel_step_none()
```

The FTL service tick calls `rel_tick_select`, then executes **exactly one** step
via its own handle (`gc_once` / drain the `MarkForRefresh` queue / `scrub_once` /
`wear_level_once`). Two mechanisms sit outside the reclaim slot:

- **`rain_seal`** — parity only, relocates no host data → its own small bound,
  **≤1 stripe/tick**, does not compete for the reclaim slot.
- **`alloc_spare`** — **event-driven, not a background step.** Fires from the
  retire path (`Quarantine` / program-fail / erase-fail → `fil.mark_bad` →
  `band.set_bad`) to remap the retired block onto a reserved OP spare (blocks
  56..63, `fil_badblock.spl:52-61`), closing gap A7.

**`rel_health.spl` — the observability sink** (durable at `RelFtlMount.health`):

```
fn rel_cause_none() -> i64: 0
fn rel_cause_age()  -> i64: 1     # FCR
fn rel_cause_err()  -> i64: 2     # DEAR
fn rel_cause_dist() -> i64: 3     # STRAW

fn rel_health_note_read(h: RelHealth, blk: i64, corrected: i64, depth: i64) -> RelHealth:
    var out = h
    out.reads[blk]         = h.reads[blk] + 1
    out.corrected_sum[blk] = h.corrected_sum[blk] + corrected
    if corrected >= 1:
        out.corrected_events[blk] = h.corrected_events[blk] + 1
    if depth > h.retry_depth_max[blk]:
        out.retry_depth_max[blk] = depth
    return out

fn rel_health_rber(h: RelHealth, blk: i64) -> i64:      # scaled ppm, i64-first (no float)
    if h.reads[blk] == 0:
        return 0
    return (h.corrected_sum[blk] * 1000000) / h.reads[blk]

fn rel_health_mark_cause(h: RelHealth, blk: i64, cause: i64) -> RelHealth:
    var out = h
    out.refresh_cause[blk] = cause
    return out

fn rel_health_on_erase(h: RelHealth, blk: i64) -> RelHealth:
    var out = h
    out.corrected_events[blk] = 0      # else a recycled block re-fires FCR on its first corrected read
    out.retry_depth_max[blk]  = 0
    out.refresh_cause[blk]    = rel_cause_none()
    return out                         # call from the erase/reclaim path, parallel to
                                       # rel_vref_decay_on_erase and rel_disturb_clear
```

**Erase-reset discipline (all three per-block policies clear on erase).** A block's
reliability state must not survive a P/E cycle: `rel_vref_decay_on_erase` (§3),
`rel_disturb_clear` (§5), and `rel_health_on_erase` above are all invoked from the
erase/reclaim path. Without `rel_health_on_erase`, a refreshed-then-recycled block
keeps a stale `corrected_events >= REL_REFRESH_ERR_EVENTS` and its first corrected
read would immediately re-fire refresh — a sticky FCR trigger. (Wired in L2 and
exercised by the L8 erase path; see §9.)

**Constants:** `GC_LOW_WATERMARK`, `GC_RESERVE = 2` (existing, unchanged);
`rain_seal` bound = 1 stripe/tick; step priority order GC > refresh > scrub > WL
(fixed).

**Mount point:** **FTL** service tick (round-robin); `alloc_spare` at the retire
path (FIL/FTL boundary). `rel_health` folded at `ftl.read`.

**Validation scenario (nand_emu).** Emu drivers: `inject(EraseFail)` /
`inject(ProgFail)`, per-block `erase_count`.
- **Primary oracle (budget):** with several gates hot simultaneously (free <
  watermark AND disturb > threshold AND spread > WL), assert `rel_tick_select`
  returns exactly one step and priority holds (GC first); count `reclaim_block`
  calls == 1 per tick; assert `GC_RESERVE` is never exhausted across a burst.
- **Primary oracle (spare):** `inject(EraseFail)` on a block → it retires → assert
  a spare from 56..63 is remapped active in the band and the retired block is out
  of rotation.
- §8 scenarios **#7** (program-fail block replacement), **#8** (erase-fail retire +
  BBT survives power cycle), **#3** (scrub selection), **#11** (WL selection).

**Does NOT do in v1:** one step/tick bounds latency but throttles recovery under a
multi-trigger storm (bursts queue — honest ceiling); `rain_seal` parity stays
DRAM-only / non-power-safe (existing honesty note `ftl.spl:398-415`); GC default
victim scorer stays greedy-fewest-valid (error/age-aware GC is gap #8, out of this
v1 set).

---

## 8. Prerequisite seams (blockers; not implemented by the `rel_*` modules)

These thin extensions to `fil.spl` / `fil_nand_emu` / the `NandEmu` wrapper are
required before the modules can be validated. They are separate implementation
lanes (§9 lane 0) because the guide forbids the doc wave from editing those files
and the modules cannot be exercised without them.

1. **Read result carries `corrected` AND retry-depth.** `FilRead{data,lba,seq,code}`
   surfaces neither the coarse corrected count that `ecc_decode` already computes
   (architecture prereq 1) NOR a "needed a retry" outcome. `rel_health`/`rel_ladder`
   need `corrected`; `rel_refresh`'s DEAR trigger (§4) needs retry-depth/needed_retry
   — corrected-count on the *successful* retry read can be 0/1 and does not imply a
   retry happened. Add `corrected: i64` and `retry_depth: i64` (or `needed_retry: i64`)
   to the read result, folded into the durable `RelFtlMount.health` at `ftl.read`.
2. **Explicit-Vref, non-terminal sense primitive.** No `fil.read_at_vref(ppn,
   offset)` / `read_raw` exists to sense at a chosen reference without ECC-fail
   being terminal. The ladder loop (§2) requires it.
3. **Emu soft-observability re-export.** `vt_histogram(page)` / `read_margin(page)`
   exist on `NeChip` (`chip.spl:695-741`) but are NOT re-exported through the
   `NandEmu` wrapper (inventory B1/B3). Add wrapper passthroughs + FIL/FTL test
   accessors. **Gates every secondary oracle above** — leave the primary oracles
   independent of it so no lane blocks on this.
4. **(validation-only) Bulk read-disturb injection on the wrapper.** The emu
   research API (§9.4) has `emu.disturb(page, reads)` conceptually, but the
   `NandEmu` wrapper exposes only `inject_read_bitflip`/`corrupt_page_data` — no
   bulk `rd_count` bump. Without it the §5 secondary physics oracle must loop 200 K
   real `read_page` calls (infeasible under the seed). The §5 primary oracle uses
   the FW `rd_disturb` counter and does not need it; list this seam only for the
   secondary disturb-margin oracle.

---

## 9. Implementation order (dependency-ordered lanes; lane = module + its spec)

Each lane is sized for a small agent and ships the module plus its `*_spec.spl`
(rel_* unit specs under `.../test/`) or `*_check.spl` (fw integration, co-located).

| Lane | Deliverable (module + spec) | Depends on | Notes |
|---|---|---|---|
| **L0a** | seam #1: read result `corrected`+`retry_depth` → `fil`/`fil_ecc` + `fil_check` | — | prereq; owned by fw agent, not the doc wave |
| **L0b** | seam #2: `fil.read_at_vref`/`read_raw` → `fil_check` | — | prereq |
| **L0c** | seam #3: `NandEmu` re-export `vt_histogram`/`read_margin` + accessors → `fil_nand_emu_check` | — | prereq; gates secondary oracles |
| **L0d** | seam #4 (optional): wrapper bulk disturb injection | L0c | only for §5 secondary oracle |
| **L1** | `rel_types.spl` (all structs + `RelAction {kind,arg}` + constants) + `rel_types_spec` | — | **spec MUST round-trip `RelAction.kind/arg` across a module boundary** — the interpreter gate (architecture §3). |
| **L2** | `rel_health.spl` + `rel_health_spec` | L1 | sink; note_read / rber / mark_cause |
| **L3** | `rel_vref.spl` (7-entry table + calibration cache) + `rel_vref_spec` | L1 | table order + lookup/calibrate/decay |
| **L4** | `rel_ladder.spl` (state machine) + `rel_ladder_spec` | L1, L2, L3, L0a, L0b | full recovery loop; emu-validated |
| **L5** | `rel_refresh.spl` + `rel_refresh_spec` | L1, L2, L0a | needs corrected_events + needed_retry |
| **L6** | `rel_disturb.spl` + `rel_disturb_spec` | L1 | consumes existing `rd_disturb` |
| **L7** | `rel_wear.spl` + `rel_wear_spec` | L1 | dwell proxy |
| **L8** | wiring pass: `rel_tick_select` + FIL mount adapter + FTL tick + `alloc_spare` retire path + fw `*_check.spl` | L2–L7, L0a–L0c | integration; budget invariant |

Critical path: **L0a/L0b → L1 → {L2, L3} → L4 → {L5, L6, L7} → L8**. L0c gates only
secondary oracles; L6/L7 are independent of L4 and can run parallel to it once L1
lands.

---

## 10. Verification matrix (algorithm × nand_emu scenario × oracle)

Primary oracles are runnable today (ECC pass/fail, exact data round-trip, FW
counters). Secondary oracles are gated on seam #3 (and #4 for disturb margin).

| Algorithm | Module | §8 scen. | Emu API driver | Primary oracle (absolute) | Secondary (gated) |
|---|---|---|---|---|---|
| Recovery ladder | `rel_ladder` | #1 | `set_block_wear(blk,5000)`, `advance_time_s`, `set_vref_offset`, `read_page` | plain read@0 = FAIL/wrong; ladder returns EXACT programmed bytes at depth 2–3 | `vt_histogram` valley moved toward winner; `read_margin(winner) > read_margin(0)` |
| Recovery ladder (exhaustion) | `rel_ladder` | #2 | deep drift (higher wear/time) | table exhausts → `Uncorrectable` → `ftl.read` escalates to RAIN/Quarantine (NOT recovered — v1 hard-decision ceiling) | — |
| Retry table + ROR-lite | `rel_vref` | #1 | same as ladder | `rel_vref_lookup(B)==k` post-recover; 2nd read depth ≤ 1; after erase, lookup==0 (decay) | learned k ≈ argmax `read_margin` over offsets |
| FCR/DEAR-lite refresh | `rel_refresh` | #1 | `set_block_wear(5000)`, `advance_time_s`, per-block reads, `cur_seq` | `rel_refresh_due` = `MarkForRefresh` BEFORE any plain read returns `NAND_ECC_FAIL`; age trigger fires on stale `last_prog_seq` | `read_margin(B) > 0` at fire point (correctable regime) |
| STRAW-lite disturb | `rel_disturb` | #3 | repeated `read_page`, `erase_block`/reclaim | reads > 50 (or hot_count > 40) → `ReclaimNow`; `scrub_once` resets `rd_disturb` to 0 | `read_margin(page±1)` recovers post-reclaim (needs #3 + #4) |
| SREA-lite wear | `rel_wear` | #11 | `set_block_wear`, per-block `erase_count` | spread > 2 + dwell ≥ 8 → `ReclaimNow`; `wear_level_once` narrows max−min; dwell < 8 → `Accept` (deferral) | relocated block `vt_histogram` σ tighter |
| Wiring / budget | tick + `rel_health` | #7, #8, #3, #11 | `inject(EraseFail/ProgFail)`, `erase_count` | `rel_tick_select` returns exactly 1 step, priority GC>refresh>scrub>WL; `reclaim_block` ≤ 1/tick; `GC_RESERVE` never exhausted; retire → spare 56..63 remapped | — |

---

## 11. Non-goals (anti-over-engineering)

The whole v1 deliverable is *the seven `rel_*` modules + two composed mount
bundles + the `RelAction {kind,arg}` verdict + the four prereq seams + the wiring
pass*. Explicitly NOT built (per architecture §7 and gap analysis §4): no plugin
registry, no config-file policy DSL, no per-policy dynamic loader; no soft-decision
LDPC/LLR (§2.4/2.5, v2 — emu is 1 bit/cell); no per-layer/wordline calibration
(§2.3, no 3D axis); no temperature-aware policy (no temp model); no MLC/TLC
state-mapping or cell-mode reconfiguration (§3.6/3.9, SLC only); no ML predictors
(§3.11, no training pipeline). Composition only, no inheritance, no dead
flexibility.
