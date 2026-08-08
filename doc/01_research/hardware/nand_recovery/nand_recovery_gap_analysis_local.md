# NAND Recovery/Prevention Gap Analysis — Local Repo Mapping

**Status:** research (2026-07-19). Maps
`nand_ssd_recovery_prevention_taxonomy.md` onto this repo's actual state:
`examples/09_embedded/simpleos_nvme_fw/fw/` (NVMe firmware, FIL/FTL layers) and
`src/lib/hardware/nand_emu/` (the K9F8G08X0M-compatible Vt-model emulator).
Companion: `doc/04_architecture/hardware/nand_recovery/reliability_engine_architecture.md`
(the flexible FTL/FIL-placeable design derived from this gap analysis).

Source of facts: the current-fw + emulator inventory compiled for this wave
(file:line evidence spot-checked against source during this write-up — see
`fil_ecc.spl:33-71`, `chip.spl:695-748`, `ftl.spl:617-631`, `hooks.spl:170-178`,
`nvme_types.spl:42-43`, `ftl.spl:398-415`, all confirmed to match cited
content). All claims below are either direct file:line citations or explicit
inferences labeled as such.

**2026-07-19 update (annotation only — the analysis below is NOT rewritten).**
The rel_* v1 reliability engine landed and closed several of the gaps this
document identified: `fw/rel_types.spl` (L1 shared types), `fw/rel_health.spl`
(L2 observability sink), `fw/rel_vref.spl` (L3 ROR-lite per-block vref
calibration), `fw/rel_ladder.spl` (L4 recovery-ladder retry FSM),
`fw/rel_refresh.spl` (L5 FCR/DEAR-lite refresh), `fw/rel_disturb.spl` (L6
STRAW-lite hottest-page disturb tracking), `fw/rel_wear.spl` (L7 SREA-lite
dwell-gated static WL), and an L8 wiring pass across `fil.spl`/`ftl.spl`/
`nvme_controller.spl`/`firmware.spl` (see `doc/04_architecture/hardware/
nand_recovery/reliability_engine_architecture.md` §4, gaps A2/A7). Affected §1
rows are annotated in place below with a `(2026-07-19: ...)` suffix; integration
oracle set is `fw/rel_wiring_check.spl`. **Not** part of this wave, still open
exactly as originally analyzed: RAIN production wiring (row unchanged below)
and `hooks.classify_hot`. Current status summary:
`doc/00_llm_process/feature_expert/nand_emu/skill.md` § "Implementation status".

---

## 1. Current state summary table

Status vocabulary:
- **implemented+wired** — code exists and a production (non-test) caller reaches it.
- **implemented-UNWIRED** — code exists, compiles, is exercised only by
  selftest/`*_check.spl`; no production caller.
- **actuator-only (no policy)** — a low-level control exists (e.g. "set this
  register") but nothing in firmware decides *when* to call it.
- **absent** — no code exists for this mechanism at this layer.

| Mechanism | Status | Evidence (file:line) |
|---|---|---|
| ECC — Hamming SECDED, 1-bit correct / 2-bit detect | implemented+wired | `fw/fil_ecc.spl:33-71` (`ecc_compute`, Hamming payload + meta guard), decode `fil_ecc.spl:86-103`; propagation `fil.spl:60-68`; fail-closed consumers `ftl.spl:521-522`, `ftl.spl:382-384,443-444`; SMART surfacing `nvme_controller.spl:55,359` |
| Read-retry / vref sweep | actuator wired, policy absent → **implemented+wired (2026-07-19)** | chain `chip.spl:743-748` (`set_vref_offset`, vref=128+offset) → `fil_nand_emu.spl:354-358` → `fil_fmc.spl:225-228` → `fil.spl:140-141` → `ftl.spl:174-175`; zero production callers — only `fil_nand_emu_check.spl:119-121`, `fil_nand_emu_e2e_check.spl:130-133`; on `NAND_ECC_FAIL` the read fails immediately, no retry loop; **2026-07-19:** retry policy landed — `fw/rel_ladder.spl` (recovery-ladder retry FSM) + `fw/rel_vref.spl` (7-entry offset table, ROR-lite per-block calibration cache persisted on `Fil`), mounted at `Fil.read_with_ladder` (`fil.spl:169-204`) and reached from production reads (`ftl.spl:198,214,632` — `read`/`read_status`/GC relocate); proven by `rel_wiring_check.spl` scenario 'a' (depth-2 recovery at cal −16) |
| Read-disturb scrub (`scrub_once`) | implemented-UNWIRED → **wired (2026-07-19)** | `ftl.spl:617-631`, threshold `READ_DISTURB_THRESHOLD = 50` (`nvme_types.spl:43`); counter `rd_disturb: [i64]` (`ftl.spl:29`), bumped `ftl.spl:109,117,347-352`, cleared on erase/reclaim `ftl.spl:354-359,544,548`; no production caller (only `gc_once` is wired: `nvme_controller.spl:485,491`, `hil.spl:113-114`); **2026-07-19:** `fw/rel_disturb.spl` (STRAW-lite hottest-page estimate — consumes, does not duplicate, `rd_disturb`) plus `Ftl.rel_tick`/`rel_tick_select` fire `scrub_once` as one of the one-reclaim-class-per-tick priority steps (`ftl.spl:756-780`), mounted in `nvme_controller.io_process`/`firmware.service_tick`; proven by `rel_wiring_check.spl` scenario 'b2' |
| Refresh-before-uncorrectable (FCR/DEAR-lite) | absent → **implemented+wired (2026-07-19)** | no row previously existed for this mechanism (new row, not a rewrite); **2026-07-19:** `fw/rel_refresh.spl`'s `rel_refresh_due` fires on a block's first observed ECC 1-bit correction (DEAR-lite) or once `cur_seq - last_prog_seq >= REL_REFRESH_AGE_SEQ()` (100000, seq-epoch age proxy); `Ftl.rel_drain_refresh`/`rel_tick` reclaim-rewrites the marked block (`ftl.spl:756-786`); proven by `rel_wiring_check.spl` scenario 'a' (refresh fires, mark clears post-reclaim) |
| Static wear leveling (`wear_level_once`) | implemented-UNWIRED → **wired (2026-07-19)** | `ftl.spl:605-615` (fires when `max_erase - erase_count(cold) > WL_THRESHOLD`), threshold `WL_THRESHOLD = 2` (`nvme_types.spl:42`); victim picker `ftl_gc.spl:15-27`; no production caller; **2026-07-19:** `fw/rel_wear.spl` (SREA-lite dwell gate: `dwell = total_erases - last_global_erase[blk]`, only fires once dwell ≥ `REL_WL_DWELL_MIN()`, resets on erase) mounted via `Ftl.rel_wear_level`/`rel_tick` (`ftl.spl:791-802`); proven by `rel_wiring_check.spl` scenario 'b1' |
| Dynamic wear leveling / GC victim scoring | implemented+wired, **not error/age-aware** | `policy_gc_victim` `ftl.spl:561-578`; default hook ignores erase count (`hooks.spl:52`); greedy fewest-valid only |
| RAIN (cross-channel XOR parity) | **DRAM-only parity, test-only recovery** | stripe model `rain.spl:26-91`; `rain_seal` incremental+scrub `ftl.spl:370-389`; `rain_recover_channel` `ftl.spl:416-465`; explicit non-power-safe, non-production note `ftl.spl:398-415` (parity table lives only in DRAM, never persisted; recovery only re-drivable within the same power session) |
| Spare-block remapping (`alloc_spare`) | implemented-UNWIRED → **wired (2026-07-19)** | `fil_badblock.spl:52-61` (spare pool = OP region blocks 56..63); no FTL caller — retired blocks drop from rotation but are never remapped to a reserved spare; **2026-07-19:** event-driven from the retire path (`fil.mark_bad` → `band.set_bad` → `alloc_spare`, `ftl.spl:842`) rather than a tick step, closing gap A7 (`reliability_engine_architecture.md` §4); proven by `rel_wiring_check.spl` scenario 'a' spare-substitution oracle |
| Runtime bad-block retirement | implemented+wired | program/erase failure → `bbt.mark_bad` + `fmc.set_bad` (`fil.spl:53-56,81-84`) |
| Factory bad-block table | implemented+wired | rebuild scan `ftl.spl:302-305`; emu support `chip.spl:759` (`set_factory_bad_blocks`) |
| Hot/cold classification (`hooks.classify_hot`) | **implemented-UNWIRED (actuator-only)** | `hooks.spl:170-178`; hook slot exists with clamp-to-{0,1} semantics but is never called outside selftest — no hot/cold write-path placement |
| Age / retention-time tracking | absent in FW; present in emu only → **seq/erase-count proxies live in FW (2026-07-19)** | FTL tracks only a monotonic `seq` (`ftl.spl` `next_seq`), no wall-clock/last-program-time per page or block; emu's `NePageMeta.last_prog_time` (`nand_types.spl:301`) and `NeBlockMeta.last_erase_time` (`nand_types.spl:311-322`) exist but feed only the emulator's own drift model, never read by firmware — **this original claim still holds** (FW does not read those emu fields); **2026-07-19:** FW instead grew its own two independent, explicitly-phenomenological proxies: `rel_refresh.spl`'s `last_prog_seq[blk]` vs. `cur_seq` (seq-epoch age, resets on write, `rel_refresh_on_write`) and `rel_wear.spl`'s `last_global_erase[blk]` vs. `total_erases` (erase-count dwell). Both are documented in-source as workload-relative, not wall-clock (`rel_refresh.spl:36-39`: "a year with no writes shows zero seq-age") |
| Soft information (per-cell reliability) | **chip-level only; FW wrapper doesn't re-export** | `NeChip.vt_histogram(page)->[256]i64` (`chip.spl:695-717`, confirmed: full per-cell stored-Vt distribution) and `read_margin(page)->i64` (`chip.spl:719-741`, valley width between erased/programmed lobes) exist on `NeChip`; `NandEmu` wrapper (`fil_nand_emu.spl`) exposes `program/read_page/erase_block/inject_*/set_vref_offset/set_block_wear` but does **not** re-export `vt_histogram`/`read_margin` — observability stops at the chip, FW read path senses only column-0/single-byte/hard-bit at one vref (`fil_nand_emu.spl:208-228`) |
| Policy hooks (`fw/hooks.spl`) | implemented+wired, **narrow** | 4 scalar-in/scalar-out slots (`gc_score`, `qos`, `hot_cold`, `telemetry`), fuel-bounded, forbidden-domain gate (`hooks.spl:71-124`); only `gc_score` has a live consumer; no FTL/NAND handle in the signature, so a policy needing counters/margins or rewrite actuation cannot plug in as-is |

---

## 2. Taxonomy family × local applicability

### 2.1 Read-reference-voltage recovery
**Applicable now.** The actuator (`set_vref_offset`) is wired end-to-end from
FTL down to the chip and the physics model actually shifts the sense boundary
(`vref = 128 + offset`, applied in `ne_sense`). What's missing is entirely
firmware-side: a retry loop on `NAND_ECC_FAIL` that walks a fixed or adaptive
offset table. Fixed read-retry, linear sweep, and bidirectional search are all
directly buildable and directly observable (ECC pass/fail per offset). Binary
search / gradient / ECC-margin-guided variants need a corrected-bit-count
signal from `fil_ecc` (already available — `injected_flips`-style count) —
also in scope now. Model-predictive / ML Vref prediction is out of scope (see
§4).

### 2.2 Retention-aware read recovery
**Applicable now, partially.** `physics.spl` genuinely models retention drift
(`ne_retention_delta`, function of `dt`, `pe`, and `vt-128`, negative/charge
loss only), so ROR-style per-block calibration and ReMAR-style
retention-model-aware reading are directly validatable: a firmware policy that
learns/predicts vref from block age and P/E count can be checked against the
emulator's own drift function. HeatWatch specifically needs a temperature
history input the emulator does not have — temperature-compensated reading is
therefore **needs emu growth** until a temperature parameter is added to
`NeCellParams`/physics. Per-page/per-wordline calibration is mechanically
possible (blocks/pages already addressable) but is not meaningfully different
from per-block calibration on SLC.

### 2.3 Layer-, wordline-, and process-variation-aware recovery
**Needs emu growth / mostly out of scope for v1.** v1 is explicitly SLC,
single-plane, no vertical-layer dimension (`nand_types.spl:48`,
`sectors_per_page=1` for S1). LaVAR, LI-RAID, per-layer retry tables, and
string-position-aware reading all require a modeled 3D-layer axis that does
not exist. Per-wordline calibration (as opposed to per-layer) is nominally
possible today but offers nothing beyond per-block calibration until layers
are added. Die/chip-specific calibration is meaningful only once >1 die/chip
profile is instantiated in the same test, which v1 supports structurally
(multiple `NeChip` instances) but nothing currently differentiates them beyond
seed.

### 2.4 Soft sensing and threshold optimization
**Applicable now, but the gap is at the FW/EDC seam, not the physics core.**
`vt_histogram` already returns the full 256-bin per-cell distribution and
`set_vref_offset` + repeated read already gives genuine multi-sense-at-offset
soft information — confirmed, not aspirational. The blocker is that (a) the
`NandEmu` wrapper doesn't re-export `vt_histogram`/`read_margin` to firmware,
and (b) the FW read path only ever takes one hard-bit sense at one vref. A
firmware-side soft-read/valley-search implementation (EBDN-style nonuniform
sensing, decoder-feedback-directed sensing) is directly buildable and
directly checkable against the emulator's ground-truth histogram. MMI/entropy
threshold selection and learned (NN) threshold estimation are out of scope
per the "never over-engineer" rule for v1 — fixed/heuristic threshold
selection is in scope.

### 2.5 Error-correcting-code recovery
**Already covered at the basic tier; everything past it is out of scope for
v1.** Hamming SECDED (1-bit correct, 2-bit detect) is implemented and wired
(`fil_ecc.spl`). BCH/Reed-Solomon/LDPC (hard or soft), adaptive code rate,
and all named LDPC schemes (ALCod, DHD, REAL, DyLDPC, etc.) require a
multi-bit-per-codeword correction channel that does not exist in the firmware
ECC model — `fil_ecc` operates on a modeled low payload window per page word,
not a real 512B sector with a soft-decodable code. See §4.

### 2.6 Neighbor-cell and interference-aware recovery
**Needs emu growth.** `physics.spl` has a disturb term
(`ne_disturb_delta`, driven by `rd_count`/`pd_count`) that is a
per-cell phenomenological proxy, not a per-neighbor-state model — each cell's
Vt evolves from its own counters and seed, with no coupling to a specific
adjacent cell's programmed state. NAC/ReNAC-style correction (read neighbor
state, adjust target-cell reference) needs a neighbor-topology term in the Vt
model that v1 does not have. Previous/next-wordline-assisted correction is
similarly blocked on there being no neighbor-state signal to read.

### 2.7 Failure-mode-specific probabilistic recovery
**Applicable now, medium lift.** RFR/RDR distinguish retention-dominated from
disturb-dominated errors and probabilistically flip the most suspicious bits.
Because `physics.spl` keeps retention and disturb as two distinct,
independently-computed deltas, an emulator-validated firmware policy that
infers "this error pattern looks retention-shaped vs. disturb-shaped" from
observable signals (block age via a new age-tracking field, `rd_disturb`
count which already exists) is buildable and checkable — the emulator can
inject a specific fault type and the policy's classification can be graded
against ground truth. This needs the soft-info wrapper gap (§2.4) closed
first for anything beyond simple heuristics.

### 2.8 Cross-page, cross-die, and parity recovery
**Partially covered, unwired for production.** RAIN (single XOR parity per
channel-stripe, RAID-4-style) is implemented (`rain.spl`) with working
seal/recover logic, but the parity table is DRAM-only and non-power-safe, and
recovery is exercised only by selftest (`ftl.spl:398-415`). The highest-value
local opportunity here is wiring RAIN into the production write/recovery path
and (separately, larger) making parity power-safe. LI-RAID and any
layer-aware parity placement are out of scope until layers exist (§2.3).

### 2.9 Read repair, remapping, and retirement
**Mixed — half already wired, half is exactly the "implemented-unwired"
inventory.** Runtime bad-block retirement and factory bad-block scan are
wired. Read reclaim (`scrub_once`) and spare-block substitution
(`alloc_spare`) are implemented but have zero production callers. Block-level
remapping is native to the FTL's band structure; page-level/wordline
remapping beyond that is not modeled and not needed at SLC granularity.

### 2.10 Physical or quasi-physical cell recovery
**Erase/reprogram already fundamental; dwell-aware scheduling is a real
near-term opportunity; thermal/experimental methods are out of scope.**
Erase-and-reprogram is how every reclaim already works. `NeBlockMeta`
already carries `last_erase_time` (emu-only), which is exactly the input
SREA-style dwell-aware wear leveling needs — this is directly buildable
against the emulator today (see §3). Thermal annealing/SmartHeating and
CellRejuvo-style experimental reprogramming require physics the emulator does
not model (temperature, alternate reprogram semantics) — out of scope (§4).

### 3.1 Program-operation prevention
**Already covered inside the physics core; not FW-actuable in v1.** ISPP
pulse-and-verify is implemented in `physics.spl` (`ispp_start/step/max/
pv_level/prog_sigma`), but it is internal to the emulator's `program_cell`
model — firmware issues a whole-page PROGRAM command and has no per-pulse
visibility or control in v1's command set. Program-inhibit/self-boosting is
explicitly NAND-die-internal (per the taxonomy doc itself) — out of scope
regardless of emulator maturity. DVA/DPES-style program-voltage scaling over
device lifetime is conceptually FW-placeable (choose target margins by wear)
but has no emulator-observable hook yet since ISPP parameters are fixed
`NeCellParams`, not runtime-settable by firmware.

### 3.2 Erase-operation prevention
**Not FW-actuable in v1; low near-term value.** Same shape as §3.1: erase
pulse/voltage/duration control lives inside `physics.spl`'s erase model, and
firmware issues a single ERASE 60h/D0h command with no sub-parameters to
tune. DeVTS/AERO/GuardedErase-style adaptive erase would require the command
FSM and `NeCellParams` to expose a controllable erase-stress knob — that is
an emulator-growth item, not a firmware gap, and lower priority than the
retention/disturb items below.

### 3.3 Retention-error prevention and refresh
**Applicable now — one of the strongest opportunities.** FCR/DEAR-style
"read, correct, refresh before ECC capability is exceeded" is directly
buildable: the emulator already computes real retention drift, and the FW
already has read-count and erase-count signals; the only missing piece is (a)
an age/last-program-time signal in FTL (currently emu-only) and (b) wiring a
refresh trigger. WARM-style hot/cold-aware refresh sits directly on top of
the already-implemented-but-unwired `classify_hot` hook. HeatWatch-style
temperature/dwell fusion is blocked on temperature (§4); dwell alone
(`last_erase_time`) is available now.

### 3.4 Read-disturb prevention
**Applicable now — the other strongest opportunity.** Per-block read counters
already exist and drive an unwired scrub (`scrub_once`); per-page counters
already exist in the emulator (`NePageMeta.rd_count`) but are unused by
firmware. STRAW-style wordline/page-granularity disturb tracking-and-reclaim
is close to a pure wiring exercise: promote the existing emu per-page counter
into an FTL-visible signal and reclaim at finer granularity than the current
block-only `rd_disturb`. Pass-voltage (Vpass) tuning is NAND-die-internal and
out of scope (§4) — the emulator's disturb model does not expose a Vpass
parameter to the firmware layer, by design.

### 3.5 Program-interference and lateral-charge prevention
**Mostly out of scope for FW in v1.** `physics.spl` folds program-disturb
into the same `ne_disturb_delta` term as read-disturb, driven by `pd_count`
with no per-neighbor or per-data-pattern structure. Program-order/shadow
sequencing and neighbor-state-aware programming require the FSM to expose
sub-page program ordering and a neighbor-state model that v1 does not have —
this is squarely an emulator-growth item, lower priority than §3.3/§3.4 since
those are already close to wired.

### 3.6 Data encoding and state-mapping prevention
**Not observable in v1 — needs emu growth before it's worth building.** v1 is
SLC (1 bit/cell): Gray coding, alternate Gray mappings, and state balancing
are inherently multi-level-cell concerns and have no meaning on a two-state
cell. Data scrambling/whitening is nominally cell-count-agnostic, but the
emulator's per-cell Vt evolves from a `splitmix32` seed and counters, with no
dependency on the actual data pattern written — so a scrambling policy would
have zero observable effect in the current physics model. This entire family
is out of scope until (a) MLC/TLC coding exists or (b) the physics model
grows a data-pattern-dependent disturb term.

### 3.7 Wear-leveling algorithms
**Applicable now — directly overlaps the inventory's unwired-mechanism
list.** Both dynamic WL (via GC victim scoring) and static WL
(`wear_level_once`) are implemented; static WL simply has no caller. SREA-style
dwell-aware WL is a natural extension once `last_erase_time` is surfaced to
FTL (see §3.3/§2.10). Layer-aware, wordline-aware, and SLC/TLC/QLC-mode-aware
variants are out of scope per §2.3/§3.6.

### 3.8 Write-amplification prevention
**Partially covered; the extension point is already scaffolded.** GC
(`gc_once`) is wired; the default victim scorer is greedy-fewest-valid and
explicitly ignores the erase count that is already passed into the hook
(`hooks.spl:52`). Cost-benefit/wear-aware/error-aware GC is therefore a small
extension of an existing, already-wired seam — not a new mechanism. Broader
write-reduction (over-provisioning, TRIM, multi-stream, ZNS) sits at the FTL
band/namespace level not covered by this inventory pass and is out of scope
for this gap analysis.

### 3.9 Cell-mode and capacity reconfiguration
**Not applicable in v1.** No QLC/TLC/MLC mode exists to convert from or to —
the emulator is SLC-only by construction (`ne_sense_bit`, one bit per cell).
This entire family requires a multi-level-cell model as a prerequisite and is
out of scope until v2+.

### 3.10 Bad-block and fault-containment prevention
**Mostly covered; the remaining gap is spare remapping.** Factory and
runtime bad-block detection/retirement are both wired. Spare-block pools
exist (`alloc_spare`) but are never called — retired blocks are dropped, not
remapped into the reserved spare region. RAID/RAIN reconstruction exists but
is test-only (§2.8). Parity patrol/scrubbing overlaps `rain_seal`, itself
unwired for production.

### 3.11 Predictive reliability and machine-learning algorithms
**Fixed-threshold family already in use; ML is explicitly out of scope for
v1.** `READ_DISTURB_THRESHOLD` and `WL_THRESHOLD` are exactly the "fixed
thresholds" model family from the taxonomy, already implemented (just
unwired for scrub/WL respectively). P/E count, read count, and a
corrected-bit/error count (`fil_ecc`'s flip count) are all observable inputs
today; retention age is observable only inside the emulator, not FTL (§1).
This gives enough signal for a DEAR-style "error-rate-triggered" refresh
without any ML — extending the fixed-threshold approach with one more
trigger (corrected-bit count) is in scope; regression/Bayesian/neural model
families are out of scope per the repo's "never over-engineer" rule and lack
of any training data pipeline.

---

## 3. Ranked opportunity list — closeable with the current emulator as validation harness

Ordered roughly by (validation strength on v1 SLC emulator) × (value) ÷
(size). All are checkable by asserting emulator-observable outcomes (ECC
pass/fail, `vt_histogram`, injected fault recovery, erase-count spread)
rather than self-comparison.

1. **Wire the 4 existing-but-unwired mechanisms** (`scrub_once`,
   `wear_level_once`, `alloc_spare`, `hooks.classify_hot`) into production
   call sites. Descends from: FCR (3.3), static WL (3.7), spare-pool
   substitution (3.10/2.9), WARM (3.3). Evidence: `ftl.spl:617-631`,
   `ftl.spl:605-615`, `fil_badblock.spl:52-61`, `hooks.spl:170-178` already
   compile and pass selftest — this is pure wiring, no new algorithm. Size:
   **small** (4 independent small changes).

2. **Read-retry ladder on `NAND_ECC_FAIL`.** Descends from: fixed/linear
   read-retry (2.1). Evidence: the emulator already shifts sense boundary via
   `set_vref_offset`; a test can assert that a page whose retention drift
   makes vref=0 fail decodes successfully at a swept offset. Size: **medium**
   (retry loop + policy module below `fil`, per the architecture doc's
   layering rule).

3. **ROR-lite per-block vref calibration.** Descends from: ROR (2.2).
   Evidence: after a successful retry at offset N, remember N per block and
   try it first next time; validate against the emulator's actual retention
   drift curve (`ne_retention_delta`) converging to the physically correct
   offset. Size: **medium**.

4. **STRAW-lite per-page disturb tracking + reclaim.** Descends from: STRAW
   (3.4). Evidence: `NePageMeta.rd_count` already exists in the emulator and
   is presently invisible to firmware, which only sees the coarser
   block-level `rd_disturb`; surfacing it gives finer-grained, directly
   observable reclaim triggers. Size: **small-medium**.

5. **FCR/DEAR-lite refresh using the ECC decode signal.** Descends from: FCR,
   DEAR (3.3, 3.11). Evidence: `fil_ecc.ecc_decode` already produces a
   clamped 0/1/2+ correction-count signal per read (`fil_ecc.spl:81-115`) —
   note this is coarse (a decode-result bucket, not a rich per-bit corrected
   count; `injected_flips` is a fault-injection input, not a decoder
   syndrome). "First 1-bit correction observed" is a legitimate DEAR-lite
   trigger at that granularity: rewrite before the block reaches the 2-bit
   uncorrectable ceiling, validated by forcing retention drift toward failure
   and checking the refresh fires before `NAND_ECC_FAIL`. Size: **medium**.

6. **SREA-lite dwell-aware wear leveling using `last_erase_time`.** Descends
   from: SREA (2.10, 3.7). Evidence: `NeBlockMeta.last_erase_time` exists in
   the emulator; extend `wear_level_once`'s victim scorer to prefer blocks
   with longer idle dwell (their physics-model wear-widening term is smaller
   at read time), checkable via `vt_histogram` sigma before/after. Size:
   **small-medium** (once #1 wires the base mechanism).

7. **Re-export `vt_histogram`/`read_margin` through `NandEmu` and add a
   valley-search soft read.** Descends from: soft sensing / valley search
   (2.1, 2.4). Evidence: the chip-level functions already exist and are
   confirmed correct; only the wrapper re-export and a firmware-side
   consumer are missing. This unlocks §2.4/§2.7/§3.4 downstream work. Size:
   **medium**.

8. **Error-aware/age-aware GC victim scoring.** Descends from: cost-benefit
   GC (3.8). Evidence: erase count is already passed into `gc_score` and
   ignored by the default (`hooks.spl:52`) — extending the default scorer to
   weight it is a small, already-scaffolded change, checkable by asserting
   GC now avoids high-erase-count blocks under contention. Size: **small**.

9. **Wire RAIN into the production reclaim path + document/track the
   power-safety gap explicitly** (rather than leaving it silently
   selftest-only). Descends from: RAID/RAIN parity recovery (2.8). Evidence:
   `rain_seal`/`rain_recover_channel` already work correctly within a power
   session (`ftl.spl:398-465`); wiring it as an FTL-level last-resort after
   ECC fail is checkable via inject(EraseFail) + verify reconstruction. Size:
   **medium-large** (full power-safety fix — persisted parity — is
   explicitly out of this list's size band; wiring the volatile-session
   version is the near-term slice).

10. **RFR/RDR-lite failure-mode classification** using existing disturb vs.
    retention deltas as ground truth to grade a firmware heuristic that
    guesses which failure mode produced a given ECC failure (informs which
    recovery to try first: vref shift vs. scrub vs. RAIN). Descends from:
    RFR, RDR (2.7). Evidence: `physics.spl` keeps the two deltas
    independently computable, so a test can inject a pure-retention or
    pure-disturb fault and grade classification accuracy. Size: **medium**,
    and best sequenced after #2/#7.

---

## 4. Explicitly out of scope (with reasons)

- **LDPC soft/hard decoding (2.4 advanced, 2.5 LDPC families).** The firmware
  ECC model (`fil_ecc.spl`) is Hamming SECDED over a modeled low payload
  window — there is no multi-bit-per-codeword correction channel for an LDPC
  decoder to operate on. Building LDPC would mean replacing the ECC model
  itself, which is out of this gap analysis's scope (a code-family swap, not
  a recovery/prevention policy addition).
- **Temperature-dependent models** (HeatWatch's temperature term, 3.1/3.2
  temperature-aware program/erase, 3.4 temperature-dependent read-disturb
  thresholds, thermal annealing/SmartHeating in 2.10). `NeCellParams` and
  `physics.spl` have no temperature input; nothing in the emulator varies
  with simulated temperature. Any temperature-aware policy would be
  unvalidatable — there is no ground truth to check it against — until a
  temperature axis is added to the physics model (a v2+ emulator-growth
  item).
- **Layer / 3D-NAND variation** (2.3 LaVAR and family, 2.8 LI-RAID,
  layer-aware entries across 3.x). v1 is explicitly single-plane SLC with no
  vertical-layer dimension (`nand_types.spl:48`). There is nothing for a
  layer-aware algorithm to key off.
- **MLC/TLC/QLC coding and cell-mode reconfiguration** (3.6 Gray-code/state
  mapping, 3.9 cell-mode reconfiguration). The sense function is explicitly
  1-bit-per-cell (`ne_sense_bit`); these mechanisms are meaningless on a
  two-state cell and their taxonomy entries all presuppose multi-level
  states.
- **NAND-die-internal program/erase-inhibit mechanisms** (3.1 self-boosting
  sub-family, 3.4 Vpass tuning). These are explicitly called out as
  NAND-die-internal rather than SSD-FTL algorithms in the taxonomy doc
  itself; the firmware command set (single PROGRAM/ERASE commands) has no
  sub-parameters for them, and adding such parameters would mean modeling
  die-internal circuitry the emulator's Vt-array abstraction deliberately
  does not represent.
- **Machine-learning model families** (3.11 regression/Bayesian/neural/RL).
  No training-data pipeline exists or is proposed; the repo's "never
  over-engineer" rule and the emulator's deterministic seed-based physics
  make fixed-threshold and heuristic models (already partially in place —
  `READ_DISTURB_THRESHOLD`, `WL_THRESHOLD`) the appropriate v1 tier. ML
  entries are noted in the taxonomy for completeness, not as a v1 target.
- **Physical/experimental reprogramming** (CellRejuvo-style dense/sparse
  state manipulation, 2.10). Requires reprogram semantics beyond
  erase-then-ISPP that the emulator's command FSM does not define, and a
  physics model of partial-state recovery that does not exist.
