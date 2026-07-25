# NVMe FW `rel_*` reliability-engine — rv32 self-test port assessment

**Status (2026-07-19): ASSESSMENT, not a commitment.** This is a plan/decision
doc answering "should the `fw_rv32` self-test port the new `rel_*` reliability
lanes" — it recommends **NOT NOW**, tracked as a follow-up gated on `rel_*`
becoming a production caller in `fw/`. Ground truth: direct inspection of
`examples/09_embedded/simpleos_nvme_fw/fw/` and `fw_rv32/` on 2026-07-19, plus
`doc/04_architecture/hardware/nand_recovery/reliability_engine_architecture.md`
and `doc/05_design/hardware/nand_recovery/recovery_algorithms_design.md`.

---

## 0. What `fw_rv32` actually is (this determines everything below)

`fw_rv32/` is **not** a running firmware build of `fw/`. Per its own README
("`entry.spl` remains the standalone logic reference... The full 22-module
no-alloc port of `../fw/` remains the larger ceiling") it is a **bare-metal
self-test / logic floor**: for each of 23 `fw/` subsystems (RAIN, ECC,
scheduler, power/thermal, map cache, band, journal, HIL, queue-phase,
io-command, flush, admin, reactor, policy/target, DRAM/durability, wear/scrub,
media-retire, power-cycle, backpressure/abort, feature-guard, namespace-guard,
target-profile, task-pool), `fw_rv32` re-expresses the subsystem's *decision
logic* as pure scalar free functions, validated against literal oracle values
in `*_cases.spl`, aggregated by bit-flagged section checks
(`logic_sections_primary.spl` / `logic_sections_secondary.spl` →
`logic.spl` → `entry.spl` → `rt_rv32_boot_optional_nvme_fw_selftest`) into one
UART line: `ALL RV32 NVME FW CHECKS PASS`.

Confirmed by direct grep: **zero** `[i64]`/`[u8]`/array-typed declarations
exist anywhere under `fw_rv32/*.spl` (185 files), and **zero** `use` imports
reference `fw/` — the two trees are fully decoupled at compile time. `fw_rv32`
holds no state at all; it is a battery of "given these scalar inputs, does the
port produce the oracle scalar output" assertions that boots inside
`src/os/kernel/arch/riscv32/boot.spl`'s no-heap, no-array constraint.

## 1. Is the port *required* for the current goal?

**No.** Two independent facts rule it out as a near-term requirement:

1. **`rel_*` is not yet wired into `fw/` itself.** `grep -n "rel_" fil.spl
   ftl.spl nvme_controller.spl` finds only a design-note comment in `fil.spl`
   (line 31-32) — no call site. The architecture doc §4 ("Wiring plan — the
   four unwired mechanisms") explicitly documents that `scrub_once`,
   `wear_level_once`, `rain_seal`, `alloc_spare` have "zero production
   callers"; `rel_health`/`rel_vref`/`rel_disturb`/`rel_ladder`/`rel_refresh`/
   `rel_wear` are validated only by their own co-located `*_check.spl` and
   `rel_seams_check.spl`, not mounted into the FTL maintenance tick or FIL
   read path. Porting a policy family to the bare-metal self-test before it is
   even a production caller in the portable host build would validate logic
   the firmware doesn't run yet.
2. **rv32 is out of scope in the architecture/design docs.** Neither
   `reliability_engine_architecture.md` nor `recovery_algorithms_design.md`
   mentions `fw_rv32`, "rv32", or "baremetal" as a goal — the one hit
   (design doc line 48, "fw_rv32 no-module-init rule") is a *style*
   constraint the authors chose to future-proof for (fn-returning constants,
   no `Dict`, i64-first, named-struct returns), not a stated rv32-porting
   requirement. `rel_*` was written port-*friendly*, not port-*complete*.

So the rv32 lane's current job — RAIN/ECC/map/band/journal/HIL/... self-test
parity with `fw/`'s already-*wired* logic — is unaffected by leaving `rel_*`
unported. This is a legitimate, trackable gap, not a silent omission: it is
recorded here precisely so it doesn't rot into an invisible divergence (see
§4, the LBA 1024/3072 precedent).

### Board-runnable rule interaction

The repo's board-runnable rule requires QEMU-developed work to stay runnable
on the real dev board. `fw_rv32` genuinely is the firmware's board-runnable
proxy (it is what boots under `qemu-system-riscv32 -bios none` and, per the
same doc family, is meant to run on real rv32 hardware). So the rule's spirit
*does* eventually reach `rel_*` — but only once `rel_*` is real, wired
firmware behavior, not an unwired policy lane validated solely against the
host `nand_emu` model. Today there is no board-runnable *feature* to keep in
parity, because there is no production caller. Once §4's trigger fires, the
port stops being optional under this rule.

## 2. If/when ported: lane mapping, array representability, sizes

### 2.1 The porting unit is per-field, not per-function

The existing precedent (`ftl_band.spl` → `logic_band_core.spl`,
`ftl_map.spl` → `logic_map_core.spl`) does **not** port array-holding
struct methods 1:1. It decomposes each method into one scalar transition
per **field it touches**, with the array element passed in as a plain scalar
parameter and the caller (which owns the real array) responsible for the
index/loop. E.g. `BandAlloc.mark_valid()` (`fw/ftl_band.spl`, mutates
`blk_valid[blk]` and `blk_state[blk]`) becomes
`_rv32_band_mark_valid_count(block_state, was_valid, count) -> i64` in
`logic_band_core.spl` — a pure function of one block's already-extracted
scalar state, not a ported array method.

`rel_*` mutators are **wider** than the band/map precedent: several touch
multiple fields of one struct per call (`rel_health_note_read` updates
`reads`, `corrected_sum`, `corrected_events`, and conditionally
`retry_depth_max` in one call). A faithful port therefore needs **one small
scalar fn per updated field**, not one fn per `rel_*` mutator — e.g.
`rel_health_note_read` → 3-4 separate `_rv32_rel_health_*` fns (next `reads`,
next `corrected_sum`, next `corrected_events`, next `retry_depth_max`), each
independently oracle-tested. This expands function *count* relative to
`fw/`'s fn count; it does not expand line count proportionally, since each
extracted fn is a few lines.

### 2.2 Array representability — confirmed representable, never resident

Every `rel_*` module's per-block array field is genuinely reducible to the
band/map pattern, **and no `rel_*` algorithm requires an in-module scan over
the whole array** (checked directly): `rel_wear_due(st, cold_blk, erase_min,
...)` takes the global `erase_min` as a caller-supplied scalar — the
min/max-across-blocks scan lives at the FTL mount level, outside `rel_*`,
today. So `[i64]`-of-`NUM_BLOCKS` is representable in the `logic_*` idiom the
same way it already is for `blk_state`/`blk_valid`/`valid` in
`ftl_band.spl`: **the array itself is never resident in `fw_rv32`** (nothing
there holds state); only the pure per-element transition survives, verified
against literal before/after scalar oracles.

Per-module findings (`fw/` line counts as of `335e7715aeb7`):

| `fw/` module | Lines | Array fields (all `[i64]`, len `NUM_BLOCKS`=64) | Port shape |
|---|---|---|---|
| `nd_types.spl` | 150 | none — single-field `idx: i64` newtypes + scalar coord math | **Trivially portable as-is** — closest thing to a 1:1 port in this set; no decomposition needed. |
| `rel_types.spl` (`RelLadderState` only) | (part of 157) | none — all scalar/`NdBlock` fields | Trivially portable (mirrors `nd_types`). |
| `rel_types.spl` (`RelVrefCache`/`RelRefreshState`/`RelDisturbState`/`RelWearState`/`RelHealth`) | (part of 157) | 3 / 2 / 2 / 1 / 5 respectively (13 arrays total) | Per-field scalar-parameter decomposition (§2.1); no `logic_rel_types_core.spl` struct itself is portable — only its *field transitions* are, distributed into each lane's core file. |
| `rel_health.spl` | 123 | 5 (`reads`, `corrected_sum`, `corrected_events`, `retry_depth_max`, `refresh_cause`) | `logic_rel_health_core.spl`: ~4-5 scalar fns (`note_read` split by field, `rber` derived calc, `mark_cause`, `on_erase`). |
| `rel_vref.spl` | 113 | 3 (`offset`, `valid`, `gen`) | `logic_rel_vref_core.spl`: table lookup fns (`rel_vref_table_at`/`clamp_offset`) port ~1:1 (already scalar); `lookup`/`calibrate`/`decay_on_erase` split per field. |
| `rel_disturb.spl` | 122 | 2 (`hot_page`, `hot_count`) | `logic_rel_disturb_core.spl`: Boyer-Moore-majority `observe` split into hot_page/hot_count transitions; `due`/`clear` scalar as-is. |
| `rel_refresh.spl` | 142 | 2 (`last_prog_seq`, `marked`) | `logic_rel_refresh_core.spl`: `due`/`on_write`/`enqueue` split per field. |
| `rel_wear.spl` | 71 | 1 (`last_global_erase`) | `logic_rel_wear_core.spl`: `on_erase` (1 field), `due` already scalar (`erase_min` is a param, confirms §2.2). |
| `rel_ladder.spl` | 135 | none (`RelLadderState` is pure scalars) | Trivially portable — no array decomposition; port the phase constants + `rel_ladder_step` state machine roughly 1:1. |

Total current `rel_*` + `nd_types` source: **1,013 lines across 8 files**
(863 `rel_*` + 150 `nd_types`). Using the observed `fw/`→`fw_rv32` core-file
compression ratio on precedent pairs (`ftl_map.spl` 371→`logic_map_core.spl`
42 = ~11%; `ftl_band.spl` 438→`logic_band_core.spl` 55 = ~13%; `fil_ecc.spl`
203→`logic_ecc_core.spl` 12 = ~6%; the RAIN pair runs higher, ~37%, because
RAIN's logic was already arithmetic-only) — a `rel_*` core-file port would
land **roughly 100-200 lines of core logic**, split across ~7 new
`logic_rel_*_core.spl` files (one per lane, matching the existing per-lane
`fw/` file split). Oracle `*_cases.spl` files dominate file *count*, not line
count, in the existing precedent (`logic_band_*` alone has ~15 cases files
under its 55-line core) — expect on the order of **15-25 new files, a few
hundred lines total**, following the existing `_cases.spl` → aggregator →
`logic_sections_*.spl` fan-in convention. This is a rough order-of-magnitude
estimate, not a scoped task breakdown.

### 2.3 Anti-drift guard strategy — do not just copy the LBA precedent's guard

The task framing that inspired this doc points at "logic_check now guards
3072" as the model to imitate. On inspection that guard is **weaker than it
sounds**: `logic_map_lba_cases.spl` asserts boundary literals (`1024`,
`2048`, `3071`, `3072`) copied by hand from `fw/nvme_types.spl:39`
(`LBA_COUNT: i64 = 3072`), with only a code comment
(`# LBA_COUNT (fw/nvme_types.spl) — matches ...`) tying the two together. It
is a **regression** oracle — it would catch the code reverting to the old
`1024` bound — but it does **not** catch `fw/nvme_types.spl`'s `LBA_COUNT`
changing again to a *new* value without a matching `fw_rv32` literal update.
That is exactly the failure mode the 2026-07-18 fix (commit `335e7715aeb7`)
closed after the fact, not before.

A `rel_*` port, if it happens, should not repeat this weaker pattern for its
~9 magic numbers (`NUM_BLOCKS=64`, `REL_WL_DWELL_MIN`, `REL_REFRESH_ERR_EVENTS`,
`REL_REFRESH_AGE_SEQ`, `rel_disturb_hotpage_min`, vref table entries, ...).
Recommended stronger guard, feasible because `logic_check.spl` already runs
on host (`bin/simple run .../fw_rv32/logic_check.spl`), unlike `entry.spl`
which is boot-linked:

- Add a **host-only** cross-check file (e.g. `fw_rv32/logic_rel_drift_check.spl`)
  that is **excluded from `logic.spl`/`entry.spl`'s import graph** (so the
  boot-linked baremetal build stays `fw/`-import-free, preserving the
  freestanding no-alloc constraint) but **does** `use nvme_types.*` /
  `use rel_types.*` from `../fw/` when run as a standalone host check, and
  asserts each `fw_rv32` literal equals the corresponding `fw/` constant.
- This turns "matches `fw/nvme_types.spl`" from a comment promise into an
  executable one, without touching the bare-metal link graph at all — the
  boot path keeps importing nothing from `fw/`; only the *host-run* drift
  check does.

## 3. Recommendation

**Do not port `rel_*` to `fw_rv32` now.** File it as a tracked follow-up
rather than doing it speculatively, for two reasons that both point the same
way: (1) `rel_*` is not yet a production caller in the portable `fw/` build
it would be shadowing (§1), so a port would validate unused logic; (2) rv32
is not a stated goal of the reliability-engine architecture/design docs, and
the module family was deliberately written port-*friendly* (i64-first, no
`Dict`, fn-returning constants, named-struct returns, no `rel_*`-internal
array scans — §2.2) precisely so that a later port stays cheap, not so that
it must happen immediately.

**Trigger condition for revisiting:** once `rel_*` lands as an actual
production caller inside `fw/`'s FTL maintenance tick / FIL read path (per
architecture §4's wiring plan — `gc_once`/refresh-rewrite/`scrub_once`/
`wear_level_once` priority order sharing `GC_RESERVE`), parity with the
existing 23 `fw_rv32` logic floors argues for adding a 24th "rel" section
(next bit flag `2^23` = `8388608`) using the per-field decomposition and
host-only drift-check strategy in §2. Until that trigger fires, this
document is the honest record of the gap and the plan to close it, not a
commitment to close it on any timeline.

This assessment does not claim rv32-porting is risk-free or trivial once
triggered — the per-field fn-count expansion in §2.1 and the untested
host-only-check-exclusion mechanics in §2.3 are both real unknowns that a
future implementation pass would need to work through, not assume away.
