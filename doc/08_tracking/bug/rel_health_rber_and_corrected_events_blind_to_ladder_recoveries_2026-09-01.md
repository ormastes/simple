# rel_health RBER / corrected_events are blind to every read-retry-ladder recovery
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- id: rel-health-rber-blind-to-ladder-2026-09-01
- date: 2026-09-01
- area: examples/09_embedded/simpleos_nvme_fw/fw (NVMe firmware reliability layer)
- severity: medium — observability defect; the FCR (age/error) refresh trigger
  sourced from `corrected_events` can never fire from a Vref recovery.
- status: open

## Summary

`rel_health_rber()` and `RelHealth.corrected_events` cannot move on a read that
the recovery ladder recovered. Both are fed by `RelReadResult.corrected`, which
`Fil.read_with_ladder` fills from the **last** (winning) sense — a sense that by
definition decoded cleanly and therefore reports `corrected = 0`. The offset-0
hard read that actually FAILED (`NAND_ECC_FAIL` → `fil_corrected_of` = 2) is
overwritten by each subsequent rung and never reaches the sink.

Net effect: a block can be silently recovering at rung -24 on every read and its
RBER estimate stays exactly 0 ppm.

## Evidence (measured 2026-09-01, `bin/simple run`, Rust seed)

Sweep over `emu_set_block_wear` / `emu_advance_time_s` on the Vt-physics NeChip
backend, reading LBA 2 over the ordinary NVMe path:

```
wear=3000 secs=2592000  st=0   data=1 rber=0 cal=-8  rawcode=2 rawdata=255
wear=3000 secs=31536000 st=0   data=1 rber=0 cal=-16 rawcode=2 rawdata=255
wear=6000 secs=86400    st=0   data=1 rber=0 cal=-24 rawcode=2 rawdata=255
wear=9000 secs=86400    st=641 data=0 rber=0 cal=0   rawcode=2 rawdata=255
```

`cal` (the persisted ROR Vref offset) walks -8 → -16 → -24 as damage grows, and
the raw ladder-bypassing read fails ECC (`rawcode=2`) in every row — so real
recovery work is happening. `rber` is 0 in all of them, including the row where
the ladder had to go three rungs deep.

`retry_depth_max` and `refresh_cause` DO discriminate (measured 1 and
`rel_cause_err()` = 2 respectively at wear=6000/1d), which is why
`examples/09_embedded/simpleos_nvme_fw/fw/nvme_emu_recovery_check.spl` uses those
as its health oracle and explicitly does NOT assert on RBER. An RBER assertion
there would have been an assertion that cannot fail.

## Code

`fw/fil.spl` `Fil.read_with_ladder`:

- `obs = rel_read_obs(rd.code, rd.corrected, a.arg, st.depth)` is reassigned on
  every retry rung.
- both success exits return `rel_read_result_ok(..., obs.corrected)`.

`fw/ftl.spl` `rel_note_read` folds that value into `corrected_sum` and gates
`corrected_events` on `corrected >= 1`.

## Suggested fix (not applied — reporting only)

Carry the WORST (or the first) `corrected` seen across the ladder walk rather
than the last, e.g. track `var worst_corrected` in `read_with_ladder` and return
that. A recovered read cost real ECC work and the sink should say so. Whichever
convention is chosen, `rel_health_rber`'s docstring should state it.

## Repro

```
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/nvme_emu_recovery_check.spl
```
(verdict line `NVME EMU RECOVERY OK`; the RBER finding is recorded in the
comment block above the health assertions, not asserted).



---

## Lane disposition 2026-11-13 (p3-misc-b)

open NVMe-emulator modeling gap; owner: rel_health/nvme lane with emulator fixtures.
---

## Addendum 2026-11-13 (live-p3-l4, work/live-p3-l4-20261113, base f790f7f266e) — FIX LANDED (worst-corrected convention); behavioral emu before/after host-blocked

**Fix landed** in `examples/09_embedded/simpleos_nvme_fw/fw/fil.spl`
`Fil.read_with_ladder`: a `worst_corrected` bucket now tracks the max coarse
ECC bucket seen across the whole ladder walk (initialized from the offset-0
sense, updated on every retry rung) and BOTH success exits
(`rel_act_accept`, `rel_act_calibrate`) return `rel_read_result_ok(rd,
st.depth, worst_corrected)` instead of the last/winning sense's `obs.corrected`
(which decoded cleanly and reported 0). The `RelReadResult.corrected`
docstring and `rel_health_rber`'s docstring now state the convention
explicitly (per this record's requirement). The FTL fold
(`rel_health_note_read`) is untouched: a recovered read now contributes its
real cost (e.g. uncorrectable-at-offset-0 = 2) to `corrected_sum` and counts
one `corrected_events` event, so RBER can move off exactly-0 ppm and the FCR
(age/error) refresh trigger can fire from a Vref recovery. The failure exits
(`rel_read_result_fail`, corrected hardcoded 2) are unchanged; clean reads
(depth 0, single sense) are unchanged (worst = the one sense's bucket).

**Verification status (honest):**
- `fw/rel_health_check.spl` (the sink's assertion script: RBER exact ratios,
  corrected_events counting, per-block isolation) — `REL HEALTH OK` on the
  tracked seed with the change.
- `fw/nvme_emu_recovery_check.spl` compiles and starts under the seed with
  the change (no regression in the touched path).
- Behavioral before/after on the Vt-physics NeChip recovery path is
  HOST-BLOCKED on this Windows lane: a single worn+aged read through the
  ladder exceeded 270 s wall under the seed interpreter (measured twice with
  step markers — the offset-0 FAILING sense plus rung retries dominate; the
  clean-read control is fast). The pre-fix probe did print the expected
  blind-sink signature is therefore not re-demonstrated end-to-end here; the
  discriminating assertion (`corrected_events` delta >= 1 on a recovered
  read) should be added to `nvme_emu_recovery_check.spl`'s section A oracle
  on a host where that spec completes (it could not complete within 300 s
  here even before this change — pre-existing host slowness, not caused by
  the fix).

Residual owner item: the shadow-word seam (prereq 1b) for a true bit-rate
RBER remains as the record's architecture note describes. No open code debt
from this lane beyond the spec-strengthening recommendation above.
