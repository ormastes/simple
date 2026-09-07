# rel_health RBER / corrected_events are blind to every read-retry-ladder recovery

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
