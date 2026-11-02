# stage2_parse_shard_child_av_large_closure_2026-11-02

- Status: **open** (worked around by env flags; parent in-process fallback completes)
- Severity: P1 (phase-3 targeted builds: wasted parse time, noisy failures)
- Owner area: `src/app/cli/parse_shard_main.spl` / `src/compiler/80.driver` parse shard
- Workaround: `SIMPLE_PARSE_SHARDING=0` and `SIMPLE_FILE_FIBERS=0` (inventory row
  `stage2_parse_shard_child_av_large_closure_2026-11-02` in
  `doc/03_plan/bootstrap/workaround_inventory_2026-11-01.md`)

## Symptom

Frozen stage2 parse-shard children exit with `-1073741819` (0xC0000005, access violation) on
CompilerDriver-sized closures, at any shard count. The parent process then falls back to parsing in-process,
which completes, so the build succeeds but only after the failed children are paid for.

## Evidence (AV counts per run)

| run | child AVs |
|---|---|
| parsesel_obj2 | 2 |
| parsesel_obj3 | 2 |
| combined1 | 3 |
| combined2 | 2 (at `SIMPLE_PARSE_SHARD_MAX=1`, then in-process fallback) |
| trytext batch1r | 2 |

Lowering `SIMPLE_PARSE_SHARD_MAX` to 1 does not remove the AV, so the fault is not a shard-count race; it
tracks closure size.

## Workaround

`SIMPLE_PARSE_SHARDING=0` and `SIMPLE_FILE_FIBERS=0` (plus `SIMPLE_PARSE_SHARD_MAX=1`) are set by
`scripts/bootstrap/p3-targeted-stage2-build.shs` for targeted object rebuilds.

## Notes

- A diagnostic-only unwrap diag patch (`C:/dev/p3new/cgprobe/diag_patches/unwrap_diag.diff`) correlated with
  the parse AVs; it stays local and is not landed.
- Real fix: root-cause the child fault in the parse-shard child entry (`parse_shard_main.spl`) with a stage
  built from current source; revert the env flags once a stage3 shows zero child AVs on the CompilerDriver closure.
