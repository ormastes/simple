# stage2_parse_shard_child_av_large_closure_2026-11-02

- Status: **deferred-by-design** (phase-split parse shards contradict the one-process-per-file design; AV not patched; see Design decision)
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

## Design decision (2026-11-03)

User design: ONE PROCESS PER FILE (each file parse -> HIR -> MIR -> obj in one process, like cc1); no
phase-split shard children. The parse-shard child is exactly the phase-split model: `native_build_main.spl`
(`run_parse_shards`, ~line 787) spawns `simple run src/app/cli/parse_shard_main.spl --parse-shard=i/n`, a slim
parse-only process that only warms the front-end parse cache ("sharding is a cache warm-up and can never
change the build's output"; it never loads HIR/MIR/backend). It is NOT a per-file pipeline process.

The shard path is still ON by default in code (`native_build_parse_shard_count` returns >0 unless
`SIMPLE_PARSE_SHARDING=0`, `--collection-profile`, no frontend cache, or streaming surfaces; cap 1 only in
interpret mode). Phase-3 targeted builds already disable it via `p3-targeted-stage2-build.shs`.

Resolution: the access violation is not root-caused or patched here. Design todo: retire the parse-shard
children (default `SIMPLE_PARSE_SHARDING` to off, then delete `parse_shard_main.spl`, `parse_shard_queue` and the
spawn path) in favour of the per-file pipeline; the in-process parse fallback is already correct. Keep the
env-flag workaround until then. No code changed, no seed/stage2 rebuild.
