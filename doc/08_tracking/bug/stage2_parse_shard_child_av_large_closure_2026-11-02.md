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

## 2026-11-07: pure c56 GDB-server construction recurrence (cause unproved)

This is new observed evidence for this existing deferred record, not a new
P1 claim, a repair, or proof that the historical and current faults share a
cause. The severity and deferred status remain unchanged.

Evidence owner: `build/review/mcpgdb-pure-c56-server-attempt3/TERMINAL-REPORT.md`
and its hash-bound `shard-evidence-terminal` packet. Actual owner session
34713 ended with campaign exit 1 and compiler exit 124 at the enforced
1650-second row deadline. No server PE was produced. Canonical SCV admission
preceded worker selection at +827881 ms, then four parse shards over 183
selected paths at +836076 ms. No HIR, codegen, or link completion was observed.

- Shard 0/4, PID 19248, and shard 1/4, PID 12524, each exited
  -1073741819 (`0xC0000005`); dead-child cleanup reported `kill=false`.
- Shard 2/4, PID 21852, had an actual owned command line captured while live
  and remained active until the deadline. Shard 3/4 had no independently
  recorded terminal parse result before cleanup. Neither has a successful
  parse receipt in this run.
- Exactly 96 exclusive claims mapped uniquely to the 183 selected source
  paths, with zero unmapped markers. The dynamic claim windows were 16;
  ownership counts were 16/32/16/32. These are ownership boundaries, not
  parse completion, the last parsed file, or crash attribution.
- Runtime stderr also reported four rejected invalid-array handles, with
  value bits `0x0000025248a0e371`, `0x0000023c5b8c1fc1`,
  `0x00000194d375dab1`, and `0x000001ad15126131`. The wording
  "probable compiler/FFI ABI mismatch" is the runtime diagnostic, not an
  established diagnosis. Producing PID, file, and relation to either AV are
  unproved. No packed-value, `for`, generic-push, boxed-wide, or pending-defers
  cause is attributed by this observation.

The watchdog reported quiescence, no unexpected remaining PIDs, and peak RSS
4,153,032 KiB below the 8,000,000 KiB cap. This was not a recorded memory-cap
termination. Source/tool finalization passed: before and after input manifests
both had SHA256 `3405972738d6a6c2903873ac069e93eccd618d54d0e748d8d2b5560d06c2bd3a`.
The report records source b3c8708b, authority 80726, composition 2d1472, registry
present, and no source drift or fallback. The older record's successful parent
fallback must not be inherited as a result of this current run.

The actual pure compiler invoked `run src/app/cli/parse_shard_main.spl ...
--parse-fibers=2/4` as a construction worker. This was not execution of a native
GDB product. Native server protocol, tools, and deployment remain UNRUN; the
server and five source-coherent workers remain missing/unqualified. Caches,
raw stdout/stderr, claims, selection, terminal status, and owned argv are
retained for focused diagnosis. No additional compiler or test was launched
for this documentation update.
