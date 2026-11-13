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

## 2026-11-13: Windows diag-phase4 lint_entry recurrence + parent hang (hang fixed, AV open)

New occurrence, frozen Phase 2 compiler (`19c5aea975e`, Windows llvm-mingw UCRT)
native-building `src/app/cli/lint_entry.spl` (362 closure modules, 2 parse
shards, `split=static`, `--parse-fibers`) from source tree `4b7375e435a`
(log: `/c/dev/wt-lane2/build/diag-phase4/m_lint/build.log`):

- Shard 0/2, PID 22644, exited `-1073741819` (0xC0000005).
- Shard 1/2, PID 7880, stayed alive; the parent printed nothing for ~85 min
  and was killed by hand (shard 1 then reported `exit=143`). The same
  surviving-sibling shape appeared on 2026-11-07 (shard 2/4 live to the
  deadline).

AV status: the source tree already carried `f07a5101d3e` (`reset_all_pools()`
before `module_tldr_companion_view_sections_v1` in
`driver_parse_shard_entry.spl`, PR #8700), yet the child still faulted. Not
established: whether the `run src/app/cli/parse_shard_main.spl` child executed
that source copy of the driver or the frozen binary's compiled-in 19c5 driver
(which predates the fix). No symbolized stack for this run; root cause stays
open. Re-check on a compiler built from a tree containing `f07a5101d3e`.

Parent hang root cause and fix: the frozen 19c5 parent waited its shards one
after another with the build timeout (default 6 h, `DEFAULT_TIMEOUT_MS`), and
even the current shared-deadline reap (`parse_shard_reap_v1`) did nothing on a
peer's death. Now a shard that dies bounds its live siblings by
`SIMPLE_PARSE_SHARD_DEATH_GRACE_MS` (default 300000; 0 = old behaviour); they
are then killed as TIMEOUT and the real build parses the remainder in process
(shard output is per-module cache entries, so no finished work is lost). The
reap loop also sign-restores `process_wait` statuses so a zero-extended -2 is
never recorded as an exit of a live child. Spec:
`test/01_unit/app/cli/shard_worker_reap_spec.spl` ("parse shard death bounds
live siblings").
## 2026-11-13 recurrence: a live shard spins instead of crashing (devhub, frozen Phase 2)

Phase 4 diagnostic: `native-build --entry src/app/devhub/main.spl` (LLVM backend, 300-file closure,
`SIMPLE_NATIVE_BUILD_THREADS=2`) with the frozen Windows Phase 2 binary
`C:/dev/wt-lane2/build/diag-phase4/phase2.exe`, source tree `wt-dh1` at `b7a91519cf4`.
The frozen parent predates the sibling-death bound above.

- Try 1: the log stopped after `source_closure done=300/300` and printed only
  `[parse-shard] child alive pid=21964` and `pid=31616`.
  Neither child crashed or finished, and the build hit `timeout 10800` (rc=124, 10801 s).
- Try 3: same shape. Shard `--parse-fibers=0/2` (pid 30604) used 5,319 s of CPU at 387 MB working set,
  with no log output from 21:52 to 23:21 KST. Both processes were killed by hand.
- Try 2: same env, `timeout 1800`. This time the shards did not hang.
  The build reached `native_compile` 9/150 by 444 s and then hit the 30-minute cap.
- In the earlier n_devhub run on the same binary, both children died with 0xC0000005 and the parent continued.
  That is the original AV symptom.
  So the frozen binary's parse shards on this closure fail in two ways, nondeterministically:
  an access violation, or an unbounded spin.
  A spinning child never dies, so the sibling-death bound in #8937 would not fire either.
  The parent only gets past it at the build timeout.
- Workaround applied: `SIMPLE_PARSE_SHARDING=0 SIMPLE_FILE_FIBERS=0`.
