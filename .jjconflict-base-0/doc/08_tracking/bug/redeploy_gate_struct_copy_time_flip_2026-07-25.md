# redeploy gate: struct-copy-isolation flips 5→999 on IDENTICAL binaries across time

- **Date:** 2026-07-25
- **Lane:** redeploy gate (`scripts/check/cert/redeploy_gate/redeploy_gate.shs`), macOS stage4
- **Status:** open — deploy policy fell back to gate-parity (candidate = incumbent = 10/11)

## Observation (timeline, same fixture `struct_copy_isolation.spl`)
- 13:12-13:13: candidate built from `d5a6312d` gates **11/11**; struct-copy prints 5.
- 14:0x onward: the SAME deployed binary (mtime 13:12, unchanged) and EVERY fresh build
  (cherry tip, pure `d5a6312d` control, cold-cache rebuild) print **999** deterministically.
- Seed unchanged throughout (target/bootstrap/simple mtime 11:12, runtime archive 11:08 —
  both predate the passing run). Object cache wipe did not change the result.

## Analysis
999 is the interpreter lane's longstanding struct-copy aliasing parity bug; 5 is the
correct (JIT/compiled-lane) result. Identical binary + fixture flipping across time means
**execution-mode selection is environment-sensitive**: when JIT is available the fixture
passes; when JIT declines (observed elsewhere today: "JIT compilation failed, falling back
to interpreter: unresolved external symbol 'rt_text_cmp_any'"), the interpreter's aliasing
bug surfaces. Candidate suspects for the mode flip: runtime-symbol dylib probing state
(`target/bootstrap/deps/libsimple_runtime.dylib` 11:08 vs `target/bootstrap/` 03:29),
concurrent cargo/peer rebuilds mutating probed paths mid-day, or load-dependent JIT
thresholds. Not yet isolated.

## Impact
- Gate results are not comparable across time; 11/11 vs 10/11 can reflect environment,
  not binary quality. Today this blocked a deploy until parity policy was applied.

## Fix direction
1. Gate should PIN execution mode per fixture (force JIT and force interpreter as two
   separate checks) so environment can't silently switch lanes.
2. Root-fix the interpreter struct-copy aliasing (tracked in
   `interp_option_struct_semantics_macos_parity_2026-07-25.md`).
3. Root-cause the `rt_text_cmp_any` JIT symbol-resolution failure and its dependence on
   on-disk dylib state.
