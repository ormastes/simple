# Test runner: expect() failure swallowed in wav_encode_spec (u8 byte-array case)

- **Date:** 2026-07-03
- **Severity:** P1 (trust — second greenwash mode, distinct from the fixed summary-sum bug)
- **Status:** open, needs minimal repro

## Observed (by P0c encoder agent, worktree agent-a170cd9758e16d60e)

Sabotaging an assertion in `test/01_unit/lib/common/audio/wav_encode_spec.spl`
(`expect(bytes[44]).to_equal(99u8)` where the real value is `0`) still produced
`PASSED`, `Passed: 6, Failed: 0` under `bin/simple test` — with the
summary-sum fix (test_runner_interpreter_file_summary_greenwash_2026-07-03,
landed same day) already present in the tree.

## Not reproducible with the trivial case

`expect(1).to_equal(2)` in a fresh spec correctly reports `Failed: 1` (test)
and `1 example, 1 failure` (run) on the same binary — verified 2026-07-03.
So the swallow is specific to something in the wav spec's shape. Suspects:

1. `u8`-typed matcher comparison (`bytes[44]` u8 vs `99u8` literal) — matcher
   may compare after a lossy/mismatched coercion or throw-and-swallow.
2. The failure flag being lost via the closure member-path store bug
   ([interp_member_path_store_lost_in_bdd_closure_2026-07-03]) if the spec
   builds `bytes` through captured state.
3. Helper-fn indirection between `it` and the expect.

## Next step

Minimal repro by bisecting the wav spec's failing-assert shape: u8 literal vs
i64, direct buffer vs helper-returned buffer, inside/outside closure capture.
Fix in the matcher/runner, add the shape to the greenwash regression contract
spec (test_runner_single_example_failure_contract_spec.spl).

## Workaround (used for the P0c evidence)

`bin/simple run` harness with raw print-and-compare assertions; per-describe
output lines remain trustworthy.
