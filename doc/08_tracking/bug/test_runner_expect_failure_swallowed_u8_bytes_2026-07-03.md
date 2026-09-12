# Test runner: expect() failure swallowed in wav_encode_spec (u8 byte-array case)

- **Date:** 2026-07-03
- **Severity:** P1 (trust — second greenwash mode, distinct from the fixed summary-sum bug)
- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
