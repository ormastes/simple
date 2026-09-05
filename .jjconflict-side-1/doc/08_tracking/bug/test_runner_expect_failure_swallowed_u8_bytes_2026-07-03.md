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

## Re-confirmed 2026-09-02, broader than originally scoped — NOT u8-specific

Reproduced with `bin/release/macos-arm64/simple` (self-hosted, "Simple Test
Runner v0.9.5"), invoking `simple test <one file>` directly (top-level
dispatch, not via `test_runner_new/test_runner_single.spl` as a subprocess).
Minimal 3-line repro, plain `i64`, no u8/audio anywhere:

```
use std.spec.{describe, it, expect}
describe "mixed":
    it "passes":
        expect(1).to_equal(1)
    it "fails":
        expect(1).to_equal(2)
    it "also passes":
        expect(2).to_equal(2)
```

`simple test <that file>` reports `Passed: 3, Failed: 0`, `[32mPASSED[0m (0ms)` —
the deliberately-wrong middle assertion is silently counted as a pass. A
single-`it` file with only `expect(1).to_equal(2)` reproduces the same way
(`Passed: 1, Failed: 0`). So the swallow is not specific to the wav spec's
shape, u8 matchers, or closures — a bare top-level `describe`/`it`/`expect`
mismatch is enough. `--clean` does not change the outcome.

**Side finding, filed as its own defect elsewhere in this batch and directly
implicated here:** the per-file result cache at `.simple/test-result-cache-rs.txt`
recorded these brand-new files as `passed=N failed=0` on their FIRST run (no
prior entry could have existed for a just-created path), and a *second*
invocation of the same failing file printed `Skipped 1 unchanged test(s)
(cached)` and kept reporting 0 failures — see
`doc/08_tracking/bug/test_manifest_invalidation_is_size_only_mtime_never_read_2026-08-17.md`
for the general cache-staleness defect this compounds with (though the FIRST
run's wrong 0-failure count is not a caching issue at all — it establishes the
wrong result that then gets cached).

**Important scope caveat:** the repo already carries an extensive contract
spec for this exact bug class,
`test/03_system/check/test_runner_single_example_failure_contract_spec.spl`,
but every one of its scenarios drives failure detection either by invoking
`src/app/test_runner_new/test_runner_single.spl` directly as a subprocess, or
by invoking `bin/simple test --no-session-daemon --assert-ran <fixture>` — a
different code path from the plain `simple test <file>` invocation used
above. Whether that spec's scenarios currently pass could not be established
in this session (running it would itself go through the same top-level `test`
dispatch whose reliability is in question, and the contract spec's own
`it`-level pass/fail reporting is exactly the mechanism just shown to be
unreliable on this binary — a passing report from it is not trustworthy
without independent confirmation, e.g. checking `process_run`'s captured
`stdout`/`code` values by hand rather than the wrapping spec's own verdict).
This record stays OPEN. The new minimal 3-line repro above should be the
first thing whoever picks this up re-runs after any fix, since it needs no
audio/u8/closure setup at all.
