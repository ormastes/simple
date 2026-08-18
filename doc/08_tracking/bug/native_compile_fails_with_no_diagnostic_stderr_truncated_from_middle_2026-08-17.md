# `native_compile` can fail a unit with ZERO diagnostic; the truncator drops the middle of stderr

- **Filed:** 2026-08-17
- **Status:** Defect 1 **FIXED** (re-verified 2026-08-17, see *Re-verification* at the
  bottom). Defect 2 mitigated; the head+tail excerpt policy itself stays OPEN.
- **Lane:** `native-build`, `native_compile` stage (step 5/6).

## Observed

Native-building `test/fixtures/native_trailing_default_param/main.spl`, the
`main` unit failed at `native_compile` with no explanatory text anywhere:

```
[build] native_compile 1/2 step 5/6 test.fixtures.native_trailing_default_param.main

===== build outcome summary =====
OK=1
ERROR=1
CRASHED=0
TERMINATED=0
TIMEOUT=0
NOT_RUN=0
ERROR: 1 unit(s)
  - test.fixtures.native_trailing_default_param.main
===== end build outcome summary =====

error: build failed: 1 failed, 0 unverified, 0 not run, 1 ok of 2 unit(s)
```

A full-log scan for `^error|error:` returned only the summary lines above. The
unit is marked ERROR and the reason does not exist in the output.

## Defect 1 — an unattributable failure

`ERROR=1` with no message is unactionable. The outcome summary faithfully
reports *that* a unit failed and structurally cannot report *why*. Every
consumer of this build — a human, the pre-push guard, CI — is left to guess.

## Defect 2 — the truncator drops the MIDDLE, and says so

```
!!!!!! NATIVE-BUILD STDERR TRUNCATED !!!!!!
[native-build] TRUNCATED: 55884 of 67884 bytes of worker stderr were dropped from the MIDDLE.
[native-build] Raw head+tail below is INCOMPLETE -- counting over it is unreliable.
[native-build] BEGIN PRESERVED DIAGNOSTICS (27 line(s), from the full stream)
```

**82% of the worker's stderr was discarded**, and the surviving
"preserved diagnostics" window contained only unrelated
`compiler_cross_module_private_symbol_collision` warnings about `bytes_to_text`
and `compile_native` — not the failure.

Head-plus-tail is precisely the wrong retention policy for a compiler: the head
is startup warnings, the tail is the summary, and **the actual error is in the
middle**. The truncator is honest about what it did, which is good, but honesty
about destroying the evidence does not restore it.

This is the class of defect that cost three lanes a day on the stage-3
investigation: a build that fails with no attributable cause forces every
investigator to re-derive the failure from scratch, and invites confident wrong
diagnoses. The `undefined variable Widget` message in
`native_build_static_method_owner_unresolved_2026-08-17.md` was itself recovered
from truncated stderr by a lane that got lucky.

## Required behaviour

1. Retention must be **diagnostic-priority, not positional**: any line matching
   an error/diagnostic shape must survive truncation ahead of any warning,
   regardless of where it sits in the stream. If a budget must be enforced, drop
   repeated warnings first — the two warnings that *were* preserved here are
   emitted many times and carry almost no information.
2. A unit marked `ERROR` in the outcome summary must carry a reason string. A
   summary that can report a failure it cannot explain should be treated as a
   bug in the summary, not as a property of the build.
3. Truncation must never be able to remove the last diagnostic that explains a
   non-zero exit.

## Independent reproduction, 2026-08-17 (merged in from a duplicate row)

A separate lane hit this on a fresh **unwrapped** run of
`scripts/check/check-native-trailing-default-param.shs` (no `timeout` wrapper —
an earlier 10-minute wrapper had manufactured a false rc=143 in this campaign;
rc read into a variable on the line after the command, never through a pipe).
rc=1, verdict line verbatim:

```
FAIL — native-build failed to compile the fixture (exit 1, log saved to /tmp/check-native-trailing-default-param.last.log)
```

That log carries the truncation banner at line 1795 and again at line 2002
(`[stderr truncated by native-build entry: 55780 bytes omitted from the
middle]`), with the bare `ERROR=1` at line 1782 and no accompanying diagnostic.

Two things this adds to the observations above:

- **It is deterministic, not load noise.** A second lane running the same guard
  concurrently from a different worktree
  (`/mnt/data/tmp/claude-1000/wt-llvmcodegen`) produced the byte-identical
  verdict line and rc=1 — an unplanned independent replication.
- **The byte counts drift slightly between runs** — `55780 of 67780` here
  versus `55884 of 67884` in the original observation above — while the
  discarded fraction stays at ~82%. The drift is consistent with the discarded
  region containing run-varying text, i.e. exactly the text worth keeping.

This also corroborates point 1 of *Required behaviour*: in the reproduction the
retained head is spent on repeated
`compiler_cross_module_private_symbol_collision` warnings (lines 1563-1574),
which then appear **again** in the retained tail (lines 1798-1809). The
surviving 18% is partly duplicated warning noise, so the effective attribution
yield is lower still than the byte ratio suggests.

## Note on interaction with the pre-push guard

`scripts/check/check-native-trailing-default-param.shs` additionally applies its
own `tail -n 60` on failure, compounding this: the guard's visible output can
consist entirely of trace noise while the cause is discarded twice over.

## Root cause, measured 2026-08-17 — Defect 1 is NOT truncation

**Mechanism (b), not (a): the diagnostic was never produced in the output.**
Truncation is incidental to Defect 1.

Traced by reading the producer/consumer pair, then confirmed by direct
execution:

- `driver_native_record_module_failure`
  (`src/compiler/80.driver/driver_aot_native_output.spl:93-99`) DOES capture the
  compiler's own message: all three call sites (lines 658, 663, 692 — the
  collect-error, the single-module `Err(e)`, and every `build_result.errors`
  entry) pass it as `detail`, stored in `BuildUnitOutcome.diagnostics`.
- `BuildUnitOutcome` declares `diagnostics: text  # non-empty for ERROR; the
  compiler's own message`.
- **Nothing ever read it back out.** `BuildOutcomeSet.summary()` emitted
  `  - {path}` and nothing else; `verdict()` lists paths only. The field was
  written by every failure path and consumed by none.

So no retention policy in `eprint_bounded` could have preserved the message:
it was never written to any stream. The 82%-discard was real and is a separate
defect, but it is not why `ERROR=1` had no reason.

### Ablation (both arms verbatim, seed binary, unwrapped, rc read into a variable)

Same probe, same fixture (one ERROR unit with a recorded diagnostic, one with an
empty one), only `build_outcome.spl` swapped.

Control — `build_outcome.spl` at `HEAD` (pre-fix):

```
ERROR: 2 unit(s)
  - mod.alpha
  - mod.beta
===== end build outcome summary =====
```
`rc=0`, `grep -c "undefined variable Widget" out.txt` -> `0`.

Fixed:

```
ERROR: 2 unit(s)
  - mod.alpha
      reason: undefined variable Widget at alpha.spl:12
  - mod.beta
      reason: (none recorded — BUG in the producer: a non-OK unit must carry a diagnostic)
===== end build outcome summary =====
```

The guard's own fail-path was ablated too — with the fix reverted in the working
tree it emits, verbatim:

```
FAIL — a unit reported ERROR did not print its recorded diagnostic; summary() is structurally unable to say why a unit failed (see doc/08_tracking/bug/native_compile_fails_with_no_diagnostic_stderr_truncated_from_middle_2026-08-17.md)
```
rc=1. With the fix applied:
```
PASS — 4 invariant(s) checked, non-OK units carry printed reasons (ablated against pre-fix rev e89f0c6f94a: control printed the path with no reason)
```
rc=0.

## Fixes applied

1. `src/compiler/80.driver/driver_build/build_outcome.spl` —
   `BuildOutcomeSet.summary()` now emits an indented `reason:` block under every
   non-OK path, via a new `reason_block_for()`. A non-OK unit with an EMPTY
   diagnostic prints `(none recorded — BUG in the producer: ...)` rather than
   nothing: silence is indistinguishable from "no failure" to every reader, so
   the absence is stated. This satisfies *Required behaviour* 2.
2. `src/app/cli/native_build_main.spl` — `eprint_bounded()` now spills the FULL
   stderr to `${TMPDIR:-/tmp}/native-build-stderr-<pid>.log` and prints the path
   before truncating, so truncation can no longer make evidence unrecoverable
   (*Required behaviour* 3). A failed spill is stated, never silent. The
   existing diagnostic-priority `PRESERVED DIAGNOSTICS` block (already present,
   `native_build_collect_diagnostics`) is retained unchanged — it addresses
   *Required behaviour* 1, and this row's observation that it preserved only
   warnings is now explained: there was no error line in the stream to preserve.
3. Guard: `scripts/check/check-build-outcome-reason-attribution.shs`. Runs in
   seconds (build_outcome.spl has zero `use` lines, so it is copied to a scratch
   dir and driven by a probe); `--selftest` is fatal and runs on EVERY
   invocation, ablating against the newest committed pre-fix revision found by
   walking history (no hardcoded sha). Treats rc=143/137 as UNVERIFIED (exit 2),
   never as a pass or a fail.

## Relation to `rt_fork_parent_wait_bounded` — NOT a shared root

Checked, and the answer is no, for Defect 1 at least:
`stage4_test_runner_pipe_capture_truncation_rt_fork_2026-07-20.md` describes a
read loop exiting early while capturing a CHILD's pipes. Defect 1 crosses no
process boundary at all — the driver formats and prints its own summary in its
own process, and the loss is a struct field that no code path read. Defect 2's
cap is likewise an explicit Simple-level constant (`OUTPUT_LIMIT = 12000` in
`native_build_main.spl`), not a short read. Whether the worker's stderr capture
*additionally* loses bytes in `rt_fork_parent_wait_bounded` is untested here and
is left as an open, separate question — asserting a shared root would be
unsupported.

## Status

Defect 1: FIXED and ablated. Defect 2: mitigated (full spill to a named file);
the head+tail excerpt policy itself is unchanged and remains open as a
cosmetic-priority follow-up now that no evidence is destroyed by it.

## Re-verification 2026-08-17 (independent lane)

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (the Rust bootstrap seed).

```
$ timeout 600 sh scripts/check/check-build-outcome-reason-attribution.shs
PASS — 4 invariant(s) checked, non-OK units carry printed reasons (ablated against pre-fix rev e89f0c6f94a: control printed the path with no reason)
```

Defect 1 confirmed fixed and gated. No change made to this row's code.
