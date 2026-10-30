# Expected-failure doctest accepted process infrastructure failure

Status: source-reviewed finding; candidate repair and real-process regression
await runtime qualification.

PR #5332 added a branch in `sdoctest/runner.spl` that reports Passed for a
`ShouldFail` block whenever exit status is -1 and stderr is nonempty without a
timeout substring. Stderr alone does not establish semantic example failure.
The existing following branch identifies -1 as launch/internal failure.

The actual POSIX provider in `runtime_process.c` normalizes a signaled process
to -1 and also normalizes execvp failure (127 with its provider diagnostic) to
-1. Consequently a pinned but non-executable child can turn an unrun doctest
into PASS. This is separate from whether the compiler selector's hash matches.

The candidate removes only the abnormal-process PASS branch. Infrastructure
failure remains Error irrespective of `ShouldFail`; normally completed
nonzero semantic failures retain the existing expected-failure behavior.

`sdoctest_infrastructure_native_probe.spl` calls the real block runner against
a harness-provided non-executable file, with and without `ShouldFail`, then
against an admitted Simple CLI executing actual negative and positive source.
The harness must verify the fixture exists without execute permissions and
pin the real CLI's admission/hash. A recording shell is not semantic compiler
evidence. Runtime results and required gates remain pending; no native PASS is
claimed by this source change.
