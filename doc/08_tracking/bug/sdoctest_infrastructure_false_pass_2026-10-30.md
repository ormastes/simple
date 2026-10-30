# Expected-failure doctest accepted process infrastructure failure

Status: source reviewed; actual native process-launch regression verified.
Full semantic-control suite remains unqualified.

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

## Focused native evidence

The admitted attempt12 producer `1759a66577ca33191743401f77d712a2396debceb964ee283622a7744d92f8d1`
built the actual block-runner fixture (139 modules). The actual SCV source audit
matched both production runner and fixture to reviewed source `76b8939f67f`.
Evidence directory: `/tmp/simple-sdoctest-infrastructure-native12-20261030`.

One runtime execution verified both non-executable-child assertions: a real
mode-0600 file returned `Error` with and without `ShouldFail`, including provider
stderr `rt_process_run_timeout execvp: Permission denied`. This directly tests
the removed false-PASS branch rather than a compiler-selection refusal.

The complete five-case probe returned **8, not PASS**. Its positive semantic
control failed when the admitted build compiler was used as the child; a fully
qualified CLI was unavailable. Thus semantic negative/positive execution is
not established by this run, and there is no full application or five-case
suite PASS claim. The patch preserves the existing ordinary nonzero branch;
source review and the two actual launch-failure assertions are the scoped
repair evidence. Required broad runtime gates remain pending separately.
