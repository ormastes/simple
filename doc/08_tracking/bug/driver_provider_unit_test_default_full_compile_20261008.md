# Driver provider unit test invokes a whole-project compile

Status: landed upstream repair applied locally; alternative focused seed scenario passed, with provenance limits. Upstream variant runtime verification remains separate.

The Phase 1 `driver_provider_v1_spec.spl` lifecycle scenario creates a session
with default JIT options and no input paths, then expects a failed compilation.
The live retained seed process 22916 started on 2026-10-07 and had consumed
over 92,000 CPU seconds when inspected on 2026-10-08. Its bounded log shows
progress through a 5,144-source parse. This is evidence of unintended broad
test work, not proof of an infinite loop.

The initially authored local scenario supplied a single absent `.spl` input in Interpret mode.
The source loader treats this as an explicit entry and rejects zero collected
entry sources before bulk project parsing. The test still exercises the real
provider request, failed compile result, diagnostic count, busy session,
already-run request, result release, request release and session release.
No provider result or diagnostic is mocked and no assertion is removed.

Verify the exact changed scenario under the bootstrap seed and pure-Simple
test paths. Require the real failure diagnostic and complete provider lifetime
assertions; confirm the absent path is absent before execution. Preserve the
old live attempt and its evidence separately. This source change alone does
not terminate that attempt or establish a timing improvement.

## Focused verification evidence

The first focused attempt timed out during imports without a test verdict.
The corrected overlay attempt executed the changed scenario successfully:
one example, one passed, zero failed/skipped/dropped, child exit 0 in
59.495 seconds. Its intentional missing-input compile failed during source
loading in 23 ms, then all provider lifecycle assertions passed.
Evidence: `build/phase1-terminal-evidence-recovery/provider-focused-overlay2`.

The outer harness exited 1 because its provenance checker rejected 115
warning-location paths. The retained trace contains 1,173 actual read records
with no reads from `C:/dev/simple/src`, and 5,384 resolver records including
both intended provider modules. Warning display paths and actual reads must
be reviewed separately; this result is a functional scenario PASS, not yet
full namespace qualification. No matched performance improvement or
pure-Simple test PASS is claimed.

The provenance follow-up found that all 115 warning locations appeared before
the instrumented resolver/read records. The seed's pipeline loader also has
uninstrumented reads, so absence from the read trace cannot rule out early
workspace reads. Preserve the outer harness failure until that boundary is
qualified; do not relabel it from the functional test result alone.

## Upstream overlap

Fetched `release/1.0` at `340c3106bdb946a03d85bcab655125e5a73fc481`
already contains commit `06bc8aef74a5c7ed165f3bc811e29d6d38de1414`,
which supplies an explicit invalid source to the same lifecycle scenario.
It retains the default compile mode. Source review confirmed its `test/` input
bypasses bootstrap defaults and does not enable the bulk `src/` scan. It solves
the original broad-compilation bug without needing the local alternative.

The owned local test was reconciled to that exact upstream blob
`f7c87084d74f3bf041680c4a4cc82be147dac4a5`. No duplicate PR was opened.
The passing run above exercised the earlier Interpret/absent-path variant,
not the upstream malformed-source variant; do not transfer the PASS between
them. Active bootstrap source holders and unrelated dirty files were unchanged.
Comparison: `build/phase1-terminal-evidence-recovery/provider-focused-overlay2/REMOTE-FIX-COMPARISON.md`.
