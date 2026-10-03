# Streaming parse failure reason lost after local Result handling

Status: source fix proposed; native and system regression UNRUN.

Retained Windows evidence: `D:/dev/windows-release-7734-build-20261002/full-cli-streaming-optin-2`.
Producer `2f3d16fdfaaafcdb630361dd37ed62fe8cef171946b245fe88629b6e5d5f0384`,
source `7734f947be8ba9465d0ba312170681074e990587`: released 649 surfaces, then
last logged parse-start `src/app/devhub/auth.spl`; phase 2 failed with one
recorded error and no diagnostic payload. Exit 1, not a memory-cap termination.
The last parse-start does not prove an authored grammar defect in that file.

The existing owned parser-message capture (PR2213) is present. Streaming Err
handling only records the reason through CompileContext.add_error; its immediate
dump is disabled by default. The later orchestration accessor explicitly returns
empty text when diagnostic-array transport is unreadable. This explains a route
that can lose the reason, without proving which parser/scope/ownership error
occurred in the retained run.

The proposed fix emits the local Result reason and source path to stderr before
either recoverable-parse or fatal-invariant handling. It changes no parser verdict,
scope ownership, poison budget, error count, or collect-all policy. The aggregate
report can still repeat a reason when context transport succeeds.

Regression: `test/03_system/compiler/streaming_parse_failure_receipt_spec.spl`
invokes a source-matched pure-Simple native compiler once on a malformed explicit
entry, enables streaming, disables optional compile-error dumping, and requires
exit 1 plus the tagged source and actual type-annotation error on stderr.
Run only with external resource admission and genuine warm SCV authority; no seed
fallback, fabricated snapshot receipt, or automatic retry. This regression covers
the parser-error boundary, not an injected transient-owner failure.
The system regression also depends on entry-routing PR2262: explicit entries
under `test/` must reach the explicit-source collector instead of the production
import collector's test-path exclusion. This patch covers only the local
`parsed_result` Err boundary, not all compiler diagnostic transport.

No native invocation was performed while preparing this patch. The underlying
full-CLI failure remains unclassified until a source-local reason is observed.
Root review accepted the source delta only. Native execution, system regression,
and generated spec manual remain UNRUN; this is not release qualification.
