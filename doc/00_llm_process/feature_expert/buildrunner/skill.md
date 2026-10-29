# BuildRunner

The manager owns task admission and publication; transport collects worker
receipts and isolated outputs. `builder_transport_collect_v1` must bind all
four identity fields (task, attempt, host, immutable digest) before output
handling, including failure receipts without outputs. The manager's subsequent
validation does not replace this collection boundary.

Guide: [receipt collection](../../../07_guide/tooling/buildrunner_collection_identity.md).
Regression: `test/01_unit/app/bootstrap_builder/transport_identity_spec.spl`.
An executed filesystem regression is not live process or strict V4 evidence.

The Hello fixture declares a native executable only and pins one-binary mode
in argv and versioned cache identity. Darwin callers supply SDKROOT and
MACOSX_DEPLOYMENT_TARGET; the worker retains them in its bound snapshot. See
[Hello prerequisites](../../../07_guide/tooling/buildrunner_stage_trace.md#native-hello-fixture-prerequisites).

Frozen P2 loses the imported database session receiver after Result-match and
optional bang-unwrap. Keep the explicit BuildRunnerDatabaseSessionV1 binding
until a new producer passes the unannotated native probe. Settlement and finish
are ownership gates, never optional diagnostics. See
[tracked inference boundary](../../../08_tracking/bug/buildrunner_database_match_unwrap_owner_2026_10_29.md).

## Live Linux containment evidence (2026-10-29)

The cgroup owner now has live setsid-descendant retirement and kernel OOM
fixtures. Run `scripts/check/check-linux-capacity-containment.shs` only with an
already-delegated isolated memory controller; missing prerequisites are errors.
Native C evidence remains distinct from the authored, unexecuted SSpec and full
BuildRunner qualification. See `doc/08_tracking/bug/buildrunner_linux_containment_evidence_2026_10_29.md`.

The live driver is registered as the bootstrap-tier automated
`linux-capacity-containment` gate. Its delegated Linux prerequisites stay
explicit; do not run it as a generic push-tier check or convert refusal to PASS.

### Linux native archiver preflight (2026-10-29)

Canonical bootstrap now checks the strict native owner's working LLVM archiver
before pure-stage source compilation on Linux. Seed-only preparation is separate;
GNU ar or AR overrides do not satisfy this check. Candidate ordering and broken
executable refusal are covered by `preflight-authority-milestone-test.shs`.
This is availability evidence, not tool-byte authority or Stage2 admission.
See [failure evidence](../../../08_tracking/bug/bootstrap_linux_archiver_late_failure_2026_10_29.md)
and [native staging](../../../07_guide/tooling/bootstrap_native_staging.md).

### Sanity memory reserve preservation (2026-10-30)

The canonical sanity scrub preserves an explicitly configured positive canonical
i64 `SIMPLE_BUILD_MEMORY_RESERVE_BYTES`; absence retains the compiler default,
and malformed values refuse before candidate execution. This does not change
hard memory enforcement or admit a previously rejected compiler. See
[reserve scrub evidence](../../../08_tracking/bug/bootstrap_sanity_memory_reserve_scrub_2026_10_30.md).

## Cranelift rejected-call publication (2026-10-30)

A void call legitimately returns handle zero; do not use that value alone as an
error test. The Rust provider retains declaration/import/direct-call failures
per live module and refuses function completion and object/JIT publication.
Free/reset clear owned failures. Isolated provider evidence is separate from
new compiler qualification. See
[refusal propagation](../../../08_tracking/bug/cranelift_rejected_call_publication_2026_10_30.md).

## Panic call ABI (2026-10-30)

Generated one-message panic calls must split the evaluated text into raw bytes
and byte length at MirBuilder.emit_call. Keep Abort and explicit two-argument
calls intact. A successful native build can still contain logged rejected
declarations; inspect those diagnostics before qualification. See
[panic ABI evidence](../../../08_tracking/bug/cranelift_panic_call_abi_conflict_2026_10_30.md).

The a52 producer's four native panic controls passed with clean compiler
diagnostics, including runtime-concatenated text evaluated once and the cast's
intended panic. Its separate full CLI matrix exceeded the enforced RSS cap;
native SSpec/docgen and complete BuildRunner admission are not implied.

### Frontend core RTI owner alias (2026-10-30)

The native SSpec runner exposed mixed `compiler.core.types` /
`compiler.frontend.core.types` declaration ownership. Shared HIR owner normalization
now folds the loader alias; RTI mixed-provider rejection remains intact. Focused
seed red/green tests pass; newly matched native runner validation is pending.
See `doc/08_tracking/bug/rti_frontend_core_alias_owner_2026_10_30.md`.
