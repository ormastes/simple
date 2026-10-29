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
