# BuildRunner receipt collection

Collection binds a receipt to the transport's task name, attempt number, host
and immutable task digest before inspecting or transferring its output files.
Reusing a task name and attempt number does not authorize a receipt from another
manifest. Failed receipts with no outputs require the same binding.

The manager separately validates the full task/result contract and ownership
receipts. Successful collection alone does not establish compiler-tree reap or
admit a completed build. Darwin strict V4 remains unavailable until its complete
host authority is implemented and qualified.

Regression: `test/01_unit/app/bootstrap_builder/transport_identity_spec.spl`.
See the [bug record](../../08_tracking/bug/buildrunner_transport_task_identity_2026_10_29.md)
for execution status and diagnostic-runtime limitations.
