# Lossless diagnostic response

Source: `test/01_unit/compiler/driver/source_analysis_wire_v1_spec.spl`.

Serialize a real DiagnosticV1 containing cross-file labels, notes/help, nested child, macro trace and empty replacement text. Parse the SDN envelope and inspect its explicitly named canonical JSON payload. Reject excessive recursive depth before rendering. Preserve the distinction between completed empty diagnostics and failed collection.

Status: **NOT_RUN**. This is an authored obligation manual, not generated execution evidence. Requires an admitted self-hosted compiler and full original diagnostic producer capture. Runtime regeneration, semantic behavior, cancellation, startup/latency/RSS and release admission remain pending.
