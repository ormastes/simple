# Canonical snapshot Check dispatch

Source: `test/01_unit/compiler/driver/source_analysis_dispatch_v1_spec.spl`.

Invoke check_snapshot_set_v1 against a clean overlay over invalid disk and an invalid overlay over valid disk. Require completed structured results, exact overlay dependency digest and original diagnostic file/span after compiler session teardown. Load an imported module absent on disk from the overlay set. Reject environment mismatch before compilation. Check an original LOG001 parser warning survives a successful Check.

Status: **NOT_RUN**. This is an authored obligation manual, not generated execution evidence. Requires an admitted self-hosted compiler and full original diagnostic producer capture. Runtime regeneration, semantic behavior, cancellation, startup/latency/RSS and release admission remain pending.
