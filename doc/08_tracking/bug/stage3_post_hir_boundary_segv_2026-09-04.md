# Stage 3 post-HIR boundary SIGSEGV (2026-09-04)

## Status

Open. A clean, provenance-admitted Apple Silicon Stage 2 compiler completed all
771 HIR modules and then exited from signal 11 before the former
`phase3:hir_typecheck:done` marker. This is later than the historical streaming
owner crash and does not identify the same source owner.

## Retained evidence

- Resume log: `build/caret-bootstrap-current.stage3-resume.retry3.log`
- Native-build log:
  `build/caret-bootstrap-current/logs/aarch64-apple-darwin/stage3-native-build.log`
- Status receipt:
  `build/caret-bootstrap-current/stage3/aarch64-apple-darwin/stage3-native-build-status.env`
- Status classification: `shell-signal-exit`, `signal-number-11`
- Long pre-frontier sample: `/tmp/caret-stage3-retry3.sample.txt`; it reaches
  the already-tracked transient-heap promotion scan and later makes progress,
  so that scan was not the crash.

The final retained progress line is HIR module 771 of 771. macOS emitted no
DiagnosticReport. The old logging therefore left the cache summary, shard gate,
poison-owner read, context commit, layout validation, and owner reclaim as one
indistinguishable crash region.

## Diagnostic repair

`driver_hir_pipeline_lowering.spl` now emits ordered phase markers around each
of those boundaries. The modern SSpec
`stage3_post_hir_boundary_diagnostics_spec.spl` requires every marker and their
execution order, preventing the blind region from returning during refactors.

## Next bounded action

After rebuilding and re-admitting Stage 2 for this source identity, run Stage 3
once with `SIMPLE_NO_STUB_FALLBACK=1`. The last emitted marker selects the exact
operation to repair. Do not replay the uninstrumented receipt or attribute the
fault to a boundary that the retained evidence cannot distinguish.
