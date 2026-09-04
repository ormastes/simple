# Stage 3 post-HIR boundary SIGSEGV (2026-09-04)

## Status

Open. A clean, provenance-admitted Apple Silicon Stage 2 compiler completed all
771 HIR modules and then exited from signal 11 before the former
`phase3:hir_typecheck:done` marker. This is later than the historical streaming
owner crash and does not identify the same source owner.

The first instrumented replay completed the HIR loop, cache summary, shard
gate, poison-owner read, and HIR context commit. It emitted
`phase3:hir:layout-validation:start` and then exited from signal 11 without
`phase3:hir:layout-validation:done`. The fault is therefore inside the
post-HIR validation dispatcher, not context commit or owner reclaim.

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
The dispatcher now also brackets value-struct, layer-equality, effect, aspect,
and weave passes independently; the same spec requires that ordered evidence.

The second admitted replay emitted `phase3:validation:value-struct:start`, then
exited from signal 11 without `phase3:validation:value-struct:done`. The selected
repair introduces the concrete `ValueStructLayoutErrors` owner and
`validate_value_struct_layouts_into(...)`. The Stage 3 dispatcher fills and
reads that owner instead of consuming an aggregate `[text]` function return;
the original value-returning function remains as a compatibility wrapper for
focused callers and unit specs. This preserves validation rather than skipping
the failing pass.

The final permitted replay for this session used a newly rebuilt, admitted
Stage 2 compiler containing that owner-result repair. It did not reach the
validation dispatcher: after HIR module 1 of 771 it diagnosed two ambiguous
explicit callable dependencies named `Option`, from
`compiler.backend.backend.env` and
`compiler.backend.backend.interpreter`, while declaring
`src/compiler/driver/driver.spl`. The diagnostic was emitted successfully, but
the process then exited with signal 11 instead of returning a normal compile
failure. This is a distinct earlier frontier; consequently this replay neither
confirms nor disproves the value-layout repair.

Final-replay evidence:

- Resume transcript:
  `build/caret-bootstrap-current.stage3-value-layout-owner.log`
- Native log and status receipt are the paths listed above.
- Status: `shell_exit_status=139`, `signal_identity=signal-number-11`
- Last completed marker: `phase3:hir:declare:done` for
  `src/compiler/driver/driver.spl`
- Fatal diagnostics: two ambiguous `Option` dependencies, followed by the
  signal exit.

## Next bounded action

In a fresh bounded session, first remove or qualify the two ambiguous `Option`
callable dependencies and inspect the HIR fatal-diagnostic cleanup path that
turns a reported compile error into SIGSEGV. Rebuild and re-admit Stage 2, then
run Stage 3 once with `SIMPLE_NO_STUB_FALLBACK=1`. Do not run a fourth replay in
the current session: the mandatory three-cycle convergence cap has been
reached. The value-layout owner-result repair still needs a replay that reaches
`phase3:validation:value-struct:done`.
