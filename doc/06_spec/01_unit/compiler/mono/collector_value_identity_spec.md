# Generic collector retained-value regression

Executable: `test/01_unit/compiler/mono/collector_value_identity_spec.spl`. Native fixture: `test/fixtures/compiler/native_mono_collector_values/main.spl`.

**AUTHORED_UNRUN** in the G1 port. No interpreter, compiler, native build, link or runtime evidence is claimed.

## Unit scenarios

1. Parse and lower real generic and ordinary declarations, then independently reconstruct every `SymbolId` dictionary key. Collect in both retained-body and archive-request modes. Assert the generic template recipe/module/binder, retained-body mode behavior, ordinary symbol registration and complete symbol-name registration.
2. Parse a real generic inherent impl and verify its `Box__read` template recipe and owner binder remain registered.

The native fixture checks integer and text generic results, a generic owner method, and an ordinary call. It returns nonzero on incorrect values and prints `PASS generic collector standalone owner ordinary` only after every check passes. Native execution is required to qualify aggregate-key behavior; interpreter-only success would not qualify this regression.

## Port boundary

Original source candidate: `f392d4f24996becb7312b407e6f2b1dca2c47524`. G1 lacks the separate `class_static_template_v1`/`collect_class_static_templates_v1` feature used by the original Factory scenario. This port preserves supported impl-owner coverage and omits only that independent static-feature scenario; it does not claim static-template coverage or add its implementation. The collector fix changes only function-value traversal/extraction and bounded diagnostics, preserving all surrounding G1 registration behavior.
