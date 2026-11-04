# Nested Some loses declared Value optional payload context

2026-10-16. Source annotation candidate only; native verification UNRUN; DB
reconciliation pending. Recovery base67ba74d9acbaa998d5efcb3c162bf61a63f839d0.

The retained main attempt lowered the genuine backend_types owner (43functions)
but reported three qualified Value.Option/Result payload type mismatches in
existing some/ok/err factories. Module completion does not mean this owner
passed. These errors are independent of imported constructor receiver failures.

The source candidate binds Some(value) and nil to explicit Value? locals before
passing the same fields to the original constructors. Presence, wrapped Value,
nil placement and argument order are preserved. No unwrap, fallback payload,
enum alias, changed runtime identity or optional representation cast is used.
This is not proof the annotation repair works on the baked producer: its exact
MIR validation and real Some/nil payload controls remain necessary.

This source belongs to the same bounded constructor feature; do not reset the
three-cycle budget or infer a successful full compiler from a small probe.

The original some/none/ok/err methods now delegate those typed fields to genuine top-level option/result factories beside the same declaration. The probe calls these actual functions with Some/nil combinations, not imported static methods or a mirrored constructor. Payload presence and contained Value are checked; all controls remain UNRUN.

## Verification pending (n88_b, 2026-11-04)

Source repair/workaround is pinned by `bin/simple.exe test test/01_unit/compiler/80.driver/n88b_native_workaround_shapes_spec.spl` (8/8 pass on the seed).
Native repro fixture: `test/fixtures/compiler/n88b_native_producer_idioms_native.spl` (+ `.expected`); covers the SOME_ line (typed optional payload). Source now lives in src/compiler/00.common/runtime_value_v1.spl (moved from backend_types.spl:233).

Stage3 repro (expected: no diff output, exit 0; then remove the matching `@workaround` tags):

```
bin/simple native-build --entry test/fixtures/compiler/n88b_native_producer_idioms_native.spl -o build/n88b_idioms.exe && build/n88b_idioms.exe | diff - test/fixtures/compiler/n88b_native_producer_idioms_native.spl.expected
```
