# KPF Worker-Wire Projection — 2026-09-03

## Result

The canonical KPF schema compiler now emits a deterministic package-specific
worker-wire module. It binds worker dispatch to the canonical schema digest and
dense interface/operation slots without changing the common native ABI.

## Contract

- Fixed 112-byte envelope prefix and 4 MiB V1 frame ceiling.
- Exact magic, wire version, header size, schema digest, and reserved-zero validation.
- Overflow-safe payload bounds using subtraction after offset validation.
- Generated interface/operation slot validation and required-operation policy.
- Reordered equivalent schemas produce byte-identical projections.

## Evidence

- `test/01_unit/tool/kernel_plugin_schema/generate_worker_wire_spec.spl`: 3 passed.
- `test/01_unit/tool/kernel_plugin_schema/generated_worker_wire_bounds_spec.spl`: 4 passed.
- Malformed mutations cover magic, version, header size, digest, reserved fields,
  short/oversized frames, invalid offsets, negative/excess payload lengths, and
  unknown interface/operation slots.

## Remaining Gate

REQ-KPF-008 still requires the broader shared malformed native-layout corpus
across C, Simple, Rust, and C++. This change closes only the worker-wire
generation and focused bounds-conformance gap.
