# VHDL Python-HDL Parity Detail Design

## Backend

- Validate enum variants before package emission.
- Sanitize enum literal names with the existing VHDL identifier sanitizer.
- Reject payload variants with a diagnostic that names the enum and variant.
- Continue using MIR VHDL instructions for resize, slice, concat, port maps, and process lowering.

## Driver Facade

- `aot_vhdl_file` writes generated VHDL and a deterministic source-map sidecar.
- Sidecar JSON includes version, source path, generated path, backend label, entity anchors, and port anchors.
- Existing source-facade parsing remains compatibility-only and is covered by system specs.

## Vendor Smoke

- `test/system/compiler/vhdl_vendor_synthesis_smoke_spec.spl` checks the opt-in/skip contract.
- Vendor execution is enabled only when `SIMPLE_VHDL_VENDOR_SMOKE=1`.
- Missing selected tools report a clear skip reason.
