# VHDL Python-HDL Parity System Test Plan

## Runnable Specs

- `test/01_unit/compiler/backend/vhdl_backend_spec.spl`
- `test/03_system/compiler/vhdl_source_facade_spec.spl`
- `test/01_unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl`
- `test/02_integration/compiler/vhdl_backend_e2e_spec.spl`
- `test/03_system/feature/usage/vhdl_spec.spl`

## Coverage

- MIR payload-free enum emission and payload enum rejection.
- Enum sanitized-name collision diagnostics.
- Source facade reset, fixed-width operations, bundle flattening, and GHDL analysis where available.
- Source-map sidecar creation and stable content anchors.
- Vendor smoke skip behavior.

## Final Gates

- `sh scripts/check/check-core-runtime-smoke.shs bin/simple`
- `SIMPLE_BINARY=bin/simple sh scripts/check/check-mcp-native-smoke.shs`
