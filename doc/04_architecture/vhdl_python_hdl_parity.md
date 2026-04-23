# VHDL Python-HDL Parity Architecture

The pure Simple compiler path remains the source of truth for MIR-to-VHDL behavior. The source facade stays as compatibility coverage for legacy Python-HDL-like fixtures but must not grow into the main lowering strategy.

## Layers

- **Metadata preservation:** `compiler.common.attributes` owns `@hardware`, `@generic`, and `@clocked` metadata.
- **MIR ABI:** `compiler.mir` carries hardware metadata, VHDL process instructions, fixed-width primitive types, tuple returns, structs, and enum type definitions.
- **VHDL backend:** `compiler.backend.backend.vhdl_backend` maps MIR types/instructions to VHDL-2008 and rejects unsupported hardware constructs before emission.
- **Compatibility facade:** `compiler.driver.driver_public_compile` handles narrow source fixtures and writes source-map sidecars for public `aot_vhdl_file` users.

## Decisions

- Payload-free enums use VHDL enumeration declarations in MIR declaration order.
- Payload enum hardware use is rejected until tagged-record lowering is designed and tested.
- Optional vendor smoke is environment-gated and not a normal verification dependency.
- Source maps are sidecar JSON next to generated VHDL: `<output>.map.json`.
