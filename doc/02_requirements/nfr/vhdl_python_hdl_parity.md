# VHDL Python-HDL Parity NFRs

**Selected NFR level:** Simulation-grade

## Requirements

- **NFR-VHDL-PARITY-001:** Generated VHDL for supported examples must pass GHDL analysis and elaboration when GHDL is available.
- **NFR-VHDL-PARITY-002:** Unsupported constructs must fail before writing stale or invalid VHDL.
- **NFR-VHDL-PARITY-003:** Source-map sidecars must be deterministic across repeated generation from the same source.
- **NFR-VHDL-PARITY-004:** Vendor synthesis checks must not run during normal local verification unless explicitly enabled.
- **NFR-VHDL-PARITY-005:** Diagnostics must name the unsupported hardware construct and, where available, the generated VHDL identifier involved.
