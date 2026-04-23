# VHDL Python-HDL Parity Requirements

**Feature:** VHDL Python-HDL parity gaps `VHDL-PARITY-003` through `VHDL-PARITY-015`
**Selected scope:** Parity gaps
**Status:** Implemented slice with documented deferrals

## Requirements

- **REQ-VHDL-PARITY-003:** VHDL lowering preserves structured clock/reset/domain metadata and emits supported async, sync, and no-reset clocked process shapes.
- **REQ-VHDL-PARITY-004:** Fixed-width integer operations lower with explicit VHDL signedness, resize, slice, concat, shift, comparison, and width mismatch diagnostics.
- **REQ-VHDL-PARITY-005:** Interface bundles flatten deterministically from labeled tuple fields and reject sanitized VHDL name collisions.
- **REQ-VHDL-PARITY-006:** Payload-free enums lower in declaration order. Payload enums fail before VHDL emission with a payload-specific diagnostic until tagged-record lowering exists.
- **REQ-VHDL-PARITY-010:** Pure helper subprograms remain deferred unless a helper classifier proves they are combinational and side-effect-free; public hardware still lowers as entities.
- **REQ-VHDL-PARITY-011:** ROM/RAM inference remains explicit and conservative; unsupported memory patterns fail before invalid VHDL emission.
- **REQ-VHDL-PARITY-012:** Supported testbench conversion slice covers one DUT, literal stimuli, named port maps, and `expect(...).to_equal(...)` as VHDL assertions.
- **REQ-VHDL-PARITY-013:** VHDL generation emits a deterministic `.map.json` sidecar with generated entity and port anchors.
- **REQ-VHDL-PARITY-014:** Vendor synthesis smoke is opt-in by `SIMPLE_VHDL_VENDOR_SMOKE=1` and skips clearly when disabled or unavailable.
- **REQ-VHDL-PARITY-015:** The support matrix and parity roadmap distinguish pure Simple source-of-truth support from compatibility source-facade coverage.

## Explicit Deferrals

Tagged-record payload enum lowering, general helper-to-subprogram lowering, and broad ROM/RAM inference are not enabled by default in this pass. They must remain hard diagnostics rather than partial VHDL output.
