# VHDL Backend Known Limitations

**Date:** 2026-04-04
**Status:** Active
**Tracks:** Known limitations and workarounds for the VHDL backend

## Runtime/Language Limitations

### L001: No floating-point type support
**Severity:** By design
**Workaround:** Use integer fixed-point representations
**Details:** `f16`, `f32`, `f64` are not synthesizable in VHDL. The backend produces a hard error: "Floating-point constant is not synthesizable for the VHDL backend."

### L002: No dynamic heap allocation
**Severity:** By design
**Workaround:** Use fixed-size arrays and records
**Details:** VHDL hardware descriptions do not support dynamic memory allocation. All data structures must have statically known sizes.

### L003: No general polymorphism
**Severity:** By design
**Workaround:** Use monomorphized (concrete-typed) functions
**Details:** The VHDL backend operates on MIR after monomorphization. Generic functions must be fully specialized before VHDL lowering.

### L004: No pointer types
**Severity:** By design
**Workaround:** Use direct signal/port connections
**Details:** Pointers are mapped to an error comment in the type mapper. Hardware descriptions use signals and ports instead of memory addresses.

### L005: Unit type not lowerable
**Severity:** By design
**Workaround:** Use concrete return types or void-equivalent signals
**Details:** `Unit` cannot be mapped to a VHDL signal type. Functions that return Unit should not be lowered to hardware entities.

## Backend Behavior Limitations

### L006: HardwareCodegen trait compile_process emits error comments for failed instructions
**Severity:** Medium
**Workaround:** Use the main `VhdlBackend.compile()` path instead of `HardwareCodegen.compile_process()`
**Details:** The `compile_process()` method on the HardwareCodegen trait returns `text` (not `Result`), so instruction compilation failures produce inline error comments rather than hard compile errors. The main `compile()` path correctly returns `Result` with hard errors.

### L007: Simulation-backed proof is deferred
**Severity:** Low (scoping decision)
**Workaround:** Use GHDL analysis/elaboration for validation
**Details:** The `riscv32_sim_vhdl` target lane is quarantined. Simulation-backed execution proof is a follow-on milestone. See `doc/04_architecture/vhdl_simulation_milestone_decision.md`.

### L008: Builder API examples are not backend-generated
**Severity:** Documentation clarity
**Workaround:** See `examples/09_embedded/vhdl/README.md` for classification
**Details:** Examples under `examples/09_embedded/vhdl/` use the VhdlBuilder API programmatically, not the `--backend=vhdl` compilation path. Golden files are builder-generated, not backend-generated.

## Toolchain Requirements

### L009: GHDL required for validation
**Severity:** External dependency
**Workaround:** Tests skip gracefully when GHDL is not installed
**Details:** GHDL must be installed for integration tests to run analysis/elaboration validation. Without GHDL, structural text checks are the only validation.

### L010: Yosys synthesis is not integrated
**Severity:** Deferred feature
**Workaround:** Use GHDL `--synth` for basic synthesis checking
**Details:** Yosys integration via the GHDL plugin exists in CI workflow but is currently disabled. The `yosys_synth_ghdl()` FFI function is available but not tested in the standard test suite.

## Constraint Checker Limitations

### L011: Constraints are not auto-extracted from MIR
**Severity:** Medium
**Workaround:** Constraints must be manually registered via `VhdlConstraintChecker.add_constraint()`
**Details:** The constraint checker validates registered constraints but does not automatically extract width/CDC/sensitivity constraints from the MIR during compilation. This requires explicit integration in the compilation pipeline.

## See Also

- `doc/04_architecture/vhdl_support_matrix.md` — Full support matrix
- `doc/04_architecture/vhdl_hardware_subset_contract.md` — Supported subset
- `doc/04_architecture/vhdl_simulation_milestone_decision.md` — Simulation scope
- `doc/05_design/VHDL_BACKEND_DESIGN.md` — Design document
