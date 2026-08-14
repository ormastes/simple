# compiler_hwir Layer Expert

## Role

Own compiler-side typed HWIR under `src/compiler/50.mir/hwir/` and its strict
VHDL serializer under `src/compiler/70.backend/backend/`. This layer is
separate from `src/lib/hardware/vhdl_gen`: it lowers admitted compiler products
through typed graph records and must fail closed before raw VHDL exists.

## Mixed sequential contract

`HwSequentialModuleDef` owns typed datapath signals, integer and bit-vector
constants, combinational operations, comparisons, selects, fixed bit extracts,
fixed slices, and one `HwSequentialPlan`. Only input ports, registers, child
outputs, signals, and constants are readable. Operation destinations must be
declared datapath signals, every signal has exactly one operation driver, and
extension/truncation direction must match the source/result widths.

`render_strict_sequential_hwir` emits declarations, then combinational
assignments, then output bindings and the synchronous process. The v3
structural hash commits every datapath collection. Raw VHDL fragments are not
an input capability.

## Evidence and boundaries

- Plan: `doc/03_plan/agent_tasks/riscv_gen2_hwir_foundation.md` A13.
- SPipe state: `.spipe/riscv_gen2_hwir_foundation/state.md`.
- Focused spec:
  `test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl`.
- Manual:
  `doc/06_spec/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.md`.
- User/developer guide:
  `doc/07_guide/hardware/riscv/vhdl_exec_core_generator.md`.

Source-text checks prove serializer shape only. Qualification requires an
admitted self-hosted CLI, lint/duplication/SSpec maintenance, measured branch
coverage, and generated-VHDL GHDL analyze/elaborate/behavior receipts. A Rust
seed, crashing deployed binary, or the separate pure-Simple golden generator
cannot substitute.
