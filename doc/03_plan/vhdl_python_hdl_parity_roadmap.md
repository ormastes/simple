# VHDL Python-HDL Parity Task Matrix

This matrix converts the Python-HDL parity roadmap into assignable work.
The labeled multi-return and `@hardware` output-port milestone is complete;
the remaining Python-HDL parity items are pending until implemented and
verified.

Status values:

- Complete: implemented and verified in the current tree.
- Pending: scoped and assigned, but not truthfully complete.
- Blocked: cannot start until a named dependency is complete.

Pending SSpec coverage is tracked in
`test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip`. The support matrix
links these pending specs from `doc/04_architecture/vhdl_support_matrix.md`.

## Assignment Matrix

| Task ID | Owner | Status | Scope | Acceptance Criteria | Verification Commands |
| --- | --- | --- | --- | --- | --- |
| VHDL-PARITY-000 | A | Complete | Common Simple labeled multi-return syntax and runtime access. | Labeled tuple return types and expressions parse; labels are preserved through type/HIR/runtime; `r.field` and `r.0` work for labeled tuple returns; repeated same-type anonymous function returns are rejected. | `cargo test -p simple-parser --test functions labeled_tuple`; `cargo test -p simple-type --test inference labeled_tuple`; `cargo test -p simple-type --test inference repeated_same_type`; `cargo test -p simple-driver --test runner_tests runner_evaluates_labeled_tuple_return_fields` |
| VHDL-PARITY-001 | A | Complete | `@hardware` labeled multi-output VHDL ports. | A hardware function returning `(sum: bool, cout: bool)` emits `sum` and `cout` output ports; generated VHDL analyzes, elaborates, and synthesizes with GHDL. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl`; `ghdl -a --std=08 <generated>.vhdl`; `ghdl -e --std=08 <entity>`; `ghdl --synth --std=08 <entity>` |
| VHDL-PARITY-002 | B | Complete | Facade clocked process lowering. | `@clocked(clk, reset_n)` hardware emits clock/reset input ports when needed and lowers scalar assignments into a reset-aware `process(clk, reset_n)` with `rising_edge(clk)`; generated VHDL analyzes with GHDL. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-003 | B | Pending | Full reset and clock-domain model. | Hardware functions can declare reset polarity/synchrony and named clock domains; invalid domain crossings are diagnosed or explicitly modeled; generated VHDL reset behavior simulates correctly. | `bin/simple test test/system/compiler/vhdl_reset_domain_spec.spl`; `ghdl -a --std=08 <generated>.vhdl`; `ghdl -r --std=08 <testbench>` |
| VHDL-PARITY-004 | B | Pending | Fixed-width bit operations. | Sized bit vectors support arithmetic, shifts, slices, concatenation, comparisons, and explicit conversions with Python-HDL-compatible width semantics. | `bin/simple test test/system/compiler/vhdl_fixed_width_bits_spec.spl`; `ghdl -a --std=08 <generated>.vhdl`; `ghdl -r --std=08 <testbench>` |
| VHDL-PARITY-005 | C | Complete | Facade composite input ports. | Labeled tuple input parameters lower to stable flattened VHDL input ports; expressions like `bus.addr` map to deterministic names like `bus_addr`; generated VHDL analyzes with GHDL. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-006 | C | Pending | Interface bundles. | Named interface bundles can group related ports; nested bundle names are collision-safe after VHDL identifier sanitization; caller/callee wiring remains named. | `bin/simple test test/system/compiler/vhdl_interface_bundles_spec.spl`; `ghdl -a --std=08 <generated>.vhdl` |
| VHDL-PARITY-007 | C | Complete | Facade entity generics. | `@generic(...)` lowers to a VHDL entity `generic` block with default values; generated VHDL analyzes and elaborates with GHDL. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-008 | C | Pending | Enum encoding. | Payload-free enums lower to deterministic VHDL encodings; user-selected or documented default encodings are stable and covered by simulation. | `bin/simple test test/system/compiler/vhdl_enum_encoding_spec.spl`; `ghdl -a --std=08 <generated>.vhdl`; `ghdl -r --std=08 <testbench>` |
| VHDL-PARITY-009 | C | Pending | Payload enums. | Payload enums are either lowered to tagged record representations with verified behavior or rejected with a specific diagnostic until supported. | `bin/simple test test/system/compiler/vhdl_payload_enum_spec.spl`; `ghdl -a --std=08 <generated>.vhdl` |
| VHDL-PARITY-010 | D | Pending | VHDL subprogram emission. | Reusable pure combinational helpers lower to VHDL functions/procedures when profitable; direct entity lowering remains available where required. | `bin/simple test test/system/compiler/vhdl_subprogram_spec.spl`; `ghdl -a --std=08 <generated>.vhdl` |
| VHDL-PARITY-011 | D | Pending | ROM/RAM inference. | Static ROM tables and supported RAM patterns emit VHDL that synthesis tools infer as memory instead of expanded combinational logic where appropriate. | `bin/simple test test/system/compiler/vhdl_memory_inference_spec.spl`; `ghdl --synth --std=08 <entity>` |
| VHDL-PARITY-012 | D | Pending | Testbench conversion. | Simple hardware tests can emit runnable VHDL testbenches with clocks, resets, stimuli, assertions, and deterministic pass/fail exit behavior. | `bin/simple test test/system/compiler/vhdl_testbench_conversion_spec.spl`; `ghdl -a --std=08 <testbench>.vhdl`; `ghdl -r --std=08 <testbench>` |
| VHDL-PARITY-013 | E | Partial | Source maps. | `aot_vhdl_file` emits a deterministic `<output>.map.json` sidecar with generated entity and port anchors; diagnostic remapping remains future work. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-014 | E | Partial | Vendor synthesis smoke. | Optional smoke is environment-gated and skips clearly when disabled or when the selected tool is missing; full vendor command log capture remains future work. | `bin/simple test test/system/compiler/vhdl_vendor_synthesis_smoke_spec.spl` |
| VHDL-PARITY-015 | E | Complete | Parity documentation and support matrix maintenance. | Final feature/NFR/design/test artifacts exist and the support matrix distinguishes implemented, partial, pending, and unsupported Python-HDL parity features. | `bin/simple test doc/06_spec/app/compiler/feature/vhdl_python_hdl_parity_spec.spl`; docs review of `doc/04_architecture/vhdl_support_matrix.md` |

## Worker Boundaries

Worker A owns common multi-return and assignment planning. Do not reopen
completed syntax/runtime work unless a later parity task exposes a regression.

Worker B owns sequential semantics: clocks, resets, domains, and fixed-width
operations needed by clocked logic.

Worker C owns public hardware interface shape: composite ports, bundles,
generics, and enum representations.

Worker D owns generated VHDL quality and reusable generated artifacts:
subprograms, memory inference, and converted testbenches.

Worker E owns diagnostics, source mapping, vendor synthesis smoke, and support
matrix accuracy.

## Completion Gate

Python-HDL parity is not complete until all pending tasks above are complete
and the full parity verification set passes:

```sh
cargo check -p simple-parser -p simple-compiler -p simple-driver
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
sh scripts/check-core-runtime-smoke.shs bin/simple
SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs
```
