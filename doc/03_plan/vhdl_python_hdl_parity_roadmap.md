# VHDL Python-HDL Parity Task Matrix

This matrix records the selected Python-HDL parity milestone. The 2026-04-23
implementation batch closes `VHDL-PARITY-003` through `VHDL-PARITY-015` for
the supported Simple/VHDL subset: reset/domain metadata, fixed-width operations,
interface bundle flattening, payload-free enums, tagged-record payload enum construction, helper subprogram templates,
ROM/RAM templates, generated one-DUT and multi-DUT/multi-phase testbench
artifacts, source-map sidecars, vendor smoke skip/report/log behavior, and
documentation are implemented and verified.
Broad HLS behavior outside that selected subset is explicitly deferred and must
fail with hard diagnostics instead of emitting incomplete VHDL.

Status values:

- Complete: implemented and verified in the current tree.
- Deferred: intentionally out of scope for this milestone; unsupported input
  must fail before VHDL emission.
- Blocked: cannot start until a named dependency is complete.

Deferred SSpec coverage remains listed by
`bin/simple test --only-skipped --list-skip-features --pending` where present.
The support matrix distinguishes those milestone-out-of-scope items from the
completed lanes below.

## Assignment Matrix

| Task ID | Owner | Status | Scope | Acceptance Criteria | Verification Commands |
| --- | --- | --- | --- | --- | --- |
| VHDL-PARITY-000 | A | Complete | Common Simple labeled multi-return syntax and runtime access. | Labeled tuple return types and expressions parse; labels are preserved through type/HIR/runtime; `r.field` and `r.0` work for labeled tuple returns; repeated same-type anonymous function returns are rejected. | `cargo test -p simple-parser --test functions labeled_tuple`; `cargo test -p simple-type --test inference labeled_tuple`; `cargo test -p simple-type --test inference repeated_same_type`; `cargo test -p simple-driver --test runner_tests runner_evaluates_labeled_tuple_return_fields` |
| VHDL-PARITY-001 | A | Complete | `@hardware` labeled multi-output VHDL ports. | A hardware function returning `(sum: bool, cout: bool)` emits `sum` and `cout` output ports; generated VHDL analyzes, elaborates, and synthesizes with GHDL. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl`; `ghdl -a --std=08 <generated>.vhdl`; `ghdl -e --std=08 <entity>`; `ghdl --synth --std=08 <entity>` |
| VHDL-PARITY-002 | B | Complete | Facade clocked process lowering. | `@clocked(clk, reset_n)` hardware emits clock/reset input ports when needed and lowers scalar assignments into a reset-aware `process(clk, reset_n)` with `rising_edge(clk)`; generated VHDL analyzes with GHDL. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-003 | B | Complete | Reset polarity/synchrony and no-reset process emission. | Named domains, reset polarity/synchrony/no-reset metadata, duplicate sanitized domain diagnostics, and unsupported crossing diagnostics flow through attributes, MIR, backend lowering, and constraints for the supported subset. | `bin/simple test test/unit/compiler/backend/vhdl_backend_spec.spl`; `bin/simple test test/unit/compiler/backend/vhdl_constraints_spec.spl`; `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-004 | B | Complete | Fixed-width bit operations. | Explicit width propagation, resize/truncate/sign/zero extension, slice/concat, literal shifts, comparisons, and unsupported implicit-width diagnostics are covered for the supported subset. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl`; `bin/simple test test/unit/compiler/backend/vhdl_backend_spec.spl`; `bin/simple test test/unit/compiler/backend/vhdl_type_mapper_spec.spl` |
| VHDL-PARITY-005 | C | Complete | Facade composite input ports and collision diagnostics. | Labeled tuple input parameters lower to stable flattened VHDL input ports; one nested input bundle is supported; sanitized input/input and input/output port collisions are rejected before VHDL is written. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-006 | C | Complete | Interface bundles. | Named and nested bundle aliases lower through the source facade/system path with deterministic flattened names, named wiring, source-map anchors, and collision diagnostics. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl`; `ghdl -a --std=08 <generated>.vhdl` |
| VHDL-PARITY-007 | C | Complete | Facade entity generics. | `@generic(...)` lowers to a VHDL entity `generic` block with default values; generated VHDL analyzes and elaborates with GHDL. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-008 | C | Complete | Enum encoding. | Payload-free enum declarations, ports, literals, sanitized VHDL names, and collision diagnostics are supported in the current compiler layers. | `bin/simple test test/unit/compiler/backend/vhdl_backend_spec.spl`; `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-009 | C | Complete | Payload enums. | Payload enums lower to tagged-record VHDL types for ports/results, aggregate construction, payload field projection, and tag-based switch matching. | `bin/simple test test/unit/compiler/backend/vhdl_backend_spec.spl`; `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl` |
| VHDL-PARITY-010 | D | Complete | VHDL subprogram emission. | Helper classification, deterministic helper names, function/procedure declarations and bodies, direct helper calls, package integration, and name collision diagnostics are covered. | `bin/simple test test/unit/compiler/backend/vhdl_backend_spec.spl`; `ghdl -a --std=08 <generated>.vhdl` |
| VHDL-PARITY-011 | D | Complete | ROM/RAM inference. | Static ROM, registered ROM read, and explicit single-port synchronous RAM read-during-write policies render synthesizable templates; ambiguous, unconstrained, or unsupported memory forms fail with hard diagnostics. | `bin/simple test test/unit/compiler/backend/vhdl_memory_templates_spec.spl`; `ghdl --synth --std=08 <entity>` |
| VHDL-PARITY-012 | D | Complete | Testbench conversion. | The renderer emits deterministic one-DUT testbenches and ordered multi-DUT/multi-phase suites with literal stimuli, optional clock/reset driving, named port maps, equality assertions, pass/fail `severity failure` behavior, and source-map anchors. | `bin/simple test test/unit/compiler/backend/vhdl_testbench_spec.spl` |
| VHDL-PARITY-013 | E | Complete | Source maps. | `aot_vhdl_file` emits deterministic `<output>.map.json` sidecars for generated entities and ports; testbench artifacts include source-map JSON for test names, ports, port-map lines, and expectations. Diagnostics use source spans where available. | `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl`; `bin/simple test test/unit/compiler/backend/vhdl_testbench_spec.spl` |
| VHDL-PARITY-014 | E | Complete | Vendor synthesis smoke. | Optional smoke is environment-gated, never blocks normal verification, and reports deterministic command, report, and log paths with clear disabled, missing-tool, or executed diagnostics. | `bin/simple test test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl` |
| VHDL-PARITY-015 | E | Complete | Parity documentation and support matrix maintenance. | Final feature/NFR/design/test artifacts exist and the support matrix distinguishes implemented milestone behavior from deferred unsupported Python-HDL/HLS features. | `bin/simple test doc/06_spec/app/compiler/feature/vhdl_python_hdl_parity_spec.spl`; docs review of `doc/04_architecture/vhdl_support_matrix.md` |

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

The selected Python-HDL parity milestone is complete when the focused parity
verification set passes and deferred broad-HLS items remain hard diagnostics:

```sh
bin/simple test --no-cache test/unit/compiler/backend/vhdl_backend_spec.spl
bin/simple test --no-cache test/unit/compiler/backend/vhdl_type_mapper_spec.spl
bin/simple test --no-cache test/unit/compiler/backend/vhdl_constraints_spec.spl
bin/simple test --no-cache test/unit/compiler/backend/vhdl_memory_templates_spec.spl
bin/simple test --no-cache test/unit/compiler/backend/vhdl_testbench_spec.spl
bin/simple test --no-cache test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl
bin/simple test --no-cache test/system/compiler/vhdl_source_facade_spec.spl
bin/simple test --no-cache test/integration/compiler/vhdl_backend_e2e_spec.spl
bin/simple test --no-cache test/feature/usage/vhdl_spec.spl
bin/simple test --no-cache doc/06_spec/app/compiler/feature/vhdl_python_hdl_parity_spec.spl
sh scripts/check-core-runtime-smoke.shs bin/simple
SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs
```
