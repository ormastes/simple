# Cross Module Field Layout Source Specification

> Tests covering cross-module field layout precedence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Module Field Layout Source Specification

## Scenarios

### cross-module field layout precedence

#### uses name-keyed value provenance before module-local symbol ids

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses name-keyed value provenance before module-local symbol ids
   - Expected: source does not contain `self.struct_value_syms.get(base_local.id)`
   - Expected: method_source.split("self.remember_method_return_provenance(").len() - 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses name-keyed value provenance before module-local symbol ids")
val source = rt_file_read_text("src/compiler/50.mir/_MirLowering/function_lowering.spl") ?? ""
val dispatch_source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
val method_source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl") ?? ""
val module_source = rt_file_read_text("src/compiler/50.mir/_MirLowering/module_lowering.spl") ?? ""
val mir_data_source = rt_file_read_text("src/compiler/50.mir/mir_data.spl") ?? ""

expect(source).to_contain("Numeric SymbolIds are local to each module and can collide")
expect(source).to_contain("if self.struct_value_syms.contains(base_local.id):")
expect(source).to_contain("val value_fields = self.struct_field_order[value_name]")
expect(source.contains("self.struct_value_syms.get(base_local.id)")).to_equal(false)
expect(dispatch_source).to_contain("bootstrap_fn_ret_shape_lookup(call_symbol.name)")
expect(dispatch_source).to_contain("self.struct_value_syms[local.id] = shape")
expect(module_source).to_contain("prescan_return_shape = self.composite_layout_key(prescan_return_symbol)")
expect(module_source).to_contain("self.register_composite_field_metadata(class_key, class_def.fields, module.symbols, false)")
expect(mir_data_source).to_contain("fn bootstrap_fn_ret_shape_register(name: text, shape: text):")
expect(method_source).to_contain("me remember_method_return_provenance(result_local: LocalId, method_key: text):")
expect(method_source.split("self.remember_method_return_provenance(").len() - 1).to_equal(2)
expect(method_source).to_contain("case Class | Struct | Enum | Import: static_receiver_name = static_name")
expect(method_source).to_contain("self.symbols.lookup_method_in_type(static_symbol, method)")
expect(method_source).to_contain("case Function: static_method_id = Some(static_candidate_id)")
expect(method_source).to_contain("val declared_receiver_type = self.receiver_declared_type(receiver)")
expect(method_source).to_contain("case Method: unresolved_method_id = Some(instance_candidate_id)")
expect(method_source).to_contain("if not self.struct_value_syms.contains(result_local.id)")
```

</details>

#### keeps an incremental executable cross-module regression

- keeps an incremental executable cross-module regression
   - Expected: spec does not contain `--clean`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps an incremental executable cross-module regression")
val spec = rt_file_read_text("test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl") ?? ""

expect(spec).to_contain("use .payload_provider.{LayoutPayload, LayoutMaker}")
expect(spec).to_contain("val maker: LayoutMaker = LayoutMaker(seed: 7)")
expect(spec).to_contain("val static_payload: LayoutPayload = LayoutMaker.create(9)")
expect(spec).to_contain("print(payload.wanted + static_payload.wanted)")
expect(spec).to_contain("--entry-closure --cache-dir ")
expect(spec.contains("--clean")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/cross_module_field_layout_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cross-module field layout precedence.
- cross-module field layout precedence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba5a5df04ff55de6b8853bc8b1ac88de5e0e3f9d7bd9fc7216f3158bd62fd71c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba5a5df04ff55de6b8853bc8b1ac88de5e0e3f9d7bd9fc7216f3158bd62fd71c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba5a5df04ff55de6b8853bc8b1ac88de5e0e3f9d7bd9fc7216f3158bd62fd71c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/cross_module_field_layout_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/cross_module_field_layout_source_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=40
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/cross_module_field_layout_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/cross_module_field_layout_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/cross_module_field_layout_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/cross_module_field_layout_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/cross_module_field_layout_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/cross_module_field_layout_source_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses name-keyed value provenance before module-local symbol ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/cross_module_field_layout_source_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps an incremental executable cross-module regression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
