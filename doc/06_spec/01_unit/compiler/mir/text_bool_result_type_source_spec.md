# Text Bool Result Type Source Specification

> Tests covering MIR text predicate result typing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Bool Result Type Source Specification

## Scenarios

### MIR text predicate result typing

#### clears every LocalId owner table before each function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- clears every LocalId owner table before each function
   - Expected: module_source.split("self.reset_function_local_tracking()").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clears every LocalId owner table before each function")
val function_source = file_read("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val module_source = file_read("src/compiler/50.mir/_MirLowering/module_lowering.spl")
expect(function_source).to_contain("me reset_function_local_tracking():")
expect(function_source).to_contain("self.bitfield_value_syms = {}")
expect(function_source).to_contain("self.struct_value_syms = {}")
expect(function_source).to_contain("self.runtime_elem_value_type = {}")
expect(function_source).to_contain("self.array_element_struct_syms = {}")
expect(function_source).to_contain("self.option_value_locals = {}")
expect(module_source.split("self.reset_function_local_tracking()").len()).to_equal(3)
```

</details>

#### keeps starts_with, ends_with, and contains boolean through lowering

- keeps starts_with, ends_with, and contains boolean through lowering


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps starts_with, ends_with, and contains boolean through lowering")
val source = file_read("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")
expect(source).to_contain("predicate_receiver_is_text = self.local_is_str(prelowered_method_receiver)")
expect(source).to_contain("if not predicate_receiver_is_text and self.local_hir_types.has(prelowered_method_receiver.id):")
expect(source).to_contain("case HirTypeKind.Str: predicate_receiver_is_text = true")
expect(source).to_contain("val predicate_owner_recovery_allowed = match resolution:")
expect(source).to_contain("case Unresolved | InstanceMethod(_, _): true")
expect(source).to_contain("(resolution_is_unresolved or predicate_receiver_is_text)")
expect(source).to_contain("if not predicate_receiver_is_text and resolution_is_unresolved:")
expect(source).to_contain("self.build_args_from_receiver(prelowered_method_receiver, args)")
expect(source).to_contain("MirConstValue.Str(\"rt_string_starts_with\"),\n                        MirType(kind: MirTypeKind.FuncPtr(MirSignature(params: [], return_type: MirType.bool()")
expect(source).to_contain("b_sw.emit_call(starts_op, [mir_operand_copy(sw_receiver), mir_operand_copy(sw_tagged_prefix)], MirType.bool())")
expect(source).to_contain("MirConstValue.Str(\"rt_string_ends_with\"),\n                        MirType(kind: MirTypeKind.FuncPtr(MirSignature(params: [], return_type: MirType.bool()")
expect(source).to_contain("b_ew.emit_call(ends_op, [mir_operand_copy(ew_receiver), mir_operand_copy(ew_tagged_suffix)], MirType.bool())")
expect(source).to_contain("case \"contains\":\n                        MirType.bool()")
```

</details>

#### renders unresolved primitive text conversions after custom owners

- renders unresolved primitive text conversions after custom owners
   - Expected: source does not contain `method == "to_string" and args.len() == 0 and (rt_env_get("SIMPLE_BOOTSTRAP")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders unresolved primitive text conversions after custom owners")
val source = file_read("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")
expect(source).to_contain("val is_text_conversion = (method == \"to_text\" or method == \"to_string\") and args.len() == 0")
expect(source).to_contain("val conversion_rendered = self.coerce_concat_operand(unresolved_receiver_local)")
expect(source).to_contain("b_conversion.emit_call(conversion_cstr_op, [conversion_rendered], MirType(kind: MirTypeKind.Opaque(\"str\")))")
expect(source.contains("method == \"to_string\" and args.len() == 0 and (rt_env_get(\"SIMPLE_BOOTSTRAP\")")).to_equal(false)
val owner_dispatch: i64 = source.find("if self.struct_method_syms.has(unresolved_method_key):")
val primitive_fallback: i64 = source.find("val is_text_conversion = (method == \"to_text\" or method == \"to_string\")")
expect(primitive_fallback).to_be_greater_than(owner_dispatch)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/text_bool_result_type_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR text predicate result typing.
- MIR text predicate result typing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `fcf36a01803336f672dd1047ab3a49224072b3c1782119bb330117307d2a4d0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcf36a01803336f672dd1047ab3a49224072b3c1782119bb330117307d2a4d0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcf36a01803336f672dd1047ab3a49224072b3c1782119bb330117307d2a4d0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/text_bool_result_type_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/text_bool_result_type_source_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=40
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/text_bool_result_type_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/text_bool_result_type_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/text_bool_result_type_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/text_bool_result_type_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/text_bool_result_type_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/text_bool_result_type_source_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears every LocalId owner table before each function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/text_bool_result_type_source_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps starts_with, ends_with, and contains boolean through lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/text_bool_result_type_source_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders unresolved primitive text conversions after custom owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
