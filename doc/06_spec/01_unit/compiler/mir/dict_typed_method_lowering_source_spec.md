# Dict Typed Method Lowering Source Specification

> Tests covering typed Dict method lowering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Typed Method Lowering Source Specification

## Scenarios

### typed Dict method lowering

#### routes typed receivers through the shared runtime owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes typed receivers through the shared runtime owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes typed receivers through the shared runtime owner")
val types = rt_file_read_text("src/compiler/20.hir/hir_lowering/types.spl") ?? ""
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl") ?? ""
val harness = rt_file_read_text("scripts/check/check-native-seed-parity.shs") ?? ""

expect(types).to_contain("case \"Dict\":")
expect(types).to_contain("HirTypeKind.Dict(hir_args[0], hir_args[1])")
expect(source).to_contain("case Dict(_, _): receiver_is_dict = true")
expect(source).to_contain("resolution_is_unresolved or resolved_dict_probe_is_safe")
expect(source).to_contain("dict_recv_local = prelowered_method_receiver")
expect(source).to_contain("self.build_args_from_receiver(prelowered_method_receiver, args)")
expect(source).to_contain("MirConstValue.Str(\"rt_dict_contains\")")
expect(harness).to_contain("fn has_key(d: Dict<text, i64>, key: text) -> bool:")
expect(harness).to_contain("print(has_key(d, \"z\"))")
```

</details>

#### keeps the first self-host stage off ambiguous has dispatch

- keeps the first self-host stage off ambiguous has dispatch
   - Expected: source does not contain `self.local_tuple_types.has(`
   - Expected: source does not contain `self.local_struct_types.has(`
   - Expected: source does not contain `self.struct_field_types_by_name.has(`
   - Expected: source does not contain `fld_struct_fields.has(`
   - Expected: source does not contain `fld_owner_fields.has(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the first self-host stage off ambiguous has dispatch")
val source = rt_file_read_text("src/compiler/20.hir/hir_lowering/expressions.spl") ?? ""

expect(source).to_contain("extern fn rt_dict_contains(dict: i64, key: Any) -> bool")
expect(source.contains("self.local_tuple_types.has(")).to_equal(false)
expect(source.contains("self.local_struct_types.has(")).to_equal(false)
expect(source.contains("self.struct_field_types_by_name.has(")).to_equal(false)
expect(source.contains("fld_struct_fields.has(")).to_equal(false)
expect(source.contains("fld_owner_fields.has(")).to_equal(false)
```

</details>

#### keeps JSON object has receivers statically typed

- keeps JSON object has receivers statically typed
   - Expected: source.split("val map: Dict<text, any> = json_to_object(obj)").len() - 1 equals `3`
   - Expected: source.split("map.has(key)").len() - 1 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps JSON object has receivers statically typed")
val source = rt_file_read_text("src/lib/common/json/object_ops.spl") ?? ""

expect(source.split("val map: Dict<text, any> = json_to_object(obj)").len() - 1).to_equal(3)
expect(source.split("map.has(key)").len() - 1).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed Dict method lowering.
- typed Dict method lowering

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

- Canonical SPipe generation for source `0ee13356fcfe27be1c5caefb31d74b6e76b8d578924027e4ecac7b112b471acc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ee13356fcfe27be1c5caefb31d74b6e76b8d578924027e4ecac7b112b471acc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ee13356fcfe27be1c5caefb31d74b6e76b8d578924027e4ecac7b112b471acc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=30
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes typed receivers through the shared runtime owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the first self-host stage off ambiguous has dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/dict_typed_method_lowering_source_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps JSON object has receivers statically typed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
