# Hir Item Nested Value Ownership Specification

> Tests covering HIR item lowering nested value ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Item Nested Value Ownership Specification

## Scenarios

### HIR item lowering nested value ownership

#### preserves independently owned enum and constant records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves independently owned enum and constant records
   - Expected: lowering.errors.len() equals `0`
   - Expected: hir.enums.keys().len() equals `2`
   - Expected: hir.constants.keys().len() equals `2`
   - Expected: left_symbol == right_symbol is false
   - Expected: left_value equals `11`
   - Expected: right_value equals `22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves independently owned enum and constant records")
val source = "enum First:\n    One\nenum Second:\n    Two\nval left = 11\nval right = 22"
val module = parse_full_frontend(source, "owned.items", "owned.items", Logger(level: 0))
val surfaces = surfaces_for(module, source, "owned.items")
var lowering = hirlowering_for_module("owned.items", surfaces)

val hir = lowering.lower_module(module)

expect(lowering.errors.len()).to_equal(0)
expect(hir.enums.keys().len()).to_equal(2)
expect(hir.constants.keys().len()).to_equal(2)
var enum_names: [text] = []
for enum_key in hir.enums.keys():
    enum_names = enum_names.push(hir.enums[enum_key].name)
expect(enum_names).to_contain("First")
expect(enum_names).to_contain("Second")
var left_symbol = -1
var right_symbol = -1
var left_value = -1
var right_value = -1
for const_key in hir.constants.keys():
    val constant = hir.constants[const_key]
    match constant.name:
        case "left":
            left_symbol = constant.symbol.id
            match constant.value.kind:
                case HirExprKind.IntLit(value, _): left_value = value
                case _: left_value = -2
        case "right":
            right_symbol = constant.symbol.id
            match constant.value.kind:
                case HirExprKind.IntLit(value, _): right_value = value
                case _: right_value = -2
        case _: pass
expect(left_symbol).to_be_greater_than(-1)
expect(right_symbol).to_be_greater_than(-1)
expect(left_symbol == right_symbol).to_equal(false)
expect(left_value).to_equal(11)
expect(right_value).to_equal(22)
```

</details>

#### rejects an imported enum value without its declaration owner

- rejects an imported enum value without its declaration owner
   - Expected: lowered.keys().len() equals `0`
   - Expected: lowering.errors.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an imported enum value without its declaration owner")
val source = "fn noop():\n    pass"
val module = parse_full_frontend(source, "owner.guard", "owner.guard", Logger(level: 0))
val surfaces = surfaces_for(module, source, "owner.guard")
var lowering = hirlowering_for_module("owner.guard", surfaces)
lowering.imported_enums["Detached"] = ParserEnum(
    name: "Detached", type_params: [], variants: [],
    visibility: Visibility.Private, is_public: false,
    has_doc_comment: false, doc_comment: "", span: Span.empty())

val lowered = lowering.lower_module_enum_definitions(module)

expect(lowered.keys().len()).to_equal(0)
expect(lowering.errors.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR item lowering nested value ownership.
- HIR item lowering nested value ownership

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2d7d92b6b39fb63e8a67cfeceace792c4dbb55f400f662328ba3c3a7043a48be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d7d92b6b39fb63e8a67cfeceace792c4dbb55f400f662328ba3c3a7043a48be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d7d92b6b39fb63e8a67cfeceace792c4dbb55f400f662328ba3c3a7043a48be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves independently owned enum and constant records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an imported enum value without its declaration owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
