# Parser named dependency traversal

> Direct-AST regression for the owner-local parser type and enum-variant

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser named dependency traversal

Direct-AST regression for the owner-local parser type and enum-variant

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/parser_named_dependencies_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Direct-AST regression for the owner-local parser type and enum-variant
dependency walkers. Expected lists are depth-first and preserve declaration
order. Associated projection member names and array length expressions are not
type dependencies.

This spec intentionally imports the candidate helper interface directly. On a
pre-fix compiler tree where the helpers are absent, compilation must fail
rather than silently treating missing dependency coverage as a pass.

## Scenarios

### parser named dependency traversal

#### walks named types and generic arguments in depth-first order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- walks named types and generic arguments in depth-first order
   - Expected: parser_type_named_dependencies(type_) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks named types and generic arguments in depth-first order")
val type_ = dependency_type(TypeKind.Named("Envelope", [
    dependency_named("Key"),
    dependency_type(TypeKind.Named("Vector", [
        dependency_named("Item")
    ]))
]))

expect(parser_type_named_dependencies(type_)).to_equal([
    "Envelope", "Key", "Vector", "Item"
])
```

</details>

#### walks tuple array function optional and reference forms exactly

- walks tuple array function optional and reference forms exactly
   - Expected: parser_type_named_dependencies(tuple_type) equals `[`
   - Expected: parser_type_named_dependencies(array_type) equals `[`
   - Expected: parser_type_named_dependencies(function_type) equals `[`
   - Expected: parser_type_named_dependencies(optional_type) equals `[`
   - Expected: parser_type_named_dependencies(reference_type) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks tuple array function optional and reference forms exactly")
val tuple_type = dependency_type(TypeKind.Tuple([
    dependency_named("TupleFirst"),
    dependency_type(TypeKind.Optional(dependency_named("TupleOptional")))
]))
val array_type = dependency_type(TypeKind.Array(
    dependency_named("ArrayElement"),
    Expr(kind: ExprKind.IntLit(4), span: dependency_test_span())
))
val function_type = dependency_type(TypeKind.Function([
    dependency_named("FunctionFirstParam"),
    dependency_type(TypeKind.Reference(
        dependency_named("FunctionSecondParam"), false))
], dependency_named("FunctionReturn")))
val optional_type = dependency_type(TypeKind.Optional(
    dependency_named("OptionalInner")))
val reference_type = dependency_type(TypeKind.Reference(
    dependency_named("ReferenceInner"), true))

expect(parser_type_named_dependencies(tuple_type)).to_equal([
    "TupleFirst", "TupleOptional"
])
expect(parser_type_named_dependencies(array_type)).to_equal([
    "ArrayElement"
])
expect(parser_type_named_dependencies(function_type)).to_equal([
    "FunctionFirstParam", "FunctionSecondParam", "FunctionReturn"
])
expect(parser_type_named_dependencies(optional_type)).to_equal([
    "OptionalInner"
])
expect(parser_type_named_dependencies(reference_type)).to_equal([
    "ReferenceInner"
])
```

</details>

#### walks atomic isolated union projection and pointer forms exactly

- walks atomic isolated union projection and pointer forms exactly
   - Expected: parser_type_named_dependencies(atomic_type) equals `[`
   - Expected: parser_type_named_dependencies(isolated_type) equals `[`
   - Expected: parser_type_named_dependencies(union_type) equals `[`
   - Expected: parser_type_named_dependencies(projection_type) equals `[`
   - Expected: parser_type_named_dependencies(pointer_type) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks atomic isolated union projection and pointer forms exactly")
val atomic_type = dependency_type(TypeKind.Atomic(
    dependency_named("AtomicInner")))
val isolated_type = dependency_type(TypeKind.Isolated(
    dependency_named("IsolatedInner")))
val union_type = dependency_type(TypeKind.Union([
    dependency_named("UnionLeft"),
    dependency_type(TypeKind.Pointer(
        dependency_named("UnionPointerRight"), false))
]))
val projection_type = dependency_type(TypeKind.Projection(
    dependency_type(TypeKind.Named("ProjectionBase", [
        dependency_named("ProjectionArgument")
    ])),
    "AssociatedItem"
))
val pointer_type = dependency_type(TypeKind.Pointer(
    dependency_named("PointerInner"), true))

expect(parser_type_named_dependencies(atomic_type)).to_equal([
    "AtomicInner"
])
expect(parser_type_named_dependencies(isolated_type)).to_equal([
    "IsolatedInner"
])
expect(parser_type_named_dependencies(union_type)).to_equal([
    "UnionLeft", "UnionPointerRight"
])
expect(parser_type_named_dependencies(projection_type)).to_equal([
    "ProjectionBase", "ProjectionArgument"
])
expect(parser_type_named_dependencies(pointer_type)).to_equal([
    "PointerInner"
])
```

</details>

#### returns no dependencies for infer and error forms

- returns no dependencies for infer and error forms
   - Expected: parser_type_named_dependencies(infer_type) equals `[]`
   - Expected: parser_type_named_dependencies(error_type) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns no dependencies for infer and error forms")
val infer_type = dependency_type(TypeKind.Infer)
val error_type = dependency_type(TypeKind.Error)

expect(parser_type_named_dependencies(infer_type)).to_equal([])
expect(parser_type_named_dependencies(error_type)).to_equal([])
```

</details>

#### walks tuple struct and unit enum variant payloads exactly

- walks tuple struct and unit enum variant payloads exactly
   - Expected: parser_variant_named_dependencies(tuple_variant) equals `[`
   - Expected: parser_variant_named_dependencies(struct_variant) equals `[`
   - Expected: parser_variant_named_dependencies(unit_variant) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks tuple struct and unit enum variant payloads exactly")
val tuple_variant = dependency_variant("TuplePayload", VariantKind.Tuple([
    dependency_named("TuplePayloadFirst"),
    dependency_type(TypeKind.Optional(
        dependency_named("TuplePayloadOptional")))
]))
val struct_variant = dependency_variant("StructPayload", VariantKind.Struct([
    dependency_field("items", dependency_type(TypeKind.Array(
        dependency_named("StructArrayElement"), nil))),
    dependency_field("callback", dependency_type(TypeKind.Function([
        dependency_named("StructFunctionParam")
    ], dependency_named("StructFunctionReturn"))))
]))
val unit_variant = dependency_variant("NoPayload", VariantKind.Unit)

expect(parser_variant_named_dependencies(tuple_variant)).to_equal([
    "TuplePayloadFirst", "TuplePayloadOptional"
])
expect(parser_variant_named_dependencies(struct_variant)).to_equal([
    "StructArrayElement", "StructFunctionParam", "StructFunctionReturn"
])
expect(parser_variant_named_dependencies(unit_variant)).to_equal([])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `97d75f5e607a7385fb7cb9596cb2270e6829884d695d6d3986c7bd19fba5face`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97d75f5e607a7385fb7cb9596cb2270e6829884d695d6d3986c7bd19fba5face`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97d75f5e607a7385fb7cb9596cb2270e6829884d695d6d3986c7bd19fba5face`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/parser_named_dependencies_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/parser_named_dependencies_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/parser_named_dependencies_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/parser_named_dependencies_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/parser_named_dependencies_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walks named types and generic arguments in depth-first order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/parser_named_dependencies_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walks tuple array function optional and reference forms exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/parser_named_dependencies_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walks atomic isolated union projection and pointer forms exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
