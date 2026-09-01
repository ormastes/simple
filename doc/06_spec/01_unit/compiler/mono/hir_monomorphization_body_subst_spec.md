# HIR monomorphization substitutes the specialization BODY, not just its signature

> `substitute_expr` used to substitute only an expression's OWN recorded type and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR monomorphization substitutes the specialization BODY, not just its signature

`substitute_expr` used to substitute only an expression's OWN recorded type and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

```simple
`substitute_expr` used to substitute only an expression's OWN recorded type and
never recursed into sub-expressions, and `substitute_function` never touched
`func.body` at all. A specialization therefore had a CONCRETE signature and a
body still full of the template's `TypeParam("T")` types — a silent miscompile:
nothing downstream of Phase 4 diagnoses a leftover type parameter, so wrong
code would be generated with no error.

This spec builds

    fn box_it<T>(v: T) -> [T]:
        val tmp: T = v
        [tmp, v]            # nested: array literal, elem type T, elements typed T

and calls `box_it<i64>(7)`, then walks the WHOLE specialized body — every
statement, every nested expression, the `let` annotation and the array
literal's element type — asserting that NO `TypeParam` survives anywhere.

Before the fix the body walk found the template types (`let` annotation `T`,
array elem type `T`, and the `T`-typed element expressions) and the count of
surviving type params was non-zero. After it, it is zero while the signature
assertions still hold.

```
## Scenarios

### HIR monomorphization body substitution (#158 Phase B hole)

#### leaves no type parameter anywhere in the specialized body

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- leaves no type parameter anywhere in the specialized body
   - Expected: spec != nil is true
   - Expected: count_tp_block(spec.body) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves no type parameter anywhere in the specialized body")
val (result, _) = run_monomorphization(make_modules())
val spec = specialized_of(result)
expect(spec != nil).to_equal(true)
expect(count_tp_block(spec.body)).to_equal(0)
```

</details>

#### still leaves no type parameter in the specialized signature

- still leaves no type parameter in the specialized signature
   - Expected: spec != nil is true
   - Expected: spec.type_params.len() equals `0`
   - Expected: sig_tp equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still leaves no type parameter in the specialized signature")
val (result, _) = run_monomorphization(make_modules())
val spec = specialized_of(result)
expect(spec != nil).to_equal(true)
expect(spec.type_params.len()).to_equal(0)
var sig_tp = count_tp_type(spec.return_type)
for p in spec.params:
    val pt: HirParam = p
    sig_tp = sig_tp + count_tp_type(pt.type_)
expect(sig_tp).to_equal(0)
```

</details>

#### removes the consumed template rather than mutating it in place

- removes the consumed template rather than mutating it in place
   - Expected: templates equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("removes the consumed template rather than mutating it in place")
# Superseded 2026-08-21 by plan section 9.3 step 12. The point this
# example guarded - that specialization never mutates the template in
# place - is now expressed as the template being ABSENT from the emitted
# module (count_tp_block is never reached because no `box_it` remains),
# while `box_it$i64` keeps its fully substituted body (examples above).
val (result, _) = run_monomorphization(make_modules())
val out = result["mono_body_subst_test"]
var templates = 0
for key in out.functions.keys():
    val f: HirFunction = out.functions[key]
    if f.name == "box_it":
        templates = templates + 1
expect(templates).to_equal(0)
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c5b129f2ad4976171ce606f11e48af8ff07837f49e2f9b24c480234e269379d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c5b129f2ad4976171ce606f11e48af8ff07837f49e2f9b24c480234e269379d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c5b129f2ad4976171ce606f11e48af8ff07837f49e2f9b24c480234e269379d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.spl
mirror: doc/06_spec/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.spl:255:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves no type parameter anywhere in the specialized body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.spl:263:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still leaves no type parameter in the specialized signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.spl:276:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes the consumed template rather than mutating it in place' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
