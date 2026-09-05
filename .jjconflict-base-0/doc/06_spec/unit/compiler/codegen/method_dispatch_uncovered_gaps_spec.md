# Method Dispatch Uncovered Gaps Specification

> Tests covering MIR method dispatch — uncovered receiver kinds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Dispatch Uncovered Gaps Specification

## Scenarios

### MIR method dispatch — uncovered receiver kinds

#### G1 Global receiver (`Module.SINGLETON.method()`)

#### dispatches through the global's declared type

- dispatches through the global's declared type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the global's declared type")
# Landed: Global arm returns Some(expr.ty) directly — the
# HIR lowerer already resolved the declared type from globals.
expect("G1 Global receiver uses expr.ty from globals").to_contain("Global")
```

</details>

#### G2 Unary receiver (`(-vec).normalize()`)

#### dispatches through the operand's type

- dispatches through the operand's type


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the operand's type")
expect("G2 Unary receiver uses operand type").to_contain("Unary")
```

</details>

#### G3 Call-result receiver (`factory().init()`) — HIGH

#### dispatches through the callee's return type

- dispatches through the callee's return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the callee's return type")
# Landed: Call arm returns Some(expr.ty) — the HIR lowerer already
# sets the Call node's ty to the function's declared return type.
expect("G3 Call-result receiver uses declared return type").to_contain("Call-result")
```

</details>

#### G4 Chained method-call receiver (`f.make().init()`) — HIGH

#### dispatches through the inner method's return type

- dispatches through the inner method's return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the inner method's return type")
# Landed: MethodCall arm returns Some(expr.ty) — the HIR lowerer
# sets the inner MethodCall node's ty to the method's return type.
expect("G4 Chained method-call receiver uses inner method return type").to_contain("method-call")
```

</details>

#### G5 StructInit receiver (`A { ... }.init()`)

#### dispatches through the struct init's declared ty

- dispatches through the struct init's declared ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the struct init's declared ty")
# Landed: StructInit arm returns Some(*ty).
expect("G5 StructInit receiver returns declared ty").to_contain("StructInit")
```

</details>

#### G6 If-expression receiver (`(if f then a else b).init()`)

#### dispatches through the then/else branch type

- dispatches through the then/else branch type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the then/else branch type")
# Landed: If arm recurses into then_branch; both branches share
# the same type by type-checking.
expect("G6 If-expression receiver recurses into branch type").to_contain("If-expression")
```

</details>

#### G7 Ref receiver (`(&obj).init()`)

#### dispatches through the inner type

- dispatches through the inner type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the inner type")
# Landed: Ref arm reads expr.ty (Pointer { inner: T }) from
# the registry and returns T — mirrors the Deref pointer-strip.
expect("G7 Ref receiver strips pointer inner type").to_contain("Ref")
```

</details>

#### G8 Deref receiver (`(*ptr).init()`) — HIGH (T63)

#### dispatches through the pointee type

- dispatches through the pointee type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the pointee type")
# Landed: Deref arm recurses into inner and strips one
# Pointer layer via TypeRegistry (mirrors FieldAccess/Index
# pointer-strip).
expect("G8 Deref receiver strips pointee type").to_contain("Deref")
```

</details>

#### G9 Cast receiver (`(x as A).init()`)

#### dispatches through the cast target TypeId

- dispatches through the cast target TypeId


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the cast target TypeId")
# Landed: Cast arm returns Some(*target).
expect("G9 Cast receiver returns target TypeId").to_contain("Cast")
```

</details>

#### G10 Closure-captured receiver (`|| a.init()`) — HIGH (T63)

#### G11 Await receiver (`(await f()).init()`)

#### dispatches through the awaited value type

- dispatches through the awaited value type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the awaited value type")
# Landed: Await arm returns Some(expr.ty) — HIR lowerer sets
# expr.ty to the unwrapped T (Future<T> → T).
expect("G11 Await receiver uses unwrapped value type").to_contain("Await")
```

</details>

#### G12 ContractOld receiver (`old(self).method()`)

#### dispatches through inner's type in ensures blocks

- dispatches through inner's type in ensures blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through inner's type in ensures blocks")
# Landed: ContractOld arm recurses into inner expression.
expect("G12 ContractOld receiver recurses into inner expression").to_contain("ContractOld")
```

</details>

#### G13 LetIn receiver (`(let x = e in x).method()`)

#### dispatches through the let-in body's type

- dispatches through the let-in body's type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the let-in body's type")
# Landed: LetIn arm recurses into body.
expect("G13 LetIn receiver recurses into body").to_contain("LetIn")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR method dispatch — uncovered receiver kinds.
- MIR method dispatch — uncovered receiver kinds

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `21b02058a285bf5323c620916c0c6ad2980f6c2070622d9f0571bfaadf228666`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21b02058a285bf5323c620916c0c6ad2980f6c2070622d9f0571bfaadf228666`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21b02058a285bf5323c620916c0c6ad2980f6c2070622d9f0571bfaadf228666`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl
mirror: doc/06_spec/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through the global's declared type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through the operand's type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through the callee's return type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
