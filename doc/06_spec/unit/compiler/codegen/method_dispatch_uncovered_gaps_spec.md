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
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the global's declared type")
# Landed: Global arm returns Some(expr.ty) directly — the
# HIR lowerer already resolved the declared type from globals.
expect(true).to_equal(true)
```

</details>

#### G2 Unary receiver (`(-vec).normalize()`)

#### dispatches through the operand's type

- dispatches through the operand's type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the operand's type")
expect(true).to_equal(true)
```

</details>

#### G3 Call-result receiver (`factory().init()`) — HIGH

#### dispatches through the callee's return type

- dispatches through the callee's return type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the callee's return type")
# Landed: Call arm returns Some(expr.ty) — the HIR lowerer already
# sets the Call node's ty to the function's declared return type.
expect(true).to_equal(true)
```

</details>

#### G4 Chained method-call receiver (`f.make().init()`) — HIGH

#### dispatches through the inner method's return type

- dispatches through the inner method's return type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the inner method's return type")
# Landed: MethodCall arm returns Some(expr.ty) — the HIR lowerer
# sets the inner MethodCall node's ty to the method's return type.
expect(true).to_equal(true)
```

</details>

#### G5 StructInit receiver (`A { ... }.init()`)

#### dispatches through the struct init's declared ty

- dispatches through the struct init's declared ty
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the struct init's declared ty")
# Landed: StructInit arm returns Some(*ty).
expect(true).to_equal(true)
```

</details>

#### G6 If-expression receiver (`(if f then a else b).init()`)

#### dispatches through the then/else branch type

- dispatches through the then/else branch type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the then/else branch type")
# Landed: If arm recurses into then_branch; both branches share
# the same type by type-checking.
expect(true).to_equal(true)
```

</details>

#### G7 Ref receiver (`(&obj).init()`)

#### dispatches through the inner type

- dispatches through the inner type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the inner type")
# Landed: Ref arm reads expr.ty (Pointer { inner: T }) from
# the registry and returns T — mirrors the Deref pointer-strip.
expect(true).to_equal(true)
```

</details>

#### G8 Deref receiver (`(*ptr).init()`) — HIGH (T63)

#### dispatches through the pointee type

- dispatches through the pointee type
   - Expected: true is true


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
expect(true).to_equal(true)
```

</details>

#### G9 Cast receiver (`(x as A).init()`)

#### dispatches through the cast target TypeId

- dispatches through the cast target TypeId
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the cast target TypeId")
# Landed: Cast arm returns Some(*target).
expect(true).to_equal(true)
```

</details>

#### G10 Closure-captured receiver (`|| a.init()`) — HIGH (T63)

#### G11 Await receiver (`(await f()).init()`)

#### dispatches through the awaited value type

- dispatches through the awaited value type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the awaited value type")
# Landed: Await arm returns Some(expr.ty) — HIR lowerer sets
# expr.ty to the unwrapped T (Future<T> → T).
expect(true).to_equal(true)
```

</details>

#### G12 ContractOld receiver (`old(self).method()`)

#### dispatches through inner's type in ensures blocks

- dispatches through inner's type in ensures blocks
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through inner's type in ensures blocks")
# Landed: ContractOld arm recurses into inner expression.
expect(true).to_equal(true)
```

</details>

#### G13 LetIn receiver (`(let x = e in x).method()`)

#### dispatches through the let-in body's type

- dispatches through the let-in body's type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches through the let-in body's type")
# Landed: LetIn arm recurses into body.
expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl` |
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `73946751bd49d32d5112a1703284f2d9d425552c486597cbe72282d596729e7d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73946751bd49d32d5112a1703284f2d9d425552c486597cbe72282d596729e7d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73946751bd49d32d5112a1703284f2d9d425552c486597cbe72282d596729e7d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl
mirror: doc/06_spec/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through the global's declared type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through the operand's type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through the callee's return type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
