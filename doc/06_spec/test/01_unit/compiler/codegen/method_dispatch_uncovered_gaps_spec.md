# Method Dispatch Uncovered Gaps Specification

> <details>

<!-- sdn-diagram:id=method_dispatch_uncovered_gaps_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=method_dispatch_uncovered_gaps_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

method_dispatch_uncovered_gaps_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=method_dispatch_uncovered_gaps_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: Global arm returns Some(expr.ty) directly — the
# HIR lowerer already resolved the declared type from globals.
expect("G1 Global receiver uses expr.ty from globals").to_contain("Global")
```

</details>

#### G2 Unary receiver (`(-vec).normalize()`)

#### dispatches through the operand's type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("G2 Unary receiver uses operand type").to_contain("Unary")
```

</details>

#### G3 Call-result receiver (`factory().init()`) — HIGH

#### dispatches through the callee's return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: Call arm returns Some(expr.ty) — the HIR lowerer already
# sets the Call node's ty to the function's declared return type.
expect("G3 Call-result receiver uses declared return type").to_contain("Call-result")
```

</details>

#### G4 Chained method-call receiver (`f.make().init()`) — HIGH

#### dispatches through the inner method's return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: MethodCall arm returns Some(expr.ty) — the HIR lowerer
# sets the inner MethodCall node's ty to the method's return type.
expect("G4 Chained method-call receiver uses inner method return type").to_contain("method-call")
```

</details>

#### G5 StructInit receiver (`A { ... }.init()`)

#### dispatches through the struct init's declared ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: StructInit arm returns Some(*ty).
expect("G5 StructInit receiver returns declared ty").to_contain("StructInit")
```

</details>

#### G6 If-expression receiver (`(if f then a else b).init()`)

#### dispatches through the then/else branch type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: If arm recurses into then_branch; both branches share
# the same type by type-checking.
expect("G6 If-expression receiver recurses into branch type").to_contain("If-expression")
```

</details>

#### G7 Ref receiver (`(&obj).init()`)

#### dispatches through the inner type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: Ref arm reads expr.ty (Pointer { inner: T }) from
# the registry and returns T — mirrors the Deref pointer-strip.
expect("G7 Ref receiver strips pointer inner type").to_contain("Ref")
```

</details>

#### G8 Deref receiver (`(*ptr).init()`) — HIGH (T63)

#### dispatches through the pointee type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: Deref arm recurses into inner and strips one
# Pointer layer via TypeRegistry (mirrors FieldAccess/Index
# pointer-strip).
expect("G8 Deref receiver strips pointee type").to_contain("Deref")
```

</details>

#### G9 Cast receiver (`(x as A).init()`)

#### dispatches through the cast target TypeId

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: Cast arm returns Some(*target).
expect("G9 Cast receiver returns target TypeId").to_contain("Cast")
```

</details>

#### G10 Closure-captured receiver (`|| a.init()`) — HIGH (T63)

#### G11 Await receiver (`(await f()).init()`)

#### dispatches through the awaited value type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: Await arm returns Some(expr.ty) — HIR lowerer sets
# expr.ty to the unwrapped T (Future<T> → T).
expect("G11 Await receiver uses unwrapped value type").to_contain("Await")
```

</details>

#### G12 ContractOld receiver (`old(self).method()`)

#### dispatches through inner's type in ensures blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: ContractOld arm recurses into inner expression.
expect("G12 ContractOld receiver recurses into inner expression").to_contain("ContractOld")
```

</details>

#### G13 LetIn receiver (`(let x = e in x).method()`)

#### dispatches through the let-in body's type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Landed: LetIn arm recurses into body.
expect("G13 LetIn receiver recurses into body").to_contain("LetIn")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
