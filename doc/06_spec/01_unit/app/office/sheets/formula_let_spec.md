# formula_let_spec

> Calc LET (and immediately-invoked LAMBDA) spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_let_spec

Calc LET (and immediately-invoked LAMBDA) spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_let_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc LET (and immediately-invoked LAMBDA) spec.

LET(name1, value1, [name2, value2, ...], calculation) binds names on a
module-level binding stack (see formula.spl's _let_names/_let_values next to
the CARD 14 _formula_origin_key precedent) that is pushed right before
evaluating anything that might reference a name and popped again before
_eval_let returns, on every path (success or #ERR) — so bindings never leak
across sibling LET calls or across cells. Ground truths below are hand
computed (LET is pure arithmetic/binding, not a numeric-library function, so
there is no external reference table to check against beyond direct
computation).

LAMBDA ships IMMEDIATE-INVOCATION ONLY: `LAMBDA(x, x*2)(3)` = 6. A LAMBDA
stored in a name via LET and invoked later (`LET(f, LAMBDA(x,x*2), f(3))`)
would need a callable CellValue variant plumbed through the whole engine —
out of scope; it fails closed with #ERR (see the "LAMBDA must be immediately
invoked" case below) rather than shipping half-working callable semantics.

## Scenarios

### Calc LET basic binding

#### LET(x, 5, x*2) = 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x, 5, x*2)")).to_equal("10")
```

</details>

#### LET(x, 5, y, x+1, x*y) = 30

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x, 5, y, x+1, x*y)")).to_equal("30")
```

</details>

#### value1 can reference a cell: LET(x, A1, x+1) with A1=10 -> 11

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_with_a1("=LET(x, A1, x+1)", "10")).to_equal("11")
```

</details>

#### a bound name can be used more than once in the calculation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x, 3, x*x+x)")).to_equal("12")
```

</details>

#### value expressions may use string concatenation (full grammar, not just numeric)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(s, \"ab\"&\"c\", s)")).to_equal("abc")
```

</details>

### Calc LET scoping (no leakage, nesting, shadowing)

#### LET(x, 1, x) does not leak into a sibling LET(x, 2, x) in another cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x, 1, x)")).to_equal("1")
expect(_eval("=LET(x, 2, x)")).to_equal("2")
```

</details>

#### nested LET(x,1,LET(y,2,x+y)) = 3 (outer name visible inside inner)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x,1,LET(y,2,x+y))")).to_equal("3")
```

</details>

#### shadowing: LET(x,1,LET(x,5,x)) = 5 (innermost binding wins)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x,1,LET(x,5,x))")).to_equal("5")
```

</details>

#### after a nested LET returns, the outer binding is restored

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x,1,LET(x,5,x)) & \"-\" & LET(x,1,x)")).to_equal("5-1")
```

</details>

### Calc LET #ERR domains

#### a name matching a cell-ref pattern is rejected at bind time: LET(A1, 5, A1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(A1, 5, A1)")).to_contain("#ERR")
```

</details>

#### a name reusing a built-in function name is rejected: LET(SUM, 5, SUM)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(SUM, 5, SUM)")).to_contain("#ERR")
```

</details>

#### an even argument count (missing calculation) is #ERR: LET(x, 5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x, 5)")).to_contain("#ERR")
```

</details>

#### an even argument count (two pairs, no calculation) is #ERR: LET(x,5,y,6)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x,5,y,6)")).to_contain("#ERR")
```

</details>

#### LET with no arguments is #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET()")).to_contain("#ERR")
```

</details>

### Calc LAMBDA (immediate invocation only)

#### LAMBDA(x, x*2)(3) = 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LAMBDA(x, x*2)(3)")).to_equal("6")
```

</details>

#### LAMBDA(x, y, x+y)(2, 5) = 7 (multi-parameter)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LAMBDA(x, y, x+y)(2, 5)")).to_equal("7")
```

</details>

#### LAMBDA composes with LET's value expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(f, LAMBDA(x, x*2)(3), f+1)")).to_equal("7")
```

</details>

#### a LAMBDA not immediately invoked is unsupported and fails closed with #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LAMBDA(x, x*2)")).to_contain("#ERR")
```

</details>

#### LAMBDA arity mismatch (too few invocation arguments) is #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LAMBDA(x, y, x+y)(2)")).to_contain("#ERR")
```

</details>

### Calc LET deliberate-fail probe tail marker

#### tail of the file executes: LET(x, 5, x*2) still = 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LET(x, 5, x*2)")).to_equal("10")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
