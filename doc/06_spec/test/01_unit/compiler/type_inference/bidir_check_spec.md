# Bidir Check Specification

> <details>

<!-- sdn-diagram:id=bidir_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bidir_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bidir_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bidir_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bidir Check Specification

## Scenarios

### synthesize_expr

#### synthesizes integer literal type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# synthesize(42) => i64
pass
```

</details>

#### synthesizes boolean literal type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# synthesize(true) => bool
pass
```

</details>

#### synthesizes string literal type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# synthesize("hello") => text
pass
```

</details>

#### synthesizes array literal type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# synthesize([1, 2, 3]) => [i64]
pass
```

</details>

#### synthesizes lambda with inferred params

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# synthesize(\x: x + 1) => fn(Infer) -> Infer
# Without expected type, params are fresh type vars
pass
```

</details>

### check_expr

#### checks literal against matching type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check(42, i64) => Ok
pass
```

</details>

#### rejects literal against mismatched type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check(42, text) => Err(Mismatch)
pass
```

</details>

#### propagates function type into lambda params

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check(\x: x + 1, fn(i64) -> i64) => Ok
# x is inferred as i64 from expected type
pass
```

</details>

#### checks lambda body against expected return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check(\x: x, fn(i64) -> i64) => Ok
# check(\x: "hello", fn(i64) -> i64) => Err
pass
```

</details>

#### rejects lambda with wrong arity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check(\x, y: x + y, fn(i64) -> i64) => Err
# Expected 1 param, got 2
pass
```

</details>

#### handles nested lambdas with expected type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check(\f: \x: f(x), fn(fn(i64) -> i64) -> fn(i64) -> i64) => Ok
pass
```

</details>

### infer_expr_bidir

#### dispatches to synthesize in Synthesize mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# infer_expr_bidir(42, Synthesize) => Ok(i64)
pass
```

</details>

#### dispatches to check in Check mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# infer_expr_bidir(42, Check(i64)) => Ok(i64)
pass
```

</details>

#### returns expected type after successful check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# infer_expr_bidir(\x: x, Check(fn(i64) -> i64)) => Ok(fn(i64) -> i64)
pass
```

</details>

#### propagates error from failed check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# infer_expr_bidir(42, Check(text)) => Err
pass
```

</details>

### check_subsumes

#### accepts identical types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check_subsumes(i64, i64) => Ok
pass
```

</details>

#### accepts type variables that unify

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check_subsumes(T, i64) => Ok (T unified to i64)
pass
```

</details>

#### rejects incompatible types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check_subsumes(i64, text) => Err
pass
```

</details>

### lambda inference with bidirectional

#### infers lambda param from function argument position

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn apply(f: fn(i64) -> i64, x: i64): f(x)
# apply(\y: y * 2, 5) => y inferred as i64
pass
```

</details>

#### infers lambda param from assignment context

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val double: fn(i64) -> i64 = \x: x * 2
# x inferred as i64
pass
```

</details>

#### infers lambda param from return position

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn make_adder() -> fn(i64) -> i64:
#     \x: x + 1
# x inferred as i64
pass
```

</details>

#### chains bidirectional inference through multiple lambdas

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val compose: fn(fn(i64) -> i64, fn(i64) -> i64) -> fn(i64) -> i64
# compose(\x: x + 1, \y: y * 2)
# Both x and y inferred as i64
pass
```

</details>

### bidirectional error messages

#### reports expected vs found in check mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check(42, text) => "expected text, found i64"
pass
```

</details>

#### reports arity mismatch for lambdas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check(\x, y: x, fn(i64) -> i64) => "arity mismatch"
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/type_inference/bidir_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- synthesize_expr
- check_expr
- infer_expr_bidir
- check_subsumes
- lambda inference with bidirectional
- bidirectional error messages

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
