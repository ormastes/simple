# Callback Trampoline Specification

> Tests the callback trampoline generation module that converts C function pointer types to Simple-callable patterns. Covers type classification, naming, parsing, and C code emission.

<!-- sdn-diagram:id=callback_trampoline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=callback_trampoline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

callback_trampoline_spec -> std
callback_trampoline_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=callback_trampoline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Callback Trampoline Specification

Tests the callback trampoline generation module that converts C function pointer types to Simple-callable patterns. Covers type classification, naming, parsing, and C code emission.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR #SFFI-CALLBACK #WS5 |
| Category | Compiler / Backend / Callback Trampoline |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/compiler/backend/callback_trampoline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the callback trampoline generation module that converts C function
pointer types to Simple-callable patterns. Covers type classification,
naming, parsing, and C code emission.

v1 scope: stateless function pointers only (no closures with captures).

## Scenarios

### callback trampoline

### is_callback_type

#### accepts plain function pointer types

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_callback_type("Fn<(i64) -> i64>")).to_equal(true)
```

</details>

#### accepts multi-param function pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_callback_type("Fn<(i64, f64) -> bool>")).to_equal(true)
```

</details>

#### accepts no-arg function pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_callback_type("Fn<() -> void>")).to_equal(true)
```

</details>

#### rejects closures with captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_callback_type("Fn<(i64) -> i64>[x, y]")).to_equal(false)
```

</details>

#### rejects non-function types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_callback_type("i64")).to_equal(false)
expect(is_callback_type("text")).to_equal(false)
expect(is_callback_type("List<i64>")).to_equal(false)
```

</details>

### is_closure_with_captures

#### detects closures with capture lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_closure_with_captures("Fn<(i64) -> i64>[x, y]")).to_equal(true)
```

</details>

#### rejects plain function pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_closure_with_captures("Fn<(i64) -> i64>")).to_equal(false)
```

</details>

#### rejects non-function types

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_closure_with_captures("i64")).to_equal(false)
```

</details>

### callback_typedef_name

#### generates name for single-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = callback_typedef_name(["i64"], "i64")
expect(name).to_equal("spl_callback_i64_to_i64")
```

</details>

#### generates name for multi-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = callback_typedef_name(["i64", "f64"], "bool")
expect(name).to_equal("spl_callback_i64_f64_to_bool")
```

</details>

#### generates name for void-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = callback_typedef_name([], "void")
expect(name).to_equal("spl_callback_void_to_void")
```

</details>

### extract_callback_params

#### extracts single parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = extract_callback_params("Fn<(i64) -> i64>")
expect(params.len()).to_equal(1)
expect(params[0]).to_equal("i64")
```

</details>

#### extracts multiple parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = extract_callback_params("Fn<(i64, f64) -> bool>")
expect(params.len()).to_equal(2)
expect(params[0]).to_equal("i64")
expect(params[1]).to_equal("f64")
```

</details>

#### returns empty list for no-arg function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = extract_callback_params("Fn<() -> void>")
expect(params.len()).to_equal(0)
```

</details>

### extract_callback_return

#### extracts return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret = extract_callback_return("Fn<(i64) -> bool>")
expect(ret).to_equal("bool")
```

</details>

#### extracts void return

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret = extract_callback_return("Fn<() -> void>")
expect(ret).to_equal("void")
```

</details>

#### extracts i64 return

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret = extract_callback_return("Fn<(i64, f64) -> i64>")
expect(ret).to_equal("i64")
```

</details>

### emit_callback_typedef

#### generates correct C typedef for single-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = CallbackTypedef(
    name: "spl_callback_i64_to_i64",
    return_type: "int64_t",
    param_types: ["int64_t"]
)
val result = emit_callback_typedef(cb)
expect(result).to_equal("typedef int64_t (*spl_callback_i64_to_i64)(int64_t);")
```

</details>

#### generates correct C typedef for multi-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = CallbackTypedef(
    name: "spl_callback_i64_f64_to_bool",
    return_type: "int64_t",
    param_types: ["int64_t", "double"]
)
val result = emit_callback_typedef(cb)
expect(result).to_equal("typedef int64_t (*spl_callback_i64_f64_to_bool)(int64_t, double);")
```

</details>

#### generates void param list for no-arg callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = CallbackTypedef(
    name: "spl_callback_void_to_void",
    return_type: "void",
    param_types: []
)
val result = emit_callback_typedef(cb)
expect(result).to_equal("typedef void (*spl_callback_void_to_void)(void);")
```

</details>

### emit_callback_trampoline

#### generates null-check and invocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = CallbackTypedef(
    name: "spl_callback_i64_to_i64",
    return_type: "int64_t",
    param_types: ["int64_t"]
)
val result = emit_callback_trampoline("_spl_trampoline_test", cb)
expect(result).to_contain("if (!_cb)")
expect(result).to_contain("return _cb(_a0)")
```

</details>

#### generates void return for void callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = CallbackTypedef(
    name: "spl_callback_void_to_void",
    return_type: "void",
    param_types: []
)
val result = emit_callback_trampoline("_spl_trampoline_void", cb)
expect(result).to_contain("if (!_cb)")
expect(result).to_contain("_cb()")
```

</details>

### build_callback_typedef

#### builds typedef from Fn type string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = build_callback_typedef("Fn<(i64) -> i64>")
expect(cb.name).to_contain("spl_callback")
expect(cb.return_type).to_equal("int64_t")
expect(cb.param_types.len()).to_equal(1)
expect(cb.param_types[0]).to_equal("int64_t")
```

</details>

#### builds typedef from multi-param Fn type

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = build_callback_typedef("Fn<(i64, f64) -> bool>")
expect(cb.return_type).to_equal("int64_t")
expect(cb.param_types.len()).to_equal(2)
expect(cb.param_types[0]).to_equal("int64_t")
expect(cb.param_types[1]).to_equal("double")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
