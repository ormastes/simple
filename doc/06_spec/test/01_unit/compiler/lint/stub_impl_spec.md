# Stub Implementation Lint Specification

> Tests the STUB001/STUB002 lint that detects functions with trivial/dummy implementations — bare literals like 0, "", false, nil without parameter usage.

<!-- sdn-diagram:id=stub_impl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stub_impl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stub_impl_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stub_impl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stub Implementation Lint Specification

Tests the STUB001/STUB002 lint that detects functions with trivial/dummy implementations — bare literals like 0, "", false, nil without parameter usage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STUB-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/lint/stub_impl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the STUB001/STUB002 lint that detects functions with trivial/dummy
implementations — bare literals like 0, "", false, nil without parameter usage.

## Key Concepts

| Concept | Description |
|---------|-------------|
| STUB001 | Function with params returns trivial value, params unused |
| STUB002 | Zero-param function returns default value (possible stub) |
| Trivial | A bare literal or default value as entire function body |
| Default | Zero-values: 0, "", false, nil, [], {} |

## Scenarios

### STUB001 — Trivial return with unused params

#### when function returns bare 0 with unused params

#### emits STUB001 warning

1. ast reset
   - Expected: stub001.len() equals `1`
   - Expected: stub001[0].fn_name equals `gc_malloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(0, 0)
val d = make_fn_with_body("gc_malloc", ["size"], e)
val ws = check_stub_impl([d])
expect(ws.len()).to_be_greater_than(0)
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
expect(stub001[0].fn_name).to_equal("gc_malloc")
```

</details>

#### when function returns empty string with unused params

#### emits STUB001 warning

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_string_lit("", 0)
val d = make_fn_with_body("load_config", ["path"], e)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

#### when function returns false with unused params

#### emits STUB001 warning

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_bool_lit(0, 0)
val d = make_fn_with_body("is_supported", ["feature"], e)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

#### when function returns nil with unused params

#### emits STUB001 warning

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_nil_lit(0)
val d = make_fn_with_body("find_item", ["name"], e)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

#### when function returns empty array with unused params

#### emits STUB001 warning

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_array_lit([], 0)
val d = make_fn_with_body("tokenize", ["src"], e)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

#### when function returns non-zero literal with unused params

#### emits STUB001 for any literal when params unused

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(42, 0)
val d = make_fn_with_body("compute", ["x"], e)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

#### when function returns non-empty string with unused params

#### emits STUB001 (constant string ignoring params)

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_string_lit("GET", 0)
val d = make_fn_with_body("get_method", ["request"], e)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

#### when function returns true with unused params

#### emits STUB001

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_bool_lit(1, 0)
val d = make_fn_with_body("supports_target", ["target"], e)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

#### when explicit return with unused params

#### emits STUB001 for return 0

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(0, 0)
val d = make_fn_with_return("process", ["data"], e)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

#### when Ok(nil) with unused params

#### emits STUB001

1. ast reset
   - Expected: stub001.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val nil_e = expr_nil_lit(0)
val ok_callee = expr_ident("Ok", 0)
val ok_call = expr_call(ok_callee, [nil_e], 0)
val d = make_fn_with_body("run_backend", ["module"], ok_call)
val ws = check_stub_impl([d])
val stub001 = find_warnings_by_code(ws, "STUB001")
expect(stub001.len()).to_equal(1)
```

</details>

### STUB002 — Zero-param default return

#### when zero-param function returns 0

#### emits STUB002 info

1. ast reset
   - Expected: stub002.len() equals `1`
   - Expected: stub002[0].severity equals `INFO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(0, 0)
val d = make_fn_with_body("get_count", [], e)
val ws = check_stub_impl([d])
val stub002 = find_warnings_by_code(ws, "STUB002")
expect(stub002.len()).to_equal(1)
expect(stub002[0].severity).to_equal("INFO")
```

</details>

#### when zero-param function returns empty string

#### emits STUB002 info

1. ast reset
   - Expected: stub002.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_string_lit("", 0)
val d = make_fn_with_body("get_name", [], e)
val ws = check_stub_impl([d])
val stub002 = find_warnings_by_code(ws, "STUB002")
expect(stub002.len()).to_equal(1)
```

</details>

#### when zero-param function returns false

#### emits STUB002 info

1. ast reset
   - Expected: stub002.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_bool_lit(0, 0)
val d = make_fn_with_body("is_ready", [], e)
val ws = check_stub_impl([d])
val stub002 = find_warnings_by_code(ws, "STUB002")
expect(stub002.len()).to_equal(1)
```

</details>

#### when zero-param function returns nil

#### emits STUB002 info

1. ast reset
   - Expected: stub002.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_nil_lit(0)
val d = make_fn_with_body("get_cache", [], e)
val ws = check_stub_impl([d])
val stub002 = find_warnings_by_code(ws, "STUB002")
expect(stub002.len()).to_equal(1)
```

</details>

#### when zero-param function returns non-zero constant

#### does NOT emit STUB002 (legitimate constant)

1. ast reset
   - Expected: stub002.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(42, 0)
val d = make_fn_with_body("max_retries", [], e)
val ws = check_stub_impl([d])
val stub002 = find_warnings_by_code(ws, "STUB002")
expect(stub002.len()).to_equal(0)
```

</details>

#### when zero-param function returns non-empty string

#### does NOT emit STUB002 (legitimate constant)

1. ast reset
   - Expected: stub002.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_string_lit("GET", 0)
val d = make_fn_with_body("method_get", [], e)
val ws = check_stub_impl([d])
val stub002 = find_warnings_by_code(ws, "STUB002")
expect(stub002.len()).to_equal(0)
```

</details>

#### when zero-param function returns true

#### does NOT emit STUB002 (legitimate constant)

1. ast reset
   - Expected: stub002.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_bool_lit(1, 0)
val d = make_fn_with_body("is_enabled", [], e)
val ws = check_stub_impl([d])
val stub002 = find_warnings_by_code(ws, "STUB002")
expect(stub002.len()).to_equal(0)
```

</details>

### Stub Impl Lint — No Warning Cases

#### when function uses its parameters

#### does NOT warn

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val param_ref = expr_ident("x", 0)
val d = make_fn_with_body("identity", ["x"], param_ref)
val ws = check_stub_impl([d])
expect(ws.len()).to_equal(0)
```

</details>

#### when function has noop marker

#### does NOT warn

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass(0)
val d = make_fn_with_body("not_yet", ["data"], e)
val ws = check_stub_impl([d])
expect(ws.len()).to_equal(0)
```

</details>

#### when function body is explicit pass_do_nothing placeholder

#### emits STUB003

1. ast reset
   - Expected: stub003.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass_do_nothing("intentional", 0)
val d = make_fn_with_body("noop_handler", ["event"], e)
val ws = check_stub_impl([d])
val stub003 = find_warnings_by_code(ws, "STUB003")
expect(stub003.len()).to_equal(1)
```

</details>

#### when function body is explicit pass_todo placeholder

#### emits STUB003

1. ast reset
   - Expected: stub003.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val placeholder = expr_pass_todo("todo migration marker", 0)
val d = make_fn_with_body("not_done_yet", ["value"], placeholder)
val ws = check_stub_impl([d])
val stub003 = find_warnings_by_code(ws, "STUB003")
expect(stub003.len()).to_equal(1)
```

</details>

#### when function name starts with _noop_

#### does NOT warn

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(0, 0)
val d = make_fn_with_body("_noop_load", ["path"], e)
val ws = check_stub_impl([d])
expect(ws.len()).to_equal(0)
```

</details>

#### when function has multi-statement body

#### does NOT warn (not a single-expression stub)

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e1 = expr_int_lit(1, 0)
val e2 = expr_int_lit(0, 0)
val s1 = stmt_expr_stmt(e1, 0)
val s2 = stmt_expr_stmt(e2, 0)
val param_types: [i64] = [0]
val d = decl_fn("multi_stmt", ["x"], param_types, 0, [s1, s2], 0, [], 0)
val ws = check_stub_impl([d])
expect(ws.len()).to_equal(0)
```

</details>

#### when extern fn (no body)

#### does NOT warn

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val d = decl_extern_fn("rt_read", ["path"], [0], 0, [], 0)
val ws = check_stub_impl([d])
expect(ws.len()).to_equal(0)
```

</details>

#### when function body is complex expression

#### does NOT warn for binary op

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val left = expr_ident("x", 0)
val right = expr_int_lit(2, 0)
val e = expr_binary(60, left, right, 0)
val d = make_fn_with_body("double", ["x"], e)
val ws = check_stub_impl([d])
expect(ws.len()).to_equal(0)
```

</details>

#### when function body is method call

#### does NOT warn

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val recv = expr_ident("items", 0)
val e = expr_method_call(recv, "len", [], 0)
val d = make_fn_with_body("count", ["items"], e)
val ws = check_stub_impl([d])
expect(ws.len()).to_equal(0)
```

</details>

### Stub Impl Lint — classify_trivial

#### classifies int literal

1. ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(0, 0)
val kind = classify_trivial(e)
expect(kind).to_contain("integer")
```

</details>

#### classifies empty string

1. ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_string_lit("", 0)
val kind = classify_trivial(e)
expect(kind).to_contain("empty string")
```

</details>

#### classifies non-empty string

1. ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_string_lit("hello", 0)
val kind = classify_trivial(e)
expect(kind).to_contain("string")
```

</details>

#### classifies bool false

1. ast reset
   - Expected: kind equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_bool_lit(0, 0)
val kind = classify_trivial(e)
expect(kind).to_equal("false")
```

</details>

#### classifies bool true

1. ast reset
   - Expected: kind equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_bool_lit(1, 0)
val kind = classify_trivial(e)
expect(kind).to_equal("true")
```

</details>

#### classifies nil

1. ast reset
   - Expected: kind equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_nil_lit(0)
val kind = classify_trivial(e)
expect(kind).to_equal("nil")
```

</details>

#### classifies empty array

1. ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_array_lit([], 0)
val kind = classify_trivial(e)
expect(kind).to_contain("empty array")
```

</details>

#### rejects non-empty array

1. ast reset
   - Expected: kind equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val elem = expr_int_lit(1, 0)
val e = expr_array_lit([elem], 0)
val kind = classify_trivial(e)
expect(kind).to_equal("")
```

</details>

#### classifies unit

1. ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_unit(0)
val kind = classify_trivial(e)
expect(kind).to_contain("unit")
```

</details>

#### classifies pass

1. ast reset
   - Expected: kind equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_pass(0)
val kind = classify_trivial(e)
expect(kind).to_equal("pass")
```

</details>

#### rejects complex expression (binary)

1. ast reset
   - Expected: kind equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val left = expr_int_lit(1, 0)
val right = expr_int_lit(2, 0)
val e = expr_binary(60, left, right, 0)
val kind = classify_trivial(e)
expect(kind).to_equal("")
```

</details>

### Stub Impl Lint — is_default_value

#### 0 is default

1. ast reset
   - Expected: is_default_value(e) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(0, 0)
expect(is_default_value(e)).to_equal(true)
```

</details>

#### 42 is NOT default

1. ast reset
   - Expected: is_default_value(e) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_int_lit(42, 0)
expect(is_default_value(e)).to_equal(false)
```

</details>

#### empty string is default

1. ast reset
   - Expected: is_default_value(e) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_string_lit("", 0)
expect(is_default_value(e)).to_equal(true)
```

</details>

#### non-empty string is NOT default

1. ast reset
   - Expected: is_default_value(e) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_string_lit("hello", 0)
expect(is_default_value(e)).to_equal(false)
```

</details>

#### false is default

1. ast reset
   - Expected: is_default_value(e) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_bool_lit(0, 0)
expect(is_default_value(e)).to_equal(true)
```

</details>

#### true is NOT default

1. ast reset
   - Expected: is_default_value(e) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_bool_lit(1, 0)
expect(is_default_value(e)).to_equal(false)
```

</details>

#### nil is default

1. ast reset
   - Expected: is_default_value(e) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_nil_lit(0)
expect(is_default_value(e)).to_equal(true)
```

</details>

#### empty array is default

1. ast reset
   - Expected: is_default_value(e) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val e = expr_array_lit([], 0)
expect(is_default_value(e)).to_equal(true)
```

</details>

#### non-empty array is NOT default

1. ast reset
   - Expected: is_default_value(e) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val elem = expr_int_lit(1, 0)
val e = expr_array_lit([elem], 0)
expect(is_default_value(e)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
