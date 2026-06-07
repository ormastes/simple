# Noalloc Checker Specification

> <details>

<!-- sdn-diagram:id=noalloc_checker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=noalloc_checker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

noalloc_checker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=noalloc_checker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Noalloc Checker Specification

## Scenarios

### noalloc checker — direct alloc detection

#### recognises 'new' as a direct allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_direct_alloc_expr("new")).to_equal(true)
```

</details>

#### recognises 'array_literal' as a direct allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_direct_alloc_expr("array_literal")).to_equal(true)
```

</details>

#### recognises 'dict_literal' as a direct allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_direct_alloc_expr("dict_literal")).to_equal(true)
```

</details>

#### recognises 'interpolation' as a direct allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_direct_alloc_expr("interpolation")).to_equal(true)
```

</details>

#### recognises 'string_concat' as a direct allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_direct_alloc_expr("string_concat")).to_equal(true)
```

</details>

#### does not flag 'call' as a direct allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_direct_alloc_expr("call")).to_equal(false)
```

</details>

#### does not flag 'literal_int' as a direct allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_direct_alloc_expr("literal_int")).to_equal(false)
```

</details>

#### does not flag empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_direct_alloc_expr("")).to_equal(false)
```

</details>

### noalloc checker — alloc descriptions

#### describes 'new' allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = test_direct_alloc_description("new")
expect(desc).to_contain("heap allocation")
```

</details>

#### describes 'array_literal' allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = test_direct_alloc_description("array_literal")
expect(desc).to_contain("array literal")
```

</details>

#### describes 'dict_literal' allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = test_direct_alloc_description("dict_literal")
expect(desc).to_contain("dict literal")
```

</details>

#### describes 'interpolation' allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = test_direct_alloc_description("interpolation")
expect(desc).to_contain("interpolation")
```

</details>

#### describes 'string_concat' allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = test_direct_alloc_description("string_concat")
expect(desc).to_contain("concatenation")
```

</details>

#### returns fallback for unknown tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = test_direct_alloc_description("unknown_tag")
expect(desc).to_contain("unknown")
```

</details>

### noalloc checker — family classification

#### returns false for empty module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_allocating_family_call("")).to_equal(false)
```

</details>

#### returns false for noalloc family module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_allocating_family_call("std.nogc_async_mut_noalloc.memory")).to_equal(false)
```

</details>

#### returns false for common family module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_allocating_family_call("std.common.text")).to_equal(false)
```

</details>

#### returns true for gc_async_mut family module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_allocating_family_call("std.gc_async_mut.gpu")).to_equal(true)
```

</details>

#### returns true for nogc_async_mut family module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_is_allocating_family_call("std.nogc_async_mut.actor")).to_equal(true)
```

</details>

### noalloc checker — capability manifest

#### starts empty with no noalloc fns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
expect(manifest_get_noalloc_fns(m).len()).to_equal(0)
```

</details>

#### registers and looks up a noalloc function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "boot_fn", true, false, "")
val entry = manifest_lookup(m2, "boot_fn")
expect(entry.is_noalloc).to_equal(true)
expect(entry.allocates).to_equal(false)
```

</details>

#### registers and looks up an allocating function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "heap_fn", false, true, "")
val entry = manifest_lookup(m2, "heap_fn")
expect(entry.is_noalloc).to_equal(false)
expect(entry.allocates).to_equal(true)
```

</details>

#### returns default entry for unknown function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val entry = manifest_lookup(m, "unknown_fn")
expect(entry.is_noalloc).to_equal(false)
expect(entry.allocates).to_equal(false)
```

</details>

#### get_noalloc_fns returns only noalloc-annotated names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "noalloc_fn", true, false, "")
val m3 = manifest_register(m2, "regular_fn", false, false, "")
val m4 = manifest_register(m3, "alloc_fn", false, true, "")
val noalloc_list = manifest_get_noalloc_fns(m4)
expect(noalloc_list.len()).to_equal(1)
expect(noalloc_list[0]).to_equal("noalloc_fn")
```

</details>

#### is_noalloc_fn returns true only for registered noalloc fns

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "safe_fn", true, false, "")
val m3 = manifest_register(m2, "other_fn", false, false, "")
expect(manifest_is_noalloc_fn(m3, "safe_fn")).to_equal(true)
expect(manifest_is_noalloc_fn(m3, "other_fn")).to_equal(false)
expect(manifest_is_noalloc_fn(m3, "missing_fn")).to_equal(false)
```

</details>

#### is_allocating_fn returns true for allocating fns

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "heap_fn", false, true, "")
val m3 = manifest_register(m2, "pure_fn", false, false, "")
expect(manifest_is_allocating_fn(m3, "heap_fn")).to_equal(true)
expect(manifest_is_allocating_fn(m3, "pure_fn")).to_equal(false)
```

</details>

### noalloc checker — violation detection

#### returns empty list for clean function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "pure_fn", false, false, "")
val violations = test_check_noalloc_violations("my_fn", [], ["pure_fn"], m2)
expect(violations.len()).to_equal(0)
```

</details>

#### catches direct new allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val violations = test_check_noalloc_violations("boot", ["new"], [], m)
expect(violations.len()).to_equal(1)
expect(violations[0].fn_name).to_equal("boot")
```

</details>

#### direct violation kind is DirectAlloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val violations = test_check_noalloc_violations("boot", ["array_literal"], [], m)
expect(violations.len()).to_equal(1)
val v = violations[0]
expect(v.kind).to_equal(KIND_DIRECT_ALLOC)
expect(v.detail).to_contain("array literal")
```

</details>

#### catches transitive call to allocating function

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "heap_fn", false, true, "")
val violations = test_check_noalloc_violations("my_fn", [], ["heap_fn"], m2)
expect(violations.len()).to_equal(1)
expect(violations[0].kind).to_equal(KIND_TRANSITIVE_CALL)
expect(violations[0].detail).to_contain("heap_fn")
```

</details>

#### does not flag call to pure function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "pure_fn", false, false, "")
val violations = test_check_noalloc_violations("my_fn", [], ["pure_fn"], m2)
expect(violations.len()).to_equal(0)
```

</details>

#### catches family-import violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "gpu_fn", false, false, "std.gc_async_mut.gpu")
val violations = test_check_noalloc_violations("my_fn", [], ["gpu_fn"], m2)
expect(violations.len()).to_equal(1)
expect(violations[0].kind).to_equal(KIND_FAMILY_IMPORT)
expect(violations[0].detail).to_contain("gpu_fn")
```

</details>

#### accumulates multiple direct violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val violations = test_check_noalloc_violations("boot", ["new", "array_literal", "dict_literal"], [], m)
expect(violations.len()).to_equal(3)
```

</details>

#### does not flag unknown callee (conservative — unknown not in manifest)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val violations = test_check_noalloc_violations("my_fn", [], ["unknown_fn"], m)
expect(violations.len()).to_equal(0)
```

</details>

#### noalloc family callee does not trigger family-import violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = manifest_new()
val m2 = manifest_register(m, "mem_fn", false, false, "std.nogc_async_mut_noalloc.memory")
val violations = test_check_noalloc_violations("my_fn", [], ["mem_fn"], m2)
expect(violations.len()).to_equal(0)
```

</details>

### noalloc checker — formatting

#### starts with error[noalloc]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = TestViolation(
    fn_name: "boot",
    kind: KIND_DIRECT_ALLOC,
    detail: "heap allocation via new",
    line: 0
)
val msg = test_format_violation(v)
expect(msg).to_contain("error[noalloc]")
```

</details>

#### includes fn_name in message

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = TestViolation(
    fn_name: "boot_init",
    kind: KIND_TRANSITIVE_CALL,
    detail: "call to allocating fn",
    line: 0
)
val msg = test_format_violation(v)
expect(msg).to_contain("boot_init")
```

</details>

#### includes line number when non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = TestViolation(
    fn_name: "boot",
    kind: KIND_DIRECT_ALLOC,
    detail: "heap allocation via new",
    line: 42
)
val msg = test_format_violation(v)
expect(msg).to_contain("42")
```

</details>

#### includes kind label direct-alloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = TestViolation(fn_name: "f", kind: KIND_DIRECT_ALLOC, detail: "new", line: 0)
val msg = test_format_violation(v)
expect(msg).to_contain("direct-alloc")
```

</details>

#### includes kind label transitive-call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = TestViolation(fn_name: "f", kind: KIND_TRANSITIVE_CALL, detail: "call to alloc_fn", line: 0)
val msg = test_format_violation(v)
expect(msg).to_contain("transitive-call")
```

</details>

#### includes kind label family-import

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = TestViolation(fn_name: "f", kind: KIND_FAMILY_IMPORT, detail: "call to gpu_fn", line: 0)
val msg = test_format_violation(v)
expect(msg).to_contain("family-import")
```

</details>

#### format_violations returns empty list for no violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val messages = test_format_violations([])
expect(messages.len()).to_equal(0)
```

</details>

#### format_violations returns one message per violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v1 = TestViolation(fn_name: "f1", kind: KIND_DIRECT_ALLOC, detail: "new", line: 0)
val v2 = TestViolation(fn_name: "f2", kind: KIND_TRANSITIVE_CALL, detail: "call", line: 0)
val messages = test_format_violations([v1, v2])
expect(messages.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/noalloc_checker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- noalloc checker — direct alloc detection
- noalloc checker — alloc descriptions
- noalloc checker — family classification
- noalloc checker — capability manifest
- noalloc checker — violation detection
- noalloc checker — formatting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
