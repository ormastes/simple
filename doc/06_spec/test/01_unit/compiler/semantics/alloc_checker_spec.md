# Alloc Checker Specification

> <details>

<!-- sdn-diagram:id=alloc_checker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=alloc_checker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

alloc_checker_spec -> std
alloc_checker_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=alloc_checker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Alloc Checker Specification

## Scenarios

### Noalloc Checker

### is_direct_alloc_expr

#### recognizes new as direct alloc

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(is_direct_alloc_expr("new"))
```

</details>

#### recognizes array_literal as direct alloc

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(is_direct_alloc_expr("array_literal"))
```

</details>

#### recognizes dict_literal as direct alloc

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(is_direct_alloc_expr("dict_literal"))
```

</details>

#### recognizes interpolation as direct alloc

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(is_direct_alloc_expr("interpolation"))
```

</details>

#### recognizes string_concat as direct alloc

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(is_direct_alloc_expr("string_concat"))
```

</details>

#### does not flag plain call as direct alloc

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_false(is_direct_alloc_expr("call"))
```

</details>

#### does not flag arithmetic as direct alloc

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_false(is_direct_alloc_expr("add"))
```

</details>

### direct_alloc_description

#### returns non-empty description for new

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = direct_alloc_description("new")
expect(desc.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty description for array_literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = direct_alloc_description("array_literal")
expect(desc.len()).to_be_greater_than(0)
```

</details>

### NoallocCapabilityManifest

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
expect(m.get_noalloc_fns().len()).to_equal(0)
```

</details>

#### registers and looks up a function

- m register
- assert true
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
m.register("my_fn", true, false, "")
assert_true(m.is_noalloc_fn("my_fn"))
assert_false(m.is_allocating_fn("my_fn"))
```

</details>

#### unknown function is not noalloc and not allocating

- assert false
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
assert_false(m.is_noalloc_fn("unknown"))
assert_false(m.is_allocating_fn("unknown"))
```

</details>

#### get_noalloc_fns returns only noalloc-annotated fns

- m register
- m register
   - Expected: fns.len() equals `1`
   - Expected: fns[0] equals `noalloc_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
m.register("noalloc_fn", true, false, "")
m.register("plain_fn", false, false, "")
val fns = m.get_noalloc_fns()
expect(fns.len()).to_equal(1)
expect(fns[0]).to_equal("noalloc_fn")
```

</details>

### check_noalloc_violations

#### detects DirectAlloc via new tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
val violations = check_noalloc_violations("boot_fn", ["new"], [], m)
expect(violations.len()).to_equal(1)
expect(violations[0].fn_name).to_equal("boot_fn")
```

</details>

#### detects DirectAlloc via array_literal tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
val violations = check_noalloc_violations("isr_fn", ["array_literal"], [], m)
expect(violations.len()).to_equal(1)
```

</details>

#### detects TransitiveCall to allocating function

- m register
   - Expected: violations.len() equals `1`
   - Expected: violations[0].fn_name equals `noalloc_caller`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
m.register("alloc_helper", false, true, "")
val violations = check_noalloc_violations("noalloc_caller", [], ["alloc_helper"], m)
expect(violations.len()).to_equal(1)
expect(violations[0].fn_name).to_equal("noalloc_caller")
```

</details>

#### clean function with non-allocating callee has no violations

- m register
   - Expected: violations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
m.register("pure_fn", false, false, "")
val violations = check_noalloc_violations("safe_fn", [], ["pure_fn"], m)
expect(violations.len()).to_equal(0)
```

</details>

#### clean function with no body has no violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
val violations = check_noalloc_violations("empty_fn", [], [], m)
expect(violations.len()).to_equal(0)
```

</details>

#### multiple direct alloc tags produce multiple violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
val violations = check_noalloc_violations("multi_fn", ["new", "array_literal"], [], m)
expect(violations.len()).to_equal(2)
```

</details>

#### violation kind is DirectAlloc for new tag

- assert true
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
val violations = check_noalloc_violations("fn1", ["new"], [], m)
expect(violations.len()).to_equal(1)
match violations[0].kind:
    NoallocViolationKind.DirectAlloc:
        assert_true(true)
    _:
        assert_false(true)
```

</details>

#### violation kind is TransitiveCall for allocating callee

- m register
   - Expected: violations.len() equals `1`
- assert true
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
m.register("heap_fn", false, true, "")
val violations = check_noalloc_violations("fn2", [], ["heap_fn"], m)
expect(violations.len()).to_equal(1)
match violations[0].kind:
    NoallocViolationKind.TransitiveCall:
        assert_true(true)
    _:
        assert_false(true)
```

</details>

### check_all_noalloc_fns

#### returns all violations across noalloc fns in manifest

- m register
- m register
- m register
   - Expected: violations.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
m.register("noalloc_a", true, false, "")
m.register("noalloc_b", true, false, "")
m.register("plain_fn", false, false, "")
val fn_bodies: [{text: [text]}] = [{"noalloc_a": ["new"]}, {"noalloc_b": ["array_literal"]}]
val fn_callees: [{text: [text]}] = []
val violations = check_all_noalloc_fns(fn_bodies, fn_callees, m)
expect(violations.len()).to_equal(2)
```

</details>

#### ignores non-noalloc fns even if they allocate

- m register
   - Expected: violations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = NoallocCapabilityManifest.new()
m.register("plain_fn", false, false, "")
val fn_bodies: [{text: [text]}] = [{"plain_fn": ["new"]}]
val fn_callees: [{text: [text]}] = []
val violations = check_all_noalloc_fns(fn_bodies, fn_callees, m)
expect(violations.len()).to_equal(0)
```

</details>

### format_noalloc_violation

#### formats DirectAlloc violation with error prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = NoallocViolation(fn_name: "boot", kind: NoallocViolationKind.DirectAlloc, detail: "heap allocation via 'new'", line: 0)
val msg = format_noalloc_violation(v)
expect(msg).to_contain("error[noalloc]")
expect(msg).to_contain("boot")
```

</details>

#### formats TransitiveCall violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = NoallocViolation(fn_name: "isr", kind: NoallocViolationKind.TransitiveCall, detail: "call to allocating function 'malloc_fn'", line: 0)
val msg = format_noalloc_violation(v)
expect(msg).to_contain("transitive-call")
```

</details>

#### includes line number when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = NoallocViolation(fn_name: "isr", kind: NoallocViolationKind.DirectAlloc, detail: "new", line: 42)
val msg = format_noalloc_violation(v)
expect(msg).to_contain("42")
```

</details>

#### format_noalloc_violations returns empty for no violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msgs = format_noalloc_violations([])
expect(msgs.len()).to_equal(0)
```

</details>

#### format_noalloc_violations formats each violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v1 = NoallocViolation(fn_name: "f1", kind: NoallocViolationKind.DirectAlloc, detail: "new", line: 0)
val v2 = NoallocViolation(fn_name: "f2", kind: NoallocViolationKind.TransitiveCall, detail: "call", line: 0)
val msgs = format_noalloc_violations([v1, v2])
expect(msgs.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/alloc_checker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Noalloc Checker
- is_direct_alloc_expr
- direct_alloc_description
- NoallocCapabilityManifest
- check_noalloc_violations
- check_all_noalloc_fns
- format_noalloc_violation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
