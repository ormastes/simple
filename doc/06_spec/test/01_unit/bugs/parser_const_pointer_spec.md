# Parser *const/*mut Pointer Type Specification

> Verifies that the parser correctly handles *const T and *mut T pointer type syntax in extern function declarations, struct fields, and other type positions. Previously, 'const' was tokenized as KwConst keyword and caused "expected identifier, found Const" parse errors.

<!-- sdn-diagram:id=parser_const_pointer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_const_pointer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_const_pointer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_const_pointer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser *const/*mut Pointer Type Specification

Verifies that the parser correctly handles *const T and *mut T pointer type syntax in extern function declarations, struct fields, and other type positions. Previously, 'const' was tokenized as KwConst keyword and caused "expected identifier, found Const" parse errors.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-CONST-001 |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/bug/bug_report_const_pointer_parsing.md |
| Source | `test/01_unit/bugs/parser_const_pointer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the parser correctly handles *const T and *mut T pointer
type syntax in extern function declarations, struct fields, and other
type positions. Previously, 'const' was tokenized as KwConst keyword
and caused "expected identifier, found Const" parse errors.

## Syntax

```simple
extern fn memcpy(dst: *mut u8, src: *const u8, n: u64) -> *mut u8
struct Buffer:
    data: *const u8
    len: u64
```

## Scenarios

### Parser *const pointer types

#### extern function parsing

#### parses *const u8 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_const_u8(data: *const u8) -> i32").to_contain("*const u8")
```

</details>

#### parses *const u16 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_const_u16(data: *const u16, len: u64) -> i32").to_contain("*const u16")
```

</details>

#### parses *const u32 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_const_u32(data: *const u32, len: u64) -> i32").to_contain("*const u32")
```

</details>

#### parses *const u64 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_const_u64(data: *const u64) -> u64").to_contain("*const u64")
```

</details>

#### parses *const i32 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_const_i32(data: *const i32, count: u64) -> i64").to_contain("*const i32")
```

</details>

#### parses *const i64 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_const_i64(data: *const i64) -> i64").to_contain("*const i64")
```

</details>

#### extern function *mut parsing

#### parses *mut u8 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_mut_u8(data: *mut u8, len: u64) -> i32").to_contain("*mut u8")
```

</details>

#### parses *mut u16 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_mut_u16(data: *mut u16, len: u64) -> i32").to_contain("*mut u16")
```

</details>

#### parses *mut u32 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_mut_u32(data: *mut u32, len: u64) -> i32").to_contain("*mut u32")
```

</details>

#### parses *mut u64 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_mut_u64(data: *mut u64) -> i32").to_contain("*mut u64")
```

</details>

#### mixed *const and *mut

#### parses both *const and *mut in same function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_mixed_copy(dst: *mut u8, src: *const u8, n: u64) -> *mut u8").to_contain("*const u8")
```

</details>

#### parses multiple *const params

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_multi_const(a: *const u32, b: *const u32, c: *const u32) -> i32").to_contain("c: *const u32")
```

</details>

#### parses multiple *mut params

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_multi_mut(a: *mut u8, b: *mut u8) -> i32").to_contain("b: *mut u8")
```

</details>

#### parses complex mixed signatures

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_multi_mixed(src1: *const u8, src2: *const u8, dst: *mut u8, len: u64) -> i32").to_contain("dst: *mut u8")
```

</details>

#### plain *T pointer (no qualifier)

#### parses *u8 without const/mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_plain(p: *u8) -> i32").to_contain("p: *u8")
```

</details>

#### parses *u64 without const/mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_plain_wide(p: *u64) -> u64").to_contain("p: *u64")
```

</details>

#### pointer return types

#### parses *const T return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_ret_const(handle: u64) -> *const u8").to_end_with("*const u8")
```

</details>

#### parses *mut T return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_ret_mut(size: u64) -> *mut u8").to_end_with("*mut u8")
```

</details>

#### pointers mixed with regular params

#### parses pointer params alongside regular params

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_with_regular(handle: u64, data: *const u8, size: u64, flags: i32) -> i32").to_contain("data: *const u8")
```

</details>

#### parses strlen-like signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("extern fn ptr_strlen(s: *const u8) -> u64").to_contain("s: *const u8")
```

</details>

### Struct fields with pointer types

#### struct declarations

#### parses *const T struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = ReadOnlyBuffer(data: nil, len: 64)
expect(buf.len).to_equal(64)
```

</details>

#### parses *mut T struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = WritableBuffer(data: nil, len: 0, cap: 256)
expect(buf.cap).to_equal(256)
```

</details>

#### parses struct with both *const and *mut fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = DualBuffer(read_ptr: nil, write_ptr: nil, size: 1024)
expect(buf.size).to_equal(1024)
```

</details>

#### parses plain *T struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PlainPointerStruct(ptr: nil, size: 8)
expect(p.size).to_equal(8)
```

</details>

#### parses struct with multiple pointer fields of different types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MultiPointerStruct(a: nil, b: nil, c: nil, d: nil, count: 5)
expect(m.count).to_equal(5)
```

</details>

### Regression - existing type syntax still works

#### reference types

#### plain reference &T works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("val x: &i64").to_contain("&i64")
```

</details>

#### mutable reference &mut T works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("val x: &mut i64").to_contain("&mut i64")
```

</details>

#### basic types

#### i64 type annotation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
expect(x).to_equal(42)
```

</details>

#### text type annotation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: text = "hello"
expect(s).to_equal("hello")
```

</details>

#### bool type annotation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: bool = true
expect(b).to_equal(true)
```

</details>

#### collection types

#### array type [T] works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: [i64] = [1, 2, 3]
expect(a.len()).to_equal(3)
```

</details>

#### tuple type (A, B) works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (1, "two")
expect(t.1).to_equal("two")
```

</details>

#### function types

#### fn(A) -> B type works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: fn(i64) -> i64 = \x: x * 2
expect(f(5)).to_equal(10)
```

</details>

#### optional types

#### T? optional works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o: i64? = 42
expect(o ?? 0).to_equal(42)
```

</details>

#### nil optional works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o: i64? = nil
expect(o ?? 99).to_equal(99)
```

</details>

#### generic types

#### named generic types work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe: Option<i64> = Some(42)
expect(maybe ?? 0).to_equal(42)
```

</details>

#### infer type _

#### underscore infer still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("val inferred: _ = 17").to_contain(": _")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** [doc/bug/bug_report_const_pointer_parsing.md](doc/bug/bug_report_const_pointer_parsing.md)


</details>
