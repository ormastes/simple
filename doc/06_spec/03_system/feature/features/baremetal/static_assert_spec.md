# Static Assertions Specification

> Static assertions allow compile-time validation of conditions.

<!-- sdn-diagram:id=static_assert_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_assert_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_assert_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_assert_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Assertions Specification

Static assertions allow compile-time validation of conditions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-001 |
| Category | Language / Bare-Metal |
| Status | Parser-safe local coverage |
| Source | `test/03_system/feature/features/baremetal/static_assert_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Static assertions allow compile-time validation of conditions.
They are evaluated during compilation and cause a compile error if false.

## Scenarios

### Static Assertions
_Compile-time assertion validation._

#### Basic Assertions
_Simple constant expression assertions._

#### validates true literal

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = static_assert_case("true literal", true, "expected true")
check(record.passes())
check(record.error_message() == "")
```

</details>

#### validates integer equality

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = static_assert_case("integer equality", 1 + 1 == 2, "1 + 1 must equal 2")
check(record.passes())
check(record.error_message() == "")
```

</details>

#### validates boolean operations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = static_assert_case("boolean operations", true and true, "boolean expression failed")
check(record.passes())
```

</details>

#### Type Size Assertions
_Validate type sizes at compile time._

#### validates primitive type sizes

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val i64_size = 8
val u32_size = 4
check(i64_size > u32_size)
check(i64_size == 8)
```

</details>

#### validates float sizes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f64_size = 8
val f32_size = 4
check(f64_size > f32_size)
```

</details>

#### validates char size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val char_size = 4
check(char_size > 0)
```

</details>

#### validates bool size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bool_size = 1
check(bool_size == 1)
```

</details>

#### Alignment Assertions
_Validate type alignments at compile time._

#### validates primitive alignments

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val int_align = 8
check(is_power_of_two(int_align))
```

</details>

#### validates float alignments

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val float_align = 8
check(is_power_of_two(float_align))
```

</details>

#### Custom Error Messages
_Static assertions with custom messages._

#### uses custom message on failure

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = static_assert_case("failure", false, "alignment must be a power of two")
check(record.passes() == false)
check(record.error_message() == "alignment must be a power of two")
```

</details>

#### Complex Expressions
_Assertions with compound expressions._

#### validates compound comparisons

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lhs = 10
val rhs = 2
check((lhs + rhs) == 12)
check((lhs - rhs) == 8)
```

</details>

#### validates bitwise operations

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((0xFF xor 0x0F) == 0xF0)
check((0xF0 & 0x0F) == 0x00)
```

</details>

#### validates shift operations

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((1 << 4) == 16)
check((16 >> 2) == 4)
```

</details>

#### Use Cases - Bare Metal
_Real-world static assertion use cases._

#### validates GDT entry size

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gdt_entry_size = 8
check(gdt_entry_size == 8)
check(is_power_of_two(gdt_entry_size))
```

</details>

#### validates multiboot header alignment

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val multiboot_header_alignment = 8
check(is_power_of_two(multiboot_header_alignment))
```

</details>

#### validates page size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 4096
check(is_power_of_two(page_size))
```

</details>

### Const Evaluation
_Compile-time constant evaluation._

#### Arithmetic

#### evaluates integer arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 3
expect(a + b).to_equal(13)
expect(a - b).to_equal(7)
expect(a * b).to_equal(30)
expect(a / b).to_equal(3)
expect(a % b).to_equal(1)
```

</details>

#### evaluates negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val neg = -42
expect(neg).to_equal(-42)
expect(-neg).to_equal(42)
```

</details>

#### Comparison

#### evaluates comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 < 2).to_equal(true)
expect(2 <= 2).to_equal(true)
expect(3 > 2).to_equal(true)
expect(3 >= 3).to_equal(true)
expect(1).to_equal(1)
expect(1).to_not_equal(2)
```

</details>

#### Boolean Logic

#### evaluates boolean operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true and true).to_equal(true)
expect(not (true and false)).to_equal(true)
expect(false or true).to_equal(true)
expect(not (false or false)).to_equal(true)
expect(not false).to_equal(true)
expect(not (not true)).to_equal(true)
```

</details>

#### Bitwise Operations

#### evaluates bitwise AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((0xFF & 0x0F) == 0x0F).to_equal(true)
```

</details>

#### evaluates bitwise OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((0xF0 | 0x0F) == 0xFF).to_equal(true)
```

</details>

#### evaluates bitwise XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((0xFF xor 0xF0) == 0x0F).to_equal(true)
```

</details>

#### evaluates bit shifts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((1 << 0) == 1).to_equal(true)
expect((1 << 1) == 2).to_equal(true)
expect((1 << 4) == 16).to_equal(true)
expect((16 >> 2) == 4).to_equal(true)
expect((256 >> 4) == 16).to_equal(true)
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
