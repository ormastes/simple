# Static Assertions Specification

> Static assertions allow compile-time validation of conditions.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Static assertions allow compile-time validation of conditions.
They are evaluated during compilation and cause a compile error if false.

## Scenarios

### Static Assertions

#### Basic Assertions
_Simple constant expression assertions._

#### validates true literal

- validates true literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates true literal")
val record = static_assert_case("true literal", true, "expected true")
check(record.passes())
check(record.error_message() == "")
```

</details>

#### validates integer equality

- validates integer equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates integer equality")
val record = static_assert_case("integer equality", 1 + 1 == 2, "1 + 1 must equal 2")
check(record.passes())
check(record.error_message() == "")
```

</details>

#### validates boolean operations

- validates boolean operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates boolean operations")
val record = static_assert_case("boolean operations", true and true, "boolean expression failed")
check(record.passes())
```

</details>

#### Type Size Assertions
_Validate type sizes at compile time._

#### validates primitive type sizes

- validates primitive type sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates primitive type sizes")
val i64_size = 8
val u32_size = 4
check(i64_size > u32_size)
check(i64_size == 8)
```

</details>

#### validates float sizes

- validates float sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates float sizes")
val f64_size = 8
val f32_size = 4
check(f64_size > f32_size)
```

</details>

#### validates char size

- validates char size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates char size")
val char_size = 4
check(char_size > 0)
```

</details>

#### validates bool size

- validates bool size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates bool size")
val bool_size = 1
check(bool_size == 1)
```

</details>

#### Alignment Assertions
_Validate type alignments at compile time._

#### validates primitive alignments

- validates primitive alignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates primitive alignments")
val int_align = 8
check(is_power_of_two(int_align))
```

</details>

#### validates float alignments

- validates float alignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates float alignments")
val float_align = 8
check(is_power_of_two(float_align))
```

</details>

#### Custom Error Messages
_Static assertions with custom messages._

#### uses custom message on failure

- uses custom message on failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses custom message on failure")
val record = static_assert_case("failure", false, "alignment must be a power of two")
check(record.passes() == false)
check(record.error_message() == "alignment must be a power of two")
```

</details>

#### Complex Expressions
_Assertions with compound expressions._

#### validates compound comparisons

- validates compound comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates compound comparisons")
val lhs = 10
val rhs = 2
check((lhs + rhs) == 12)
check((lhs - rhs) == 8)
```

</details>

#### validates bitwise operations

- validates bitwise operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates bitwise operations")
check((0xFF xor 0x0F) == 0xF0)
check((0xF0 & 0x0F) == 0x00)
```

</details>

#### validates shift operations

- validates shift operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates shift operations")
check((1 << 4) == 16)
check((16 >> 2) == 4)
```

</details>

#### Use Cases - Bare Metal
_Real-world static assertion use cases._

#### validates GDT entry size

- validates GDT entry size


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates GDT entry size")
val gdt_entry_size = 8
check(gdt_entry_size == 8)
check(is_power_of_two(gdt_entry_size))
```

</details>

#### validates multiboot header alignment

- validates multiboot header alignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates multiboot header alignment")
val multiboot_header_alignment = 8
check(is_power_of_two(multiboot_header_alignment))
```

</details>

#### validates page size

- validates page size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates page size")
val page_size = 4096
check(is_power_of_two(page_size))
```

</details>

### Const Evaluation
_Compile-time constant evaluation._

#### Arithmetic

#### evaluates integer arithmetic

- evaluates integer arithmetic
   - Expected: a + b equals `13`
   - Expected: a - b equals `7`
   - Expected: a * b equals `30`
   - Expected: a / b equals `3`
   - Expected: a % b equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates integer arithmetic")
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

- evaluates negative numbers
   - Expected: neg equals `-42`
   - Expected: -neg equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates negative numbers")
val neg = -42
expect(neg).to_equal(-42)
expect(-neg).to_equal(42)
```

</details>

#### Comparison

#### evaluates comparisons

- evaluates comparisons
   - Expected: 1 < 2 is true
   - Expected: 2 <= 2 is true
   - Expected: 3 > 2 is true
   - Expected: 3 >= 3 is true
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates comparisons")
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

- evaluates boolean operations
   - Expected: true and true is true
   - Expected: not (true and false) is true
   - Expected: false or true is true
   - Expected: not (false or false) is true
   - Expected: not false is true
   - Expected: not (not true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates boolean operations")
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

- evaluates bitwise AND
   - Expected: (0xFF & 0x0F) equals `0x0F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates bitwise AND")
expect((0xFF & 0x0F)).to_equal(0x0F)
```

</details>

#### evaluates bitwise OR

- evaluates bitwise OR
   - Expected: (0xF0 | 0x0F) equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates bitwise OR")
expect((0xF0 | 0x0F)).to_equal(0xFF)
```

</details>

#### evaluates bitwise XOR

- evaluates bitwise XOR
   - Expected: (0xFF xor 0xF0) equals `0x0F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates bitwise XOR")
expect((0xFF xor 0xF0)).to_equal(0x0F)
```

</details>

#### evaluates bit shifts

- evaluates bit shifts
   - Expected: (1 << 0) equals `1`
   - Expected: (1 << 1) equals `2`
   - Expected: (1 << 4) equals `16`
   - Expected: (16 >> 2) equals `4`
   - Expected: (256 >> 4) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates bit shifts")
expect((1 << 0)).to_equal(1)
expect((1 << 1)).to_equal(2)
expect((1 << 4)).to_equal(16)
expect((16 >> 2)).to_equal(4)
expect((256 >> 4)).to_equal(16)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3794f729b2e48f8837dc8b0436bdf1abe1630f8b111320b719d62f55c042cd49`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3794f729b2e48f8837dc8b0436bdf1abe1630f8b111320b719d62f55c042cd49`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3794f729b2e48f8837dc8b0436bdf1abe1630f8b111320b719d62f55c042cd49`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/features/baremetal/static_assert_spec.spl
mirror: doc/06_spec/03_system/feature/features/baremetal/static_assert_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/baremetal/static_assert_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/baremetal/static_assert_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/baremetal/static_assert_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/features/baremetal/static_assert_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates true literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/static_assert_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates integer equality' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/static_assert_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates boolean operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
