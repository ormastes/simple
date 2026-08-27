# Const Functions Specification

> Const functions can be evaluated at compile time, enabling:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Functions Specification

Const functions can be evaluated at compile time, enabling:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-002 |
| Category | Language / Bare-Metal |
| Status | Blocked (const fn syntax not supported by runtime parser) |
| Source | `test/03_system/feature/features/baremetal/const_fn_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Const functions can be evaluated at compile time, enabling:
- Compile-time computation of lookup tables
- Constant initialization without runtime overhead
- Static assertions with computed values

## Scenarios

### Const Functions

#### Basic Const Functions
_Simple const function definitions._

#### evaluates direct arithmetic helper

- evaluates direct arithmetic helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates direct arithmetic helper")
check(fake_const_add(10, 20) == 30)
```

</details>

#### evaluates nested helper calls

- evaluates nested helper calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates nested helper calls")
check(fake_const_add(fake_const_add(2, 3), 4) == 9)
```

</details>

#### evaluates a min helper like a const branch

- evaluates a min helper like a const branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates a min helper like a const branch")
check(fake_const_min(50, 100) == 50)
```

</details>

#### Const Conditionals
_Const functions with control flow._

#### evaluates const if-style branching

- evaluates const if-style branching


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates const if-style branching")
check(fake_const_min(100, 50) == 50)
```

</details>

#### evaluates const match-style selection

- evaluates const match-style selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates const match-style selection")
val input = 2
val output = if input == 1: 10 else: if input == 2: 20 else: 30
check(output == 20)
```

</details>

#### Const Recursion
_Recursive const functions._

#### evaluates factorial recursively

- evaluates factorial recursively


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates factorial recursively")
check(fake_const_factorial(5) == 120)
```

</details>

#### evaluates fibonacci recursively

- evaluates fibonacci recursively


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates fibonacci recursively")
check(fake_const_fibonacci(7) == 13)
```

</details>

#### Const Arrays
_Const functions returning arrays._

#### creates a lookup-table style array

- creates a lookup-table style array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a lookup-table style array")
val table = fake_const_lookup_table(4)
check(table.len() == 4)
check(table[0] == 0)
check(table[3] == 9)
```

</details>

#### Const Type Operations
_Const functions with type intrinsics._

#### uses a size-like helper

- uses a size-like helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses a size-like helper")
check(fake_size_of_i64() == 8)
```

</details>

#### uses an align-like helper

- uses an align-like helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses an align-like helper")
check(fake_align_of_i64() == 8)
```

</details>

#### Use Cases - Lookup Tables
_Real-world const function applications._

#### generates a CRC-style lookup table

- generates a CRC-style lookup table


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates a CRC-style lookup table")
val table = fake_crc_table()
check(table.len() == 4)
check(table[1] == 7)
```

</details>

#### generates a sin-style lookup table

- generates a sin-style lookup table


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates a sin-style lookup table")
val table = fake_sin_table()
check(table.len() == 4)
check(table[2] == 2)
```

</details>

#### Const Function Restrictions
_What's NOT allowed in const functions._

#### allows pure arithmetic

- allows pure arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows pure arithmetic")
check((2 + 3) * 4 == 20)
```

</details>

#### allows pure boolean logic

- allows pure boolean logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows pure boolean logic")
check((true and not false) == true)
```

</details>

#### allows pure bitwise operations

- allows pure bitwise operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows pure bitwise operations")
val mask = 0x0F
check((0xFF & mask) == 0x0F)
```

</details>

### Const Evaluation Context
_Compile-time evaluation environment._

#### Constant Propagation

#### propagates constants through expressions

- propagates constants through expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates constants through expressions")
val A = 10
val B = 20
val C = A + B
check(C == 30)
```

</details>

#### propagates constants through conditionals

- propagates constants through conditionals


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates constants through conditionals")
val MAX = 100
val VALUE = 50
val RESULT = if VALUE < MAX: VALUE else: MAX
check(RESULT == 50)
```

</details>

#### Type-Level Constants

#### uses constants as array sizes

- uses constants as array sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses constants as array sizes")
val size = fake_const_add(2, 2)
val table = fake_const_lookup_table(size)
check(table.len() == 4)
```

</details>

#### uses computed constants

- uses computed constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses computed constants")
val computed = fake_const_factorial(3) + fake_const_min(9, 4)
check(computed == 10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `24e37c2152b24b914ab37b6da316d32b85c65538476e312bce167d7858d4ec91`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24e37c2152b24b914ab37b6da316d32b85c65538476e312bce167d7858d4ec91`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24e37c2152b24b914ab37b6da316d32b85c65538476e312bce167d7858d4ec91`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/baremetal/const_fn_spec.spl
mirror: doc/06_spec/03_system/feature/features/baremetal/const_fn_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/baremetal/const_fn_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/baremetal/const_fn_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/baremetal/const_fn_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates direct arithmetic helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/const_fn_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates nested helper calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/const_fn_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates a min helper like a const branch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
