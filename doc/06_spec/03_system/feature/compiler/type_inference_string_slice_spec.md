# Type Inference String Slice Bug

> Purpose: string-slice expressions keep their text type so string methods resolve. Audience: engineers reading this spec to confirm the inference behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference String Slice Bug

Purpose: string-slice expressions keep their text type so string methods resolve. Audience: engineers reading this spec to confirm the inference behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/type_inference_string_slice_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: string-slice expressions keep their text type so string methods resolve. Audience: engineers reading this spec to confirm the inference behavior still holds.

## Operator workflow

1. Run `bin/simple test test/03_system/feature/compiler/type_inference_string_slice_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers string slicing inference only; other slice receivers are out of scope.

## Scenarios

### Type Inference for String Slicing

### Basic string slicing

#### infers sliced string as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
val text = "hello world"
val sliced = text[6:]

# This should work - sliced should be text
val result = sliced.split(" ")
expect(result.len()).to_be_greater_than(0)
```

</details>

#### allows method calls on sliced strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
val text = "--features=a,b,c"
val features_str = text[11:]

# This should work - features_str should be text
val features = features_str.split(",")
expect(features.len()).to_equal(3)
```

</details>

#### infers mid-range slice as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
val text = "abcdefgh"
val sliced = text[2:6]

# Should be able to call text methods
val upper = sliced.upper()
expect(upper).to_equal("CDEF")
```

</details>

### String slicing in conditionals

#### infers correctly in if branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
val arg = "--profile=release"

if arg.starts_with("--profile="):
    val profile_str = arg[10:]
    # Should infer as text, not enum
    val parts = profile_str.split("=")
    expect(parts.len()).to_be_greater_than(0)
```

</details>

#### infers correctly with variable assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
val args = ["--opt-level=2", "--features=test"]

for arg in args:
    if arg.starts_with("--opt-level="):
        val level_str = arg[12:]
        # This should work - level_str is text
        val is_empty = level_str.len() == 0
        expect(is_empty).to_equal(false)
```

</details>

### String slicing with enum variables nearby

#### doesn't confuse string slice with enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
var profile = BuildProfile.Debug
val args = ["--profile=release"]

for arg in args:
    if arg.starts_with("--profile="):
        val profile_str = arg[10:]
        # BUG: Type inference incorrectly infers profile_str as enum
        # because of the nearby 'profile' enum variable
        val parts = profile_str.split(",")
        expect(parts.len()).to_be_greater_than(0)
```

</details>

#### handles multiple string operations after slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
var profile = BuildProfile.Release
val text = "--features=a,b,c"

val features_str = text[11:]
# Chain multiple string methods
val trimmed = features_str.trim()
val parts = trimmed.split(",")
val joined = parts.join(";")

expect(joined).to_equal("a;b;c")
```

</details>

### Type annotation workaround

#### works with explicit type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
val arg = "--features=x,y,z"
val features_str: text = arg[11:]

# With explicit annotation, this should work
val features = features_str.split(",")
expect(features.len()).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b7198a7a0f48c0c79c021659caeab7f6f31bc245502b9cd8681d23a9385fc7b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7198a7a0f48c0c79c021659caeab7f6f31bc245502b9cd8681d23a9385fc7b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7198a7a0f48c0c79c021659caeab7f6f31bc245502b9cd8681d23a9385fc7b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/feature/compiler/type_inference_string_slice_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/type_inference_string_slice_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/type_inference_string_slice_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/type_inference_string_slice_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/type_inference_string_slice_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/compiler/type_inference_string_slice_spec.spl:71:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'infers sliced string as text' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/compiler/type_inference_string_slice_spec.spl:80:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'allows method calls on sliced strings' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/compiler/type_inference_string_slice_spec.spl:89:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'infers mid-range slice as text' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/compiler/type_inference_string_slice_spec.spl:101:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'infers correctly in if branches' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
