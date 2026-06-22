# Type Inference String Slice Bug

> Reproduces a type inference bug involving string slice operations. Tests that the compiler correctly infers types when slicing strings, and that the type system handles the string/slice relationship without mismatches or panics.

<!-- sdn-diagram:id=type_inference_string_slice_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_inference_string_slice_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_inference_string_slice_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_inference_string_slice_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference String Slice Bug

Reproduces a type inference bug involving string slice operations. Tests that the compiler correctly infers types when slicing strings, and that the type system handles the string/slice relationship without mismatches or panics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/type_inference_string_slice_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Reproduces a type inference bug involving string slice operations. Tests that the
compiler correctly infers types when slicing strings, and that the type system
handles the string/slice relationship without mismatches or panics.

## Scenarios

### Type Inference for String Slicing

### Basic string slicing

#### infers sliced string as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
