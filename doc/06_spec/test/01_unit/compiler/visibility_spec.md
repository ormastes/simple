# visibility_spec

> Tests the core algorithm that converts filenames to expected type names.

<!-- sdn-diagram:id=visibility_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=visibility_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

visibility_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=visibility_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# visibility_spec

Tests the core algorithm that converts filenames to expected type names.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/visibility_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Snake_case to PascalCase Conversion

    Tests the core algorithm that converts filenames to expected type names.

## Scenarios

### Filename to Type Name Conversion

#### converts simple snake_case to PascalCase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filename_to_type_name("test_case")
expect result == "TestCase"
```

</details>

#### converts multi-word snake_case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filename_to_type_name("string_interner")
expect result == "StringInterner"
```

</details>

#### handles .spl extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filename_to_type_name("test_case.spl")
expect result == "TestCase"
```

</details>

#### handles single word without underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filename_to_type_name("io")
expect result == "Io"
```

</details>

#### handles single word with extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filename_to_type_name("io.spl")
expect result == "Io"
```

</details>

#### handles three-word names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filename_to_type_name("http_client_pool")
expect result == "HttpClientPool"
```

</details>

#### preserves case for non-first letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If original has mixed case (unusual), preserve it
val result = filename_to_type_name("http_api")
expect result == "HttpApi"
```

</details>

### Type Name Matching

#### matches exact conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = type_matches_filename("TestCase", "test_case.spl")
expect matches
```

</details>

#### does not match different names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = type_matches_filename("Helper", "test_case.spl")
expect not matches
```

</details>

#### matches without extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = type_matches_filename("StringInterner", "string_interner")
expect matches
```

</details>

#### matches single-word files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = type_matches_filename("Io", "io.spl")
expect matches
```

</details>

#### handles case sensitivity correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestCase vs testcase - should not match
val matches = type_matches_filename("testcase", "test_case.spl")
expect not matches
```

</details>

### Effective Visibility Calculation

#### explicit pub is always public

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_public = effective_visibility("Helper", "test_case.spl", true)
expect is_public
```

</details>

#### filename match makes public

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_public = effective_visibility("TestCase", "test_case.spl", false)
expect is_public
```

</details>

#### non-matching name without pub is private

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_public = effective_visibility("Helper", "test_case.spl", false)
expect not is_public
```

</details>

#### explicit pub overrides any filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_public = effective_visibility("Anything", "other.spl", true)
expect is_public
```

</details>

#### filename match works for single-word files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_public = effective_visibility("Io", "io.spl", false)
expect is_public
```

</details>

### Edge Cases

#### handles empty filename parts (double underscore)

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test__case -> TestCase (empty part ignored)
val result = filename_to_type_name("test__case")
# Should handle gracefully - either "TestCase" or "Test_Case"
expect result.len() > 0
```

</details>

#### handles filename with no underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filename_to_type_name("simple")
expect result == "Simple"
```

</details>

#### handles very long filenames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filename_to_type_name("very_long_test_case_name_builder_factory")
expect result == "VeryLongTestCaseNameBuilderFactory"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
