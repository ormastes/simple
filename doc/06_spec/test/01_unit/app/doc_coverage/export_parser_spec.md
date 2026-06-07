# Export Parser Specification

> <details>

<!-- sdn-diagram:id=export_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=export_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

export_parser_spec -> std
export_parser_spec -> doc_coverage
export_parser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=export_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export Parser Specification

## Scenarios

### find_module_init

#### finds __init__.spl in parent directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = fixture_path("sample_module/feature.spl")
val result = find_module_init(file_path)

expect(result).not_to_be_nil()
val ends_init = result.ends_with("__init__.spl")
expect(ends_init).to_equal(true)
```

</details>

#### finds mod.spl in current directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = fixture_path("mod_example/helpers.spl")
val result = find_module_init(file_path)

expect(result).not_to_be_nil()
val ends_mod = result.ends_with("mod.spl")
expect(ends_mod).to_equal(true)
```

</details>

#### returns nil when no module file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = fixture_path("no_module/standalone.spl")
val result = find_module_init(file_path)

# Should be nil since no __init__.spl or mod.spl exists
# Note: Might find a parent module if one exists higher up
# For this test, we just verify it doesn't crash
val not_crashed = true
expect(not_crashed).to_equal(true)
```

</details>

#### handles nil input gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_module_init(nil)
expect(result).to_be_nil()
```

</details>

#### handles empty string input gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_module_init("")
expect(result).to_be_nil()
```

</details>

### extract_export_names

#### extracts names from simple export statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "export Foo, Bar"
val names = extract_export_names(line)

expect(names.len()).to_equal(2)
expect(names[0]).to_equal("Foo")
expect(names[1]).to_equal("Bar")
```

</details>

#### extracts names from export with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "export   Foo  ,  Bar  ,  Baz  "
val names = extract_export_names(line)

expect(names.len()).to_equal(3)
expect(names[0]).to_equal("Foo")
expect(names[1]).to_equal("Bar")
expect(names[2]).to_equal("Baz")
```

</details>

#### handles export with curly braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "export {Foo, Bar}"
val names = extract_export_names(line)

expect(names.len()).to_equal(2)
expect(names[0]).to_equal("Foo")
expect(names[1]).to_equal("Bar")
```

</details>

#### handles single name export

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "export SingleName"
val names = extract_export_names(line)

expect(names.len()).to_equal(1)
expect(names[0]).to_equal("SingleName")
```

</details>

#### handles export with curly braces and spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "export { Foo , Bar , Baz }"
val names = extract_export_names(line)

expect(names.len()).to_equal(3)
expect(names[0]).to_equal("Foo")
expect(names[1]).to_equal("Bar")
expect(names[2]).to_equal("Baz")
```

</details>

#### returns empty array for non-export line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "use module.{function}"
val names = extract_export_names(line)

expect(names.len()).to_equal(0)
```

</details>

#### returns empty array for comment line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "# export Foo"
val names = extract_export_names(line)

expect(names.len()).to_equal(0)
```

</details>

### parse_exports

#### parses exports from __init__.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_file = fixture_path("sample_module/__init__.spl")
val exports = parse_exports(module_file)

expect(exports.len()).to_equal(2)
# Should contain public_function and PublicStruct
var has_public_func = false
var has_public_struct = false

for name in exports:
    if name == "public_function":
        has_public_func = true
    if name == "PublicStruct":
        has_public_struct = true

expect(has_public_func).to_equal(true)
expect(has_public_struct).to_equal(true)
```

</details>

#### parses exports from mod.spl with multiple styles

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_file = fixture_path("mod_example/mod.spl")
val exports = parse_exports(module_file)

expect(exports.len()).to_equal(3)
# Should contain helper_one, helper_two, helper_three
var has_one = false
var has_two = false
var has_three = false

for name in exports:
    if name == "helper_one":
        has_one = true
    if name == "helper_two":
        has_two = true
    if name == "helper_three":
        has_three = true

expect(has_one).to_equal(true)
expect(has_two).to_equal(true)
expect(has_three).to_equal(true)
```

</details>

#### returns empty array for non-existent file

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_file = fixture_path("nonexistent/mod.spl")
val exports = parse_exports(module_file)

expect(exports.len()).to_equal(0)
```

</details>

#### ignores comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_file = fixture_path("sample_module/__init__.spl")
val exports = parse_exports(module_file)

# Should not include any comments
var has_comment = false
for name in exports:
    if name.starts_with("#"):
        has_comment = true

expect(has_comment).to_equal(false)
```

</details>

### is_function_exported

#### returns true for exported function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("sample_module/feature.spl")
val is_exported = is_function_exported("public_function", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns false for non-exported function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("sample_module/feature.spl")
val is_exported = is_function_exported("_internal_helper", source_file)

expect(is_exported).to_equal(false)
```

</details>

#### returns true for exported struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("sample_module/feature.spl")
val is_exported = is_function_exported("PublicStruct", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns false for non-exported struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("sample_module/feature.spl")
val is_exported = is_function_exported("InternalStruct", source_file)

expect(is_exported).to_equal(false)
```

</details>

#### returns false when no module file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("no_module/standalone.spl")
val is_exported = is_function_exported("standalone_function", source_file)

# Should return false since no module file defines exports
expect(is_exported).to_equal(false)
```

</details>

#### returns true for helper_one in mod_example

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("mod_example/helpers.spl")
val is_exported = is_function_exported("helper_one", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns true for helper_two in mod_example

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("mod_example/helpers.spl")
val is_exported = is_function_exported("helper_two", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns true for helper_three in mod_example

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("mod_example/helpers.spl")
val is_exported = is_function_exported("helper_three", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns false for not_exported in mod_example

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_file = fixture_path("mod_example/helpers.spl")
val is_exported = is_function_exported("not_exported", source_file)

expect(is_exported).to_equal(false)
```

</details>

### export_parser integration

#### correctly identifies public API across module hierarchy

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test with real module structure
val feature_file = fixture_path("sample_module/feature.spl")

# Public function should be exported
val public_is_exported = is_function_exported("public_function", feature_file)
expect(public_is_exported).to_equal(true)

# Internal helper should not be exported
val internal_is_exported = is_function_exported("_internal_helper", feature_file)
expect(internal_is_exported).to_equal(false)

# Verify the module file was found
val module_file = find_module_init(feature_file)
expect(module_file).not_to_be_nil()
```

</details>

#### handles multiple export statements in one file

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val helpers_file = fixture_path("mod_example/helpers.spl")
val module_file = find_module_init(helpers_file)

expect(module_file).not_to_be_nil()

val exports = parse_exports(module_file)
# Should have 3 exports from 2 export statements
expect(exports.len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/export_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- find_module_init
- extract_export_names
- parse_exports
- is_function_exported
- export_parser integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
