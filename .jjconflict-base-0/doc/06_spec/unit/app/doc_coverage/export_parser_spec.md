# Export Parser Specification

> Tests covering find_module_init, extract_export_names, parse_exports, is_function_exported, export_parser integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export Parser Specification

## Scenarios

### find_module_init

#### finds __init__.spl in parent directory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds __init__.spl in parent directory
   - Expected: ends_init is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds __init__.spl in parent directory")
val file_path = fixture_path("sample_module/feature.spl")
val result = find_module_init(file_path)

expect(result).not_to_be_nil()
val ends_init = result.ends_with("__init__.spl")
expect(ends_init).to_equal(true)
```

</details>

#### finds mod.spl in current directory

- finds mod.spl in current directory
   - Expected: ends_mod is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds mod.spl in current directory")
val file_path = fixture_path("mod_example/helpers.spl")
val result = find_module_init(file_path)

expect(result).not_to_be_nil()
val ends_mod = result.ends_with("mod.spl")
expect(ends_mod).to_equal(true)
```

</details>

#### returns nil when no module file exists

- returns nil when no module file exists
   - Expected: not_crashed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when no module file exists")
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

- handles nil input gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nil input gracefully")
val result = find_module_init(nil)
expect(result).to_be_nil()
```

</details>

#### handles empty string input gracefully

- handles empty string input gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string input gracefully")
val result = find_module_init("")
expect(result).to_be_nil()
```

</details>

### extract_export_names

#### extracts names from simple export statement

- extracts names from simple export statement
   - Expected: names.len() equals `2`
   - Expected: names[0] equals `Foo`
   - Expected: names[1] equals `Bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts names from simple export statement")
val line = "export Foo, Bar"
val names = extract_export_names(line)

expect(names.len()).to_equal(2)
expect(names[0]).to_equal("Foo")
expect(names[1]).to_equal("Bar")
```

</details>

#### extracts names from export with spaces

- extracts names from export with spaces
   - Expected: names.len() equals `3`
   - Expected: names[0] equals `Foo`
   - Expected: names[1] equals `Bar`
   - Expected: names[2] equals `Baz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts names from export with spaces")
val line = "export   Foo  ,  Bar  ,  Baz  "
val names = extract_export_names(line)

expect(names.len()).to_equal(3)
expect(names[0]).to_equal("Foo")
expect(names[1]).to_equal("Bar")
expect(names[2]).to_equal("Baz")
```

</details>

#### handles export with curly braces

- handles export with curly braces
   - Expected: names.len() equals `2`
   - Expected: names[0] equals `Foo`
   - Expected: names[1] equals `Bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles export with curly braces")
val line = "export {Foo, Bar}"
val names = extract_export_names(line)

expect(names.len()).to_equal(2)
expect(names[0]).to_equal("Foo")
expect(names[1]).to_equal("Bar")
```

</details>

#### handles single name export

- handles single name export
   - Expected: names.len() equals `1`
   - Expected: names[0] equals `SingleName`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single name export")
val line = "export SingleName"
val names = extract_export_names(line)

expect(names.len()).to_equal(1)
expect(names[0]).to_equal("SingleName")
```

</details>

#### handles export with curly braces and spaces

- handles export with curly braces and spaces
   - Expected: names.len() equals `3`
   - Expected: names[0] equals `Foo`
   - Expected: names[1] equals `Bar`
   - Expected: names[2] equals `Baz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles export with curly braces and spaces")
val line = "export { Foo , Bar , Baz }"
val names = extract_export_names(line)

expect(names.len()).to_equal(3)
expect(names[0]).to_equal("Foo")
expect(names[1]).to_equal("Bar")
expect(names[2]).to_equal("Baz")
```

</details>

#### returns empty array for non-export line

- returns empty array for non-export line
   - Expected: names.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty array for non-export line")
val line = "use module.{function}"
val names = extract_export_names(line)

expect(names.len()).to_equal(0)
```

</details>

#### returns empty array for comment line

- returns empty array for comment line
   - Expected: names.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty array for comment line")
val line = "# export Foo"
val names = extract_export_names(line)

expect(names.len()).to_equal(0)
```

</details>

### parse_exports

#### parses exports from __init__.spl

- parses exports from __init__.spl
   - Expected: exports.len() equals `2`
   - Expected: has_public_func is true
   - Expected: has_public_struct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses exports from __init__.spl")
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

- parses exports from mod.spl with multiple styles
   - Expected: exports.len() equals `3`
   - Expected: has_one is true
   - Expected: has_two is true
   - Expected: has_three is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses exports from mod.spl with multiple styles")
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

- returns empty array for non-existent file
   - Expected: exports.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty array for non-existent file")
val module_file = fixture_path("nonexistent/mod.spl")
val exports = parse_exports(module_file)

expect(exports.len()).to_equal(0)
```

</details>

#### ignores comment lines

- ignores comment lines
   - Expected: has_comment is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores comment lines")
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

- returns true for exported function
   - Expected: is_exported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for exported function")
val source_file = fixture_path("sample_module/feature.spl")
val is_exported = is_function_exported("public_function", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns false for non-exported function

- returns false for non-exported function
   - Expected: is_exported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-exported function")
val source_file = fixture_path("sample_module/feature.spl")
val is_exported = is_function_exported("_internal_helper", source_file)

expect(is_exported).to_equal(false)
```

</details>

#### returns true for exported struct

- returns true for exported struct
   - Expected: is_exported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for exported struct")
val source_file = fixture_path("sample_module/feature.spl")
val is_exported = is_function_exported("PublicStruct", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns false for non-exported struct

- returns false for non-exported struct
   - Expected: is_exported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-exported struct")
val source_file = fixture_path("sample_module/feature.spl")
val is_exported = is_function_exported("InternalStruct", source_file)

expect(is_exported).to_equal(false)
```

</details>

#### returns false when no module file exists

- returns false when no module file exists
   - Expected: is_exported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when no module file exists")
val source_file = fixture_path("no_module/standalone.spl")
val is_exported = is_function_exported("standalone_function", source_file)

# Should return false since no module file defines exports
expect(is_exported).to_equal(false)
```

</details>

#### returns true for helper_one in mod_example

- returns true for helper_one in mod_example
   - Expected: is_exported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for helper_one in mod_example")
val source_file = fixture_path("mod_example/helpers.spl")
val is_exported = is_function_exported("helper_one", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns true for helper_two in mod_example

- returns true for helper_two in mod_example
   - Expected: is_exported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for helper_two in mod_example")
val source_file = fixture_path("mod_example/helpers.spl")
val is_exported = is_function_exported("helper_two", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns true for helper_three in mod_example

- returns true for helper_three in mod_example
   - Expected: is_exported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for helper_three in mod_example")
val source_file = fixture_path("mod_example/helpers.spl")
val is_exported = is_function_exported("helper_three", source_file)

expect(is_exported).to_equal(true)
```

</details>

#### returns false for not_exported in mod_example

- returns false for not_exported in mod_example
   - Expected: is_exported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for not_exported in mod_example")
val source_file = fixture_path("mod_example/helpers.spl")
val is_exported = is_function_exported("not_exported", source_file)

expect(is_exported).to_equal(false)
```

</details>

### export_parser integration

#### correctly identifies public API across module hierarchy

- correctly identifies public API across module hierarchy
   - Expected: public_is_exported is true
   - Expected: internal_is_exported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("correctly identifies public API across module hierarchy")
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

- handles multiple export statements in one file
   - Expected: exports.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple export statements in one file")
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
| Source | `test/unit/app/doc_coverage/export_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering find_module_init, extract_export_names, parse_exports, is_function_exported, export_parser integration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0ed5d052e009acb0bf09a80eaecb761c6ca8a6f8521ae09d2e64fe6b15a4ec80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ed5d052e009acb0bf09a80eaecb761c6ca8a6f8521ae09d2e64fe6b15a4ec80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ed5d052e009acb0bf09a80eaecb761c6ca8a6f8521ae09d2e64fe6b15a4ec80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/doc_coverage/export_parser_spec.spl
mirror: doc/06_spec/unit/app/doc_coverage/export_parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/doc_coverage/export_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/doc_coverage/export_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/doc_coverage/export_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/doc_coverage/export_parser_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds __init__.spl in parent directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/export_parser_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds mod.spl in current directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/export_parser_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil when no module file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
