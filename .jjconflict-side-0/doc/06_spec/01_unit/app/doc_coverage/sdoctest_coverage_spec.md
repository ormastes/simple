# Sdoctest Coverage Specification

> <details>

<!-- sdn-diagram:id=sdoctest_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdoctest_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdoctest_coverage_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdoctest_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdoctest Coverage Specification

## Scenarios

### SDoctest Coverage Analysis

#### validates tag format for stdlib category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_tag_format("stdlib:string")
expect(valid).to_equal(true)
```

</details>

#### validates tag format for core category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_tag_format("core:parser")
expect(valid).to_equal(true)
```

</details>

#### rejects invalid tag without colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_tag_format("invalid_tag")
expect(valid).to_equal(false)
```

</details>

#### rejects invalid tag with uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_tag_format("stdlib:String")
expect(valid).to_equal(false)
```

</details>

#### rejects invalid category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_tag_format("invalid:name")
expect(valid).to_equal(false)
```

</details>

#### suggests tags for stdlib module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags = suggest_missing_tags("src/std/string.spl")
expect(tags.len()).to_equal(1)
expect(tags[0]).to_equal("stdlib:string")
```

</details>

#### suggests tags for core module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags = suggest_missing_tags("src/core/parser.spl")
expect(tags.len()).to_equal(1)
expect(tags[0]).to_equal("core:parser")
```

</details>

#### suggests tags for app module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags = suggest_missing_tags("src/app/io/mod.spl")
expect(tags.len()).to_equal(1)
expect(tags[0]).to_equal("feature:io")
```

</details>

#### extracts function name from code line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn hello_world():"
val names = extract_function_names_from_code(code)
expect(names.len()).to_equal(1)
expect(names[0]).to_equal("hello_world")
```

</details>

#### extracts class name from code line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "class Point:"
val names = extract_function_names_from_code(code)
expect(names.len()).to_equal(1)
expect(names[0]).to_equal("Point")
```

</details>

#### extracts enum name from code line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "enum Status:"
val names = extract_function_names_from_code(code)
expect(names.len()).to_equal(1)
expect(names[0]).to_equal("Status")
```

</details>

#### matches functions to sdoctest blocks

1. public funcs push
2. public funcs push
3. blocks push
   - Expected: matched.len() equals `1`
   - Expected: matched[0] equals `hello_world`
   - Expected: missing.len() equals `1`
   - Expected: missing[0] equals `goodbye_world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var public_funcs: [text] = []
public_funcs.push("hello_world")
public_funcs.push("goodbye_world")

var blocks: [text] = []
blocks.push("fn hello_world():\n    print 'Hello'")

val result = match_functions_to_sdoctest(public_funcs, blocks)
val matched = result.0
val missing = result.1

expect(matched.len()).to_equal(1)
expect(matched[0]).to_equal("hello_world")
expect(missing.len()).to_equal(1)
expect(missing[0]).to_equal("goodbye_world")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/sdoctest_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDoctest Coverage Analysis

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
