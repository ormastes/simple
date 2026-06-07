# Code Generator Specification

> <details>

<!-- sdn-diagram:id=code_generator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=code_generator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

code_generator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=code_generator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Code Generator Specification

## Scenarios

### CodeTemplate

#### creates a template with name and description

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = CodeTemplate.new("entity", "An entity", "struct Foo:\n    x: f64")
expect(tmpl.name).to_equal("entity")
expect(tmpl.description).to_equal("An entity")
expect(tmpl.parameter_count()).to_equal(0)
```

</details>

#### adds parameters

1. var tmpl = CodeTemplate new
2. tmpl add parameter
3. tmpl add parameter
   - Expected: tmpl.parameter_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tmpl = CodeTemplate.new("test", "test tmpl", "code")
tmpl.add_parameter("name")
tmpl.add_parameter("type")
expect(tmpl.parameter_count()).to_equal(2)
```

</details>

### GeneratedCode

#### creates valid generated code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = GeneratedCode.new("struct Player:\n    x: f64", "entity")
expect(code.source).to_contain("Player")
expect(code.template_name).to_equal("entity")
expect(code.valid).to_equal(true)
```

</details>

#### counts lines correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = GeneratedCode.new("line1\nline2\nline3", "test")
expect(code.line_count()).to_equal(3)
```

</details>

#### counts single line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = GeneratedCode.new("single", "test")
expect(code.line_count()).to_equal(1)
```

</details>

### CodeGenerator

#### starts with default templates

1. var cg = CodeGenerator new
   - Expected: cg.template_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
expect(cg.template_count()).to_equal(3)
```

</details>

#### lists template names

1. var cg = CodeGenerator new
   - Expected: names.len().to_i32() equals `3`
   - Expected: names[0] equals `entity`
   - Expected: names[1] equals `component`
   - Expected: names[2] equals `system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
val names = cg.list_template_names()
expect(names.len().to_i32()).to_equal(3)
expect(names[0]).to_equal("entity")
expect(names[1]).to_equal("component")
expect(names[2]).to_equal("system")
```

</details>

#### finds a template by name

1. var cg = CodeGenerator new
   - Expected: tmpl.name equals `entity`
   - Expected: "not found" equals `entity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
val found = cg.find_template("entity")
if val Some(tmpl) = found:
    expect(tmpl.name).to_equal("entity")
else:
    expect("not found").to_equal("entity")
```

</details>

#### returns None for unknown template

1. var cg = CodeGenerator new
   - Expected: "should not find" equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
val found = cg.find_template("nonexistent")
if val Some(tmpl) = found:
    expect("should not find").to_equal("none")
# If we reach here without entering Some, the template was not found (correct)
```

</details>

#### generates entity code with name substitution

1. var cg = CodeGenerator new
   - Expected: code.valid is true
   - Expected: code.template_name equals `entity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
val code = cg.generate("entity", "Player")
expect(code.valid).to_equal(true)
expect(code.template_name).to_equal("entity")
expect(code.source).to_contain("Player")
expect(code.source).to_contain("x: f64")
```

</details>

#### generates component code with name substitution

1. var cg = CodeGenerator new
   - Expected: code.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
val code = cg.generate("component", "Health")
expect(code.valid).to_equal(true)
expect(code.source).to_contain("Health")
expect(code.source).to_contain("value: f64")
```

</details>

#### generates system code with name substitution

1. var cg = CodeGenerator new
   - Expected: code.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
val code = cg.generate("system", "update_physics")
expect(code.valid).to_equal(true)
expect(code.source).to_contain("update_physics")
```

</details>

#### returns invalid code for unknown template

1. var cg = CodeGenerator new
   - Expected: code.valid is false
   - Expected: code.source equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
val code = cg.generate("unknown", "Foo")
expect(code.valid).to_equal(false)
expect(code.source).to_equal("")
```

</details>

#### adds custom templates

1. var cg = CodeGenerator new
2. var custom = CodeTemplate new
3. cg add template
   - Expected: cg.template_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cg = CodeGenerator.new()
var custom = CodeTemplate.new("singleton", "Singleton pattern", "class SingletonName:\n    instance: bool")
cg.add_template(custom)
expect(cg.template_count()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/code_generator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CodeTemplate
- GeneratedCode
- CodeGenerator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
