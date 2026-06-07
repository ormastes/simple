# Linker Context Specification

> 1. templates["Array"] = GenericTemplate

<!-- sdn-diagram:id=linker_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linker_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linker_context_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linker_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linker Context Specification

## Scenarios

### Linker Context

#### loads templates from the provided object map

1. templates["Array"] = GenericTemplate
   - Expected: ctx.has_template("Array") is true
   - Expected: ctx.has_template("Vec") is false
   - Expected: loaded.is_ok() is true
   - Expected: loaded.unwrap().name equals `Array`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var templates: Dict<text, GenericTemplate> = {}
templates["Array"] = GenericTemplate(name: "Array", type_params: ["T"], ast_data: nil)

val ctx = linkercompilationcontext_from_objects(templates, nil, nil)
expect(ctx.has_template("Array")).to_equal(true)
expect(ctx.has_template("Vec")).to_equal(false)

val loaded = ctx.load_template("Array")
expect(loaded.is_ok()).to_equal(true)
expect(loaded.unwrap().name).to_equal("Array")
```

</details>

#### reports linker-specific modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = linkercompilationcontext_from_objects({}, nil, nil)
expect(ctx.contract_mode()).to_equal(ContractMode.All)
expect(ctx.coverage_enabled()).to_equal(false)
expect(ctx.instantiation_mode()).to_equal(InstantiationMode.LinkTime)
expect(ctx.recorded.len()).to_equal(0)
```

</details>

#### returns an error for missing templates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = linkercompilationcontext_from_objects({}, nil, nil)
val result = ctx.load_template("Missing")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("Template not in objects")
```

</details>

#### records instantiation metadata entries

1. var ctx = linkercompilationcontext from objects
   - Expected: ctx.recorded.len() equals `1`
   - Expected: ctx.recorded[0].mangled_name equals `Vec$i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = linkercompilationcontext_from_objects({}, nil, nil)
ctx.record_instantiation(InstantiationEntry(
    id: 0,
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "Vec$i64",
    from_file: "main.spl",
    from_loc: "1:1",
    to_obj: "main.smf",
    status: "completed"
))

expect(ctx.recorded.len()).to_equal(1)
expect(ctx.recorded[0].mangled_name).to_equal("Vec$i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/linker_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Linker Context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
