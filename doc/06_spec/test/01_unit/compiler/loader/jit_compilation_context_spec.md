# Jit Compilation Context Specification

> 1. templates["Vec"] = build template

<!-- sdn-diagram:id=jit_compilation_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_compilation_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_compilation_context_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_compilation_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Compilation Context Specification

## Scenarios

### Jit Compilation Context

#### loads existing templates from SMF state

1. templates["Vec"] = build template
   - Expected: ctx.has_template("Vec") is true
   - Expected: ctx.has_template("Map") is false
   - Expected: ctx.load_template("Vec").is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var templates: Dict<text, TemplateBytes> = {}
templates["Vec"] = build_template("Vec", 1)
val ctx = JitCompilationContext.from_smf(templates)

expect(ctx.has_template("Vec")).to_equal(true)
expect(ctx.has_template("Map")).to_equal(false)
expect(ctx.load_template("Vec").is_ok()).to_equal(true)
```

</details>

#### reports boundary contract mode and jit_time instantiation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({})
expect(ctx.contract_mode()).to_equal("boundary")
expect(ctx.coverage_enabled()).to_equal(false)
expect(ctx.instantiation_mode()).to_equal("jit_time")
expect(ctx.di_container().?).to_equal(false)
expect(ctx.aop_weaver().?).to_equal(false)
```

</details>

#### compiles a template into a mangled specialized unit

1. templates["List"] = build template
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().name equals `List$Int`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var templates: Dict<text, TemplateBytes> = {}
templates["List"] = build_template("List", 1)
val ctx = JitCompilationContext.from_smf(templates)
val tmpl = ctx.load_template("List").unwrap()

val result = ctx.compile_template(tmpl, [make_named_type("Int")])
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().name).to_equal("List$Int")
expect(result.unwrap().bytes.len()).to_be_greater_than(0)
```

</details>

#### records instantiation attempts

1. var ctx = JitCompilationContext from smf
2. ctx record instantiation
   - Expected: ctx.recorded.len() equals `1`
   - Expected: ctx.recorded[0].mangled_name equals `Result$String`
   - Expected: ctx.recorded[0].success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = JitCompilationContext.from_smf({})
ctx.record_instantiation("Result", [make_named_type("String")], "Result$String", true, nil)

expect(ctx.recorded.len()).to_equal(1)
expect(ctx.recorded[0].mangled_name).to_equal("Result$String")
expect(ctx.recorded[0].success).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/jit_compilation_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jit Compilation Context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
