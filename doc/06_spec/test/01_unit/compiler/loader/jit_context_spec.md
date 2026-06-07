# JIT Compilation Context Specification

> JitCompilationContext implements CompilationContext for load-time JIT instantiation. It loads templates from SMF TemplateCode sections and provides:

<!-- sdn-diagram:id=jit_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_context_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JIT Compilation Context Specification

JitCompilationContext implements CompilationContext for load-time JIT instantiation. It loads templates from SMF TemplateCode sections and provides:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1041-1045 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/compiler/loader/jit_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

JitCompilationContext implements CompilationContext for load-time JIT instantiation.
It loads templates from SMF TemplateCode sections and provides:
- Template lookup from SMF
- Boundary-only contract mode (lighter than full contracts)
- Type registry management
- AOP and DI configuration integration
- Instantiation recording

## Key Features

- CompilationContext trait implementation for JIT
- SMF template loading
- Lighter contract mode for JIT (Boundary only)
- Integration with AopWeaver and DiContainer
- InstantiationEntry recording

## Implementation

File: `/home/ormastes/dev/pub/simple/src/compiler/loader/jit_context.spl`

## Architecture

```
JitCompilationContext (implements CompilationContext)
├── smf_templates: Dict<text, GenericTemplate>
├── type_reg: TypeRegistry
├── smf_aop_config: AopWeaver?
├── smf_di_config: DiContainer?
└── recorded: [InstantiationEntry]
```

## Scenarios

### JitCompilationContext Construction

#### creates with empty templates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

expect(ctx.has_template("any_template")).to_equal(false)
expect(ctx.recorded.len()).to_equal(0)
```

</details>

#### creates with templates

1. templates["Vec"] = create test template
   - Expected: ctx.has_template("Vec") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var templates: Dict<text, GenericTemplate> = {}
templates["Vec"] = create_test_template("Vec", ["T"])

val ctx = JitCompilationContext.from_smf(templates, nil, nil)

expect(ctx.has_template("Vec")).to_equal(true)
```

</details>

#### creates with AOP config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aop = create_mock_aop_weaver()
val ctx = JitCompilationContext.from_smf({}, Some(aop), nil)

val result = ctx.aop_weaver()
expect(result.?).to_equal(true)
```

</details>

#### creates with DI config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = create_mock_di_container()
val ctx = JitCompilationContext.from_smf({}, nil, Some(di))

val result = ctx.di_container()
expect(result.?).to_equal(true)
```

</details>

#### creates with both AOP and DI

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aop = create_mock_aop_weaver()
val di = create_mock_di_container()
val ctx = JitCompilationContext.from_smf({}, Some(aop), Some(di))

expect(ctx.aop_weaver().?).to_equal(true)
expect(ctx.di_container().?).to_equal(true)
```

</details>

#### initializes empty type registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

val type_reg = ctx.type_registry()
# TODO: Verify TypeRegistry.empty() properties
pass
```

</details>

#### initializes empty recorded list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

expect(ctx.recorded.len()).to_equal(0)
```

</details>

### JitCompilationContext Template Loading

#### when loading templates

#### loads existing template

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var templates: Dict<text, GenericTemplate> = {}
val vec_template = create_test_template("Vec", ["T"])
templates["Vec"] = vec_template

val ctx = JitCompilationContext.from_smf(templates, nil, nil)

val result = ctx.load_template("Vec")
expect(result.ok.?).to_equal(true)

val loaded = result.unwrap()
expect(loaded.name).to_equal("Vec")
```

</details>

#### returns error for missing template

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

val result = ctx.load_template("Missing")
expect(result.err.?).to_equal(true)

val error = result.unwrap_err()
expect(error).to_contain("not in SMF")
expect(error).to_contain("Missing")
```

</details>

#### when checking template existence

#### returns true for existing template

1. templates["Vec"] = create test template
   - Expected: ctx.has_template("Vec") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var templates: Dict<text, GenericTemplate> = {}
templates["Vec"] = create_test_template("Vec", ["T"])

val ctx = JitCompilationContext.from_smf(templates, nil, nil)

expect(ctx.has_template("Vec")).to_equal(true)
```

</details>

#### returns false for missing template

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

expect(ctx.has_template("Missing")).to_equal(false)
```

</details>

#### checks multiple templates

1. templates["Vec"] = create test template
2. templates["Option"] = create test template
   - Expected: ctx.has_template("Vec") is true
   - Expected: ctx.has_template("Option") is true
   - Expected: ctx.has_template("Result") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var templates: Dict<text, GenericTemplate> = {}
templates["Vec"] = create_test_template("Vec", ["T"])
templates["Option"] = create_test_template("Option", ["T"])

val ctx = JitCompilationContext.from_smf(templates, nil, nil)

expect(ctx.has_template("Vec")).to_equal(true)
expect(ctx.has_template("Option")).to_equal(true)
expect(ctx.has_template("Result")).to_equal(false)
```

</details>

### JitCompilationContext Interface

#### when getting contract mode

#### returns Boundary contract mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

val mode = ctx.contract_mode()
expect(mode).to_equal(ContractMode.Boundary)
```

</details>

#### when getting instantiation mode

#### returns JitTime instantiation mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

val mode = ctx.instantiation_mode()
expect(mode).to_equal(InstantiationMode.JitTime)
```

</details>

#### when getting coverage setting

#### returns false for coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

expect(ctx.coverage_enabled()).to_equal(false)
```

</details>

#### when getting type registry

#### returns type registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

val type_reg = ctx.type_registry()
# Type registry should be initialized
# TODO: Add TypeRegistry validation
pass
```

</details>

#### when getting DI container

#### returns nil when no DI config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

val di = ctx.di_container()
expect(di.?).to_equal(false)
```

</details>

#### returns DI config when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di_mock = create_mock_di_container()
val ctx = JitCompilationContext.from_smf({}, nil, Some(di_mock))

val di = ctx.di_container()
expect(di.?).to_equal(true)
```

</details>

#### when getting AOP weaver

#### returns nil when no AOP config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JitCompilationContext.from_smf({}, nil, nil)

val aop = ctx.aop_weaver()
expect(aop.?).to_equal(false)
```

</details>

#### returns AOP config when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aop_mock = create_mock_aop_weaver()
val ctx = JitCompilationContext.from_smf({}, Some(aop_mock), nil)

val aop = ctx.aop_weaver()
expect(aop.?).to_equal(true)
```

</details>

### JitCompilationContext Template Compilation

#### compiles template with type args

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Create test template and type args
# val ctx = JitCompilationContext.from_smf(templates, nil, nil)
# val template = create_test_template("Vec", ["T"])
# val type_args = [ConcreteType(name: "i64")]
# val result = ctx.compile_template(template, type_args)
# expect(result.ok.?).to_equal(true)
pass
```

</details>

#### uses Boundary contract mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Verify compile_specialized_template called with ContractMode.Boundary
pass
```

</details>

#### disables coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Verify compile_specialized_template called with coverage=false
pass
```

</details>

#### passes AOP config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Verify AOP weaver passed to compilation
pass
```

</details>

#### passes DI config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Verify DI container passed to compilation
pass
```

</details>

### JitCompilationContext Instantiation Recording

#### records single instantiation

1. var ctx = JitCompilationContext from smf
2. ctx record instantiation
   - Expected: ctx.recorded.len() equals `1`
   - Expected: ctx.recorded[0].mangled_name equals `Vec$i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = JitCompilationContext.from_smf({}, nil, nil)

val entry = create_test_instantiation_entry("Vec$i64")
ctx.record_instantiation(entry)

expect(ctx.recorded.len()).to_equal(1)
expect(ctx.recorded[0].mangled_name).to_equal("Vec$i64")
```

</details>

#### records multiple instantiations

1. var ctx = JitCompilationContext from smf
2. ctx record instantiation
3. ctx record instantiation
   - Expected: ctx.recorded.len() equals `2`
   - Expected: ctx.recorded[0].mangled_name equals `Vec$i64`
   - Expected: ctx.recorded[1].mangled_name equals `Vec$f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = JitCompilationContext.from_smf({}, nil, nil)

val entry1 = create_test_instantiation_entry("Vec$i64")
val entry2 = create_test_instantiation_entry("Vec$f64")

ctx.record_instantiation(entry1)
ctx.record_instantiation(entry2)

expect(ctx.recorded.len()).to_equal(2)
expect(ctx.recorded[0].mangled_name).to_equal("Vec$i64")
expect(ctx.recorded[1].mangled_name).to_equal("Vec$f64")
```

</details>

#### appends to recorded list

1. var ctx = JitCompilationContext from smf
   - Expected: ctx.recorded.len() equals `0`
2. ctx record instantiation
   - Expected: ctx.recorded.len() equals `1`
3. ctx record instantiation
   - Expected: ctx.recorded.len() equals `2`
4. ctx record instantiation
   - Expected: ctx.recorded.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = JitCompilationContext.from_smf({}, nil, nil)

expect(ctx.recorded.len()).to_equal(0)

ctx.record_instantiation(create_test_instantiation_entry("A"))
expect(ctx.recorded.len()).to_equal(1)

ctx.record_instantiation(create_test_instantiation_entry("B"))
expect(ctx.recorded.len()).to_equal(2)

ctx.record_instantiation(create_test_instantiation_entry("C"))
expect(ctx.recorded.len()).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
