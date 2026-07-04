# Generic Template Bytecode in SMF

> Tests storage of generic function templates in the SMF (Simple Module Format) bytecode format.

<!-- sdn-diagram:id=generic_bytecode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generic_bytecode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generic_bytecode_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generic_bytecode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Template Bytecode in SMF

Tests storage of generic function templates in the SMF (Simple Module Format) bytecode format.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GENERIC-001 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/usage/generic_bytecode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests storage of generic function templates in the SMF (Simple Module Format)
bytecode format.

## Syntax

```simple
# Generic function stored in .smf
fn identity<T>(x: T) -> T: x
```

## Scenarios

### Generic Template Bytecode in SMF

#### stores generic function templates in .smf

1. templates["identity"] = build generic template
   - Expected: ctx.has_template("identity") is true
   - Expected: compiled.is_ok() is true
   - Expected: compiled.unwrap().name equals `identity$Int`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var templates: Dict<text, TemplateBytes> = {}
templates["identity"] = build_generic_template("identity", 1)
val ctx = JitCompilationContext.from_smf(templates)

expect(ctx.has_template("identity")).to_equal(true)
val loaded = ctx.load_template("identity").unwrap()
val compiled = ctx.compile_template(loaded, [make_named_type("Int")])
expect(compiled.is_ok()).to_equal(true)
expect(compiled.unwrap().name).to_equal("identity$Int")
expect(compiled.unwrap().bytes.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
