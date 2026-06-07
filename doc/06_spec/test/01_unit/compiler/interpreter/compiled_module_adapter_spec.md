# Compiled Module Adapter Specification

> Tests for CompiledCallable factory functions and the compiled module registry (cmr_*).

<!-- sdn-diagram:id=compiled_module_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiled_module_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiled_module_adapter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiled_module_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiled Module Adapter Specification

Tests for CompiledCallable factory functions and the compiled module registry (cmr_*).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SMF-004 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | In Progress |
| Plan | doc/03_plan/smf_load_enable_plan.md |
| Source | `test/01_unit/compiler/interpreter/compiled_module_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for CompiledCallable factory functions and the compiled module registry (cmr_*).

## Scenarios

### CompiledCallable

#### creates AST callable with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = compiled_callable_from_ast("my_fn", 42, "std.text", 3)
expect(c.name).to_equal("my_fn")
expect(c.origin_kind).to_equal("ast")
expect(c.decl_id).to_equal(42)
expect(c.module_name).to_equal("std.text")
expect(c.param_count).to_equal(3)
```

</details>

#### creates compiled symbol callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = compiled_callable_from_symbol("add", 1000, "_simple_add", "std.math", 2)
expect(c.name).to_equal("add")
expect(c.origin_kind).to_equal("compiled")
expect(c.address).to_equal(1000)
expect(c.symbol_name).to_equal("_simple_add")
```

</details>

#### creates JIT callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = compiled_callable_from_jit("sort", 2000, "sort_T", "i64", "std.algo", 1)
expect(c.name).to_equal("sort")
expect(c.origin_kind).to_equal("jit")
expect(c.address).to_equal(2000)
expect(c.template_name).to_equal("sort_T")
expect(c.type_args).to_equal("i64")
```

</details>

### CompiledModuleRegistry

#### starts empty after init

1. cmr init
   - Expected: cmr_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cmr_init()
expect(cmr_count()).to_equal(0)
```

</details>

#### registers and looks up a callable

1. cmr init
2. cmr register
   - Expected: cmr_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cmr_init()
val c = compiled_callable_from_ast("my_fn", 1, "mod_a", 2)
cmr_register(c)
val found = cmr_lookup("my_fn")
expect(found).to_be(found)  # not nil
expect(cmr_count()).to_equal(1)
```

</details>

#### returns nil for unknown name

1. cmr init


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cmr_init()
val found = cmr_lookup("nonexistent")
expect(found).to_be_nil()
```

</details>

#### tracks module membership

1. cmr init
   - Expected: cmr_has_module("mod_a") is false
2. cmr register
   - Expected: cmr_has_module("mod_a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cmr_init()
expect(cmr_has_module("mod_a")).to_equal(false)
val c = compiled_callable_from_ast("fn1", 1, "mod_a", 0)
cmr_register(c)
expect(cmr_has_module("mod_a")).to_equal(true)
```

</details>

#### tracks module exports as comma-separated names

1. cmr init
2. cmr register
3. cmr register


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cmr_init()
cmr_register(compiled_callable_from_ast("fn1", 1, "mod_a", 0))
cmr_register(compiled_callable_from_ast("fn2", 2, "mod_a", 1))
val exports = cmr_get_module_exports("mod_a")
expect(exports).to_contain("fn1")
expect(exports).to_contain("fn2")
```

</details>

#### returns empty string for unknown module exports

1. cmr init
   - Expected: cmr_get_module_exports("unknown") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cmr_init()
expect(cmr_get_module_exports("unknown")).to_equal("")
```

</details>

#### overwrites existing entry with same name

1. cmr init
2. cmr register
3. cmr register
   - Expected: cmr_count() equals `1`
   - Expected: found.decl_id equals `99`
   - Expected: found.param_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cmr_init()
cmr_register(compiled_callable_from_ast("fn1", 1, "mod_a", 0))
cmr_register(compiled_callable_from_ast("fn1", 99, "mod_a", 3))
expect(cmr_count()).to_equal(1)
val found = cmr_lookup("fn1")
expect(found.decl_id).to_equal(99)
expect(found.param_count).to_equal(3)
```

</details>

#### unloads module entries

1. cmr init
2. cmr register
3. cmr register
4. cmr unload module
   - Expected: cmr_has_module("mod_a") is false
   - Expected: cmr_has_module("mod_b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cmr_init()
cmr_register(compiled_callable_from_ast("fn1", 1, "mod_a", 0))
cmr_register(compiled_callable_from_ast("fn2", 2, "mod_b", 0))
cmr_unload_module("mod_a")
expect(cmr_has_module("mod_a")).to_equal(false)
expect(cmr_has_module("mod_b")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/smf_load_enable_plan.md](doc/03_plan/smf_load_enable_plan.md)


</details>
