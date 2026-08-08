# Generic Template Specification

> <details>

<!-- sdn-diagram:id=generic_template_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generic_template_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generic_template_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generic_template_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Template Specification

## Scenarios

### Generic Template Partitioning

#### separates generic function into templates

- check
- check text
- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = mini_module([make_identity_function(), make_add_function()], [])
val (templates, specialized) = mini_partition_generic_constructs(module)

check(templates.functions.len() == 1)
check_text(templates.functions[0].name, "identity")
check(specialized.functions.len() == 1)
check_text(specialized.functions[0].name, "add")
```

</details>

#### separates generic struct

- check
- check text
- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = mini_module([], [make_container_struct(), make_plain_struct()])
val (templates, specialized) = mini_partition_generic_constructs(module)

check(templates.structs.len() == 1)
check_text(templates.structs[0].name, "Container")
check(specialized.structs.len() == 1)
check_text(specialized.structs[0].name, "Plain")
```

</details>

#### separates mixed generic and non-generic correctly

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = mini_module([make_identity_function(), make_add_function()], [make_container_struct()])
val (templates, specialized) = mini_partition_generic_constructs(module)

check(templates.functions.len() == 1)
check(templates.structs.len() == 1)
check(specialized.functions.len() == 1)
```

</details>

#### empty templates object has zero count

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = MiniTemplates(functions: [], structs: [])

check(mini_templates_count(empty) == 0)
check(mini_templates_is_empty(empty))
```

</details>

#### templates with multiple constructs count correctly

- functions: [make identity function
- structs: [make container struct
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val templates = MiniTemplates(
    functions: [make_identity_function()],
    structs: [make_container_struct(), make_plain_struct()]
)

check(mini_templates_count(templates) > 1)
check(not mini_templates_is_empty(templates))
```

</details>

### Monomorphization Metadata

#### should register function template in metadata

- check
- check text
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val templates = make_templates_with_identity()
val specialized = MiniSpecializedInstances(functions: [], structs: [])
val metadata = mini_build_metadata(templates, specialized)

check(metadata.functions.len() == 1)
check_text(metadata.functions[0].name, "identity")
check(metadata.functions[0].specializations.len() == 0)
```

</details>

#### should track specialization entry

- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val templates = make_templates_with_identity()
val specialized = make_specialized_identity_int()
val metadata = mini_build_metadata(templates, specialized)

check(metadata.functions[0].specializations.len() == 1)
check_text(metadata.functions[0].specializations[0].mangled_name, "identity$Int")
```

</details>

#### should track multiple specializations

- check
- check text
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val templates = MiniTemplates(functions: [mini_function("square", ["T"], "")], structs: [])
val specialized = make_specialized_square_pair()
val metadata = mini_build_metadata(templates, specialized)

check(metadata.functions[0].specializations.len() == 2)
check_text(metadata.functions[0].specializations[0].mangled_name, "square$Int")
check_text(metadata.functions[0].specializations[1].mangled_name, "square$Float")
```

</details>

### Deferred Monomorphization

#### should initialize with empty caches

- check
- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [], specializations: [])
val stats = mini_stats(mono)

check(stats.template_count == 0)
check(stats.specialization_count == 0)
check_text(stats.mode, "LinkTime")
```

</details>

#### cache template in monomorphizer

- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [make_identity_function()], specializations: [])
val retrieved = mini_get_template(mono, "identity")

check_text(retrieved, "identity")
```

</details>

#### instantiate function from template

- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [make_identity_function()], specializations: [])
val result = mini_instantiate_function(mono, "identity", ["Int"])

check(result.ok)
check_text(result.specialized_name, "identity$Int")
```

</details>

#### error on wrong type argument count

- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair_template = mini_function("pair", ["T", "U"], "")
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [pair_template], specializations: [])
val result = mini_instantiate_function(mono, "pair", ["Int"])

check(not result.ok)
check_text(result.message, "Wrong number of type args")
```

</details>

#### error on missing template

- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [], specializations: [])
val result = mini_instantiate_function(mono, "nonexistent", ["Int"])

check(not result.ok)
check_text(result.message, "No template found")
```

</details>

#### cache specializations

- templates: [make identity function
- specializations: [mini function
- check
- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mono = MiniMonomorphizer(
    mode: "JitTime",
    templates: [make_identity_function()],
    specializations: [mini_function("identity$Int", [], "identity")]
)
val stats = mini_stats(mono)

check(stats.template_count == 1)
check(stats.specialization_count == 1)
check_text(mini_get_template(mono, "identity"), "identity")
```

</details>

### Specialization Keys

#### specialization keys are equal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key1 = MiniSpecializationKey(name: "identity", type_args: ["Int"])
val key2 = MiniSpecializationKey(name: "identity", type_args: ["Int"])

check(mini_key_equals(key1, key2))
```

</details>

#### different type args not equal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key1 = MiniSpecializationKey(name: "identity", type_args: ["Int"])
val key2 = MiniSpecializationKey(name: "identity", type_args: ["Float"])

check(not mini_key_equals(key1, key2))
```

</details>

#### nested type args in keys

- check text
- check
- check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = mini_generic_type("Result", mini_tuple_type("Int", "String"))
val key = MiniSpecializationKey(name: "process", type_args: [nested])

check_text(key.name, "process")
check(key.type_args.len() == 1)
check_text(key.type_args[0], "Result<Tuple<Int,String>>")
```

</details>

### Concrete Types

#### differentiates primitives

- check text
- check text
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(mini_primitive_type("Int"), "Int")
check_text(mini_primitive_type("Float"), "Float")
check(mini_primitive_type("Int") != mini_primitive_type("Float"))
```

</details>

#### array types with different elements

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val array_int = mini_array_type("Int")
val array_float = mini_array_type("Float")

check(array_int != array_float)
```

</details>

#### tuple types preserve order

- check text
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tuple = mini_tuple_type("Int", "String")

check_text(tuple, "Tuple<Int,String>")
check(tuple != mini_tuple_type("String", "Int"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/generic_template_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generic Template Partitioning
- Monomorphization Metadata
- Deferred Monomorphization
- Specialization Keys
- Concrete Types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
