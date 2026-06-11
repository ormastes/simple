# Generic Template Specification

> 1. check

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

1. check
2. check text
3. check
4. check text


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

1. check
2. check text
3. check
4. check text


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

1. check
2. check
3. check


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

1. check
2. check


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

1. functions: [make identity function
2. structs: [make container struct
3. check
4. check


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

1. check
2. check text
3. check


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

1. check
2. check text


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

1. check
2. check text
3. check text


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

1. check
2. check
3. check text


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

1. check text


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

1. check
2. check text


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

1. check
2. check text


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

1. check
2. check text


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

1. templates: [make identity function
2. specializations: [mini function
3. check
4. check
5. check text


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

1. check


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

1. check


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

1. check text
2. check
3. check text


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

1. check text
2. check text
3. check


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

1. check


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

1. check text
2. check


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
| Updated | 2026-06-01 |
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
