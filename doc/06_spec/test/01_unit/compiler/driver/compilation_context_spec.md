# Unified CompilationContext Specification

> The CompilationContext trait provides a unified compilation interface for compiler, JIT loader, and linker. All three paths use it to ensure AOP/DI/contracts are applied consistently.

<!-- sdn-diagram:id=compilation_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compilation_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compilation_context_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compilation_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified CompilationContext Specification

The CompilationContext trait provides a unified compilation interface for compiler, JIT loader, and linker. All three paths use it to ensure AOP/DI/contracts are applied consistently.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CC-001 to #CC-030 |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/01_unit/compiler/driver/compilation_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The CompilationContext trait provides a unified compilation interface for
compiler, JIT loader, and linker. All three paths use it to ensure
AOP/DI/contracts are applied consistently.

## Key Concepts

| Concept | Description |
|---------|-------------|
| CompilationContext | Trait: load_template, compile_template, record_instantiation |
| TemplateInstantiator | Shared cache + cycle detection, delegates to context |
| InstantiationMode | When instantiation occurs: CompileTime, LinkTime, JitTime |
| ContractMode | How much checking: Off, Boundary, All |
| GenericTemplate | Template AST data with type parameters |
| ConcreteType | Concrete type used for instantiation |

## Behavior

- All three contexts implement the same trait
- TemplateInstantiator caches compiled units by mangled name
- Cycle detection prevents infinite recursion
- Each context uses its own template source (AST cache, SMF, objects)
- Pipeline: monomorphize -> HIR -> MIR -> AOP -> codegen

## Scenarios

### InstantiationMode

#### converts CompileTime to string

1. expect InstantiationMode CompileTime to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect InstantiationMode.CompileTime.to_string() == "compile_time"
```

</details>

#### converts LinkTime to string

1. expect InstantiationMode LinkTime to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect InstantiationMode.LinkTime.to_string() == "link_time"
```

</details>

#### converts JitTime to string

1. expect InstantiationMode JitTime to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect InstantiationMode.JitTime.to_string() == "jit_time"
```

</details>

### ContractMode

#### converts Off to string

1. expect ContractMode Off to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ContractMode.Off.to_string() == "off"
```

</details>

#### converts Boundary to string

1. expect ContractMode Boundary to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ContractMode.Boundary.to_string() == "boundary"
```

</details>

#### converts All to string

1. expect ContractMode All to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ContractMode.All.to_string() == "all"
```

</details>

### GenericTemplate

#### creates template with name and type params

1. expect tmpl type params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = GenericTemplate { name: "List", type_params: ["T"], ast_data: nil }
expect tmpl.name == "List"
expect tmpl.type_params.len() == 1
expect tmpl.type_params[0] == "T"
```

</details>

#### creates template with multiple type params

1. expect tmpl type params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = GenericTemplate { name: "Map", type_params: ["K", "V"], ast_data: nil }
expect tmpl.name == "Map"
expect tmpl.type_params.len() == 2
```

</details>

#### creates template with no type params

1. expect tmpl type params is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = GenericTemplate { name: "Point", type_params: [], ast_data: nil }
expect tmpl.type_params.is_empty()
```

</details>

### ConcreteType

#### converts to string

1. expect ct to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = ConcreteType { name: "Int" }
expect ct.to_string() == "Int"
```

</details>

#### supports complex type names

1. expect ct to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = ConcreteType { name: "List<String>" }
expect ct.to_string() == "List<String>"
```

</details>

### TypeRegistry

#### creates empty registry

1. expect reg types is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = TypeRegistry.empty()
expect reg.types.is_empty()
```

</details>

### mangle

#### returns template name with no type args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mangle("List", [])
expect result == "List"
```

</details>

#### mangles with single type arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = [ConcreteType { name: "Int" }]
val result = mangle("List", args)
expect result == "List$Int"
```

</details>

#### mangles with multiple type args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = [ConcreteType { name: "String" }, ConcreteType { name: "Int" }]
val result = mangle("Map", args)
expect result == "Map$String,Int"
```

</details>

#### produces unique names for different type args

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args1 = [ConcreteType { name: "Int" }]
val args2 = [ConcreteType { name: "String" }]
val name1 = mangle("List", args1)
val name2 = mangle("List", args2)
expect name1 != name2
```

</details>

### TemplateInstantiator

#### cache behavior

#### starts with empty cache

1. expect inst cache size


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = make_instantiator({})
expect inst.cache_size() == 0
```

</details>

#### reports not cached for unknown template

1. expect not inst is cached


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = make_instantiator({})
expect not inst.is_cached("Unknown", [])
```

</details>

#### caches after successful instantiation

1. var inst = make instantiator
2. expect result is ok
3. expect inst cache size
4. expect inst is cached


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = GenericTemplate { name: "Simple", type_params: [], ast_data: nil }
var inst = make_instantiator({"Simple": tmpl})

val result = inst.instantiate("Simple", [])
expect result.is_ok()
expect inst.cache_size() == 1
expect inst.is_cached("Simple", [])
```

</details>

#### returns cached result on second call

1. var inst = make instantiator
2. expect result1 is ok
3. expect result2 is ok
4. expect inst cache size


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = GenericTemplate { name: "Pair", type_params: ["A", "B"], ast_data: nil }
var inst = make_instantiator({"Pair": tmpl})

val args = [ConcreteType { name: "Int" }, ConcreteType { name: "String" }]
val result1 = inst.instantiate("Pair", args)
val result2 = inst.instantiate("Pair", args)
expect result1.is_ok()
expect result2.is_ok()
expect inst.cache_size() == 1
```

</details>

#### error handling

#### returns error for missing template

1. var inst = make instantiator
2. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inst = make_instantiator({})

val result = inst.instantiate("NonExistent", [])
expect result.is_err()
```

</details>

#### detects circular dependency

1. in progress = in progress insert
2. expect result is err
3. expect err msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val load_fn = \name: Err("not found")
val compile_fn = \tmpl, args: Err("not found")
var in_progress = {}
in_progress = in_progress.insert("Recursive")
var inst = TemplateInstantiator { load_fn: load_fn, compile_fn: compile_fn, in_progress: in_progress, cache: {} }

val result = inst.instantiate("Recursive", [])
expect result.is_err()
val err_msg = result.unwrap_err()
expect err_msg.contains("Circular dependency")
```

</details>

#### different type arguments

#### caches separately for different type args

1. var inst = make instantiator
2. expect result1 is ok
3. expect result2 is ok
4. expect inst cache size
5. expect inst is cached
6. expect inst is cached


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = GenericTemplate { name: "Box", type_params: ["T"], ast_data: nil }
var inst = make_instantiator({"Box": tmpl})

val result1 = inst.instantiate("Box", [ConcreteType { name: "Int" }])
val result2 = inst.instantiate("Box", [ConcreteType { name: "String" }])
expect result1.is_ok()
expect result2.is_ok()
expect inst.cache_size() == 2
expect inst.is_cached("Box", [ConcreteType { name: "Int" }])
expect inst.is_cached("Box", [ConcreteType { name: "String" }])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
