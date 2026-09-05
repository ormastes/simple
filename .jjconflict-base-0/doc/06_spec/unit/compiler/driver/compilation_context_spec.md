# Compilation Context Specification

> Tests covering InstantiationMode, ContractMode, GenericTemplate, ConcreteType, TypeRegistry, mangle, TemplateInstantiator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compilation Context Specification

## Scenarios

### InstantiationMode

#### converts CompileTime to string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts CompileTime to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts CompileTime to string")
expect InstantiationMode.CompileTime.to_string() == "compile_time"
```

</details>

#### converts LinkTime to string

- converts LinkTime to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts LinkTime to string")
expect InstantiationMode.LinkTime.to_string() == "link_time"
```

</details>

#### converts JitTime to string

- converts JitTime to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts JitTime to string")
expect InstantiationMode.JitTime.to_string() == "jit_time"
```

</details>

### ContractMode

#### converts Off to string

- converts Off to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Off to string")
expect ContractMode.Off.to_string() == "off"
```

</details>

#### converts Boundary to string

- converts Boundary to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Boundary to string")
expect ContractMode.Boundary.to_string() == "boundary"
```

</details>

#### converts All to string

- converts All to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts All to string")
expect ContractMode.All.to_string() == "all"
```

</details>

### GenericTemplate

#### creates template with name and type params

- creates template with name and type params


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates template with name and type params")
val tmpl = GenericTemplate { name: "List", type_params: ["T"], ast_data: nil }
expect tmpl.name == "List"
expect tmpl.type_params.len() == 1
expect tmpl.type_params[0] == "T"
```

</details>

#### creates template with multiple type params

- creates template with multiple type params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates template with multiple type params")
val tmpl = GenericTemplate { name: "Map", type_params: ["K", "V"], ast_data: nil }
expect tmpl.name == "Map"
expect tmpl.type_params.len() == 2
```

</details>

#### creates template with no type params

- creates template with no type params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates template with no type params")
val tmpl = GenericTemplate { name: "Point", type_params: [], ast_data: nil }
expect tmpl.type_params.is_empty()
```

</details>

### ConcreteType

#### converts to string

- converts to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to string")
val ct = ConcreteType { name: "Int" }
expect ct.to_string() == "Int"
```

</details>

#### supports complex type names

- supports complex type names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports complex type names")
val ct = ConcreteType { name: "List<String>" }
expect ct.to_string() == "List<String>"
```

</details>

### TypeRegistry

#### creates empty registry

- creates empty registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty registry")
val reg = TypeRegistry.empty()
expect reg.types.is_empty()
```

</details>

### mangle

#### returns template name with no type args

- returns template name with no type args


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns template name with no type args")
val result = mangle("List", [])
expect result == "List"
```

</details>

#### mangles with single type arg

- mangles with single type arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mangles with single type arg")
val args = [ConcreteType { name: "Int" }]
val result = mangle("List", args)
expect result == "List$Int"
```

</details>

#### mangles with multiple type args

- mangles with multiple type args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mangles with multiple type args")
val args = [ConcreteType { name: "String" }, ConcreteType { name: "Int" }]
val result = mangle("Map", args)
expect result == "Map$String,Int"
```

</details>

#### produces unique names for different type args

- produces unique names for different type args


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces unique names for different type args")
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

- starts with empty cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty cache")
val inst = make_instantiator({})
expect inst.cache_size() == 0
```

</details>

#### reports not cached for unknown template

- reports not cached for unknown template


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports not cached for unknown template")
val inst = make_instantiator({})
expect not inst.is_cached("Unknown", [])
```

</details>

#### caches after successful instantiation

- caches after successful instantiation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches after successful instantiation")
val tmpl = GenericTemplate { name: "Simple", type_params: [], ast_data: nil }
var inst = make_instantiator({"Simple": tmpl})

val result = inst.instantiate("Simple", [])
expect result.is_ok()
expect inst.cache_size() == 1
expect inst.is_cached("Simple", [])
```

</details>

#### returns cached result on second call

- returns cached result on second call


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns cached result on second call")
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

- returns error for missing template


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for missing template")
var inst = make_instantiator({})

val result = inst.instantiate("NonExistent", [])
expect result.is_err()
```

</details>

#### detects circular dependency

- detects circular dependency


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects circular dependency")
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

- caches separately for different type args


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches separately for different type args")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/driver/compilation_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering InstantiationMode, ContractMode, GenericTemplate, ConcreteType, TypeRegistry, mangle, TemplateInstantiator.
- InstantiationMode
- ContractMode
- GenericTemplate
- ConcreteType
- TypeRegistry
- mangle
- TemplateInstantiator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1925ae08a2cf39bc81d0ad30c6919599cb7cad03b497fb4fefaeca505d6a8838`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1925ae08a2cf39bc81d0ad30c6919599cb7cad03b497fb4fefaeca505d6a8838`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1925ae08a2cf39bc81d0ad30c6919599cb7cad03b497fb4fefaeca505d6a8838`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/driver/compilation_context_spec.spl
mirror: doc/06_spec/unit/compiler/driver/compilation_context_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/driver/compilation_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/driver/compilation_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/driver/compilation_context_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts CompileTime to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/driver/compilation_context_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts LinkTime to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/driver/compilation_context_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts JitTime to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
