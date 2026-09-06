# Generic Template Specification

> Tests covering Generic Template Partitioning, Monomorphization Metadata, Deferred Monomorphization, Specialization Keys, Concrete Types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Template Specification

## Scenarios

### Generic Template Partitioning

#### separates generic function into templates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- separates generic function into templates


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates generic function into templates")
val module = mini_module([make_identity_function(), make_add_function()], [])
val (templates, specialized) = mini_partition_generic_constructs(module)

check(templates.functions.len() == 1)
check_text(templates.functions[0].name, "identity")
check(specialized.functions.len() == 1)
check_text(specialized.functions[0].name, "add")
```

</details>

#### separates generic struct

- separates generic struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates generic struct")
val module = mini_module([], [make_container_struct(), make_plain_struct()])
val (templates, specialized) = mini_partition_generic_constructs(module)

check(templates.structs.len() == 1)
check_text(templates.structs[0].name, "Container")
check(specialized.structs.len() == 1)
check_text(specialized.structs[0].name, "Plain")
```

</details>

#### separates mixed generic and non-generic correctly

- separates mixed generic and non-generic correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates mixed generic and non-generic correctly")
val module = mini_module([make_identity_function(), make_add_function()], [make_container_struct()])
val (templates, specialized) = mini_partition_generic_constructs(module)

check(templates.functions.len() == 1)
check(templates.structs.len() == 1)
check(specialized.functions.len() == 1)
```

</details>

#### empty templates object has zero count

- empty templates object has zero count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty templates object has zero count")
val empty = MiniTemplates(functions: [], structs: [])

check(mini_templates_count(empty) == 0)
check(mini_templates_is_empty(empty))
```

</details>

#### templates with multiple constructs count correctly

- templates with multiple constructs count correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("templates with multiple constructs count correctly")
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

- should register function template in metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should register function template in metadata")
val templates = make_templates_with_identity()
val specialized = MiniSpecializedInstances(functions: [], structs: [])
val metadata = mini_build_metadata(templates, specialized)

check(metadata.functions.len() == 1)
check_text(metadata.functions[0].name, "identity")
check(metadata.functions[0].specializations.len() == 0)
```

</details>

#### should track specialization entry

- should track specialization entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should track specialization entry")
val templates = make_templates_with_identity()
val specialized = make_specialized_identity_int()
val metadata = mini_build_metadata(templates, specialized)

check(metadata.functions[0].specializations.len() == 1)
check_text(metadata.functions[0].specializations[0].mangled_name, "identity$Int")
```

</details>

#### should track multiple specializations

- should track multiple specializations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should track multiple specializations")
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

- should initialize with empty caches


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should initialize with empty caches")
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [], specializations: [])
val stats = mini_stats(mono)

check(stats.template_count == 0)
check(stats.specialization_count == 0)
check_text(stats.mode, "LinkTime")
```

</details>

#### cache template in monomorphizer

- cache template in monomorphizer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache template in monomorphizer")
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [make_identity_function()], specializations: [])
val retrieved = mini_get_template(mono, "identity")

check_text(retrieved, "identity")
```

</details>

#### instantiate function from template

- instantiate function from template


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instantiate function from template")
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [make_identity_function()], specializations: [])
val result = mini_instantiate_function(mono, "identity", ["Int"])

check(result.ok)
check_text(result.specialized_name, "identity$Int")
```

</details>

#### error on wrong type argument count

- error on wrong type argument count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error on wrong type argument count")
val pair_template = mini_function("pair", ["T", "U"], "")
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [pair_template], specializations: [])
val result = mini_instantiate_function(mono, "pair", ["Int"])

check(not result.ok)
check_text(result.message, "Wrong number of type args")
```

</details>

#### error on missing template

- error on missing template


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error on missing template")
val mono = MiniMonomorphizer(mode: "LinkTime", templates: [], specializations: [])
val result = mini_instantiate_function(mono, "nonexistent", ["Int"])

check(not result.ok)
check_text(result.message, "No template found")
```

</details>

#### cache specializations

- cache specializations


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache specializations")
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

- specialization keys are equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("specialization keys are equal")
val key1 = MiniSpecializationKey(name: "identity", type_args: ["Int"])
val key2 = MiniSpecializationKey(name: "identity", type_args: ["Int"])

check(mini_key_equals(key1, key2))
```

</details>

#### different type args not equal

- different type args not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different type args not equal")
val key1 = MiniSpecializationKey(name: "identity", type_args: ["Int"])
val key2 = MiniSpecializationKey(name: "identity", type_args: ["Float"])

check(not mini_key_equals(key1, key2))
```

</details>

#### nested type args in keys

- nested type args in keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested type args in keys")
val nested = mini_generic_type("Result", mini_tuple_type("Int", "String"))
val key = MiniSpecializationKey(name: "process", type_args: [nested])

check_text(key.name, "process")
check(key.type_args.len() == 1)
check_text(key.type_args[0], "Result<Tuple<Int,String>>")
```

</details>

### Concrete Types

#### differentiates primitives

- differentiates primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("differentiates primitives")
check_text(mini_primitive_type("Int"), "Int")
check_text(mini_primitive_type("Float"), "Float")
check(mini_primitive_type("Int") != mini_primitive_type("Float"))
```

</details>

#### array types with different elements

- array types with different elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array types with different elements")
val array_int = mini_array_type("Int")
val array_float = mini_array_type("Float")

check(array_int != array_float)
```

</details>

#### tuple types preserve order

- tuple types preserve order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tuple types preserve order")
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
| Source | `test/unit/compiler/mono/generic_template_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Generic Template Partitioning, Monomorphization Metadata, Deferred Monomorphization, Specialization Keys, Concrete Types.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `630d18433b244e586edbd419435d69e9ace4c278f65ce4644bef4d71886f64a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `630d18433b244e586edbd419435d69e9ace4c278f65ce4644bef4d71886f64a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `630d18433b244e586edbd419435d69e9ace4c278f65ce4644bef4d71886f64a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/compiler/mono/generic_template_spec.spl
mirror: doc/06_spec/unit/compiler/mono/generic_template_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mono/generic_template_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mono/generic_template_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mono/generic_template_spec.spl:209:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'separates generic function into templates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mono/generic_template_spec.spl:220:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'separates generic struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mono/generic_template_spec.spl:231:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'separates mixed generic and non-generic correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mono/generic_template_spec.spl:261:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should register function template in metadata' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/mono/generic_template_spec.spl:272:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should track specialization entry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/mono/generic_template_spec.spl:282:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should track multiple specializations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/mono/generic_template_spec.spl:294:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should initialize with empty caches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
