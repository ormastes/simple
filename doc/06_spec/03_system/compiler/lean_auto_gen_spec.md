# Lean Auto Gen Specification

> <details>

<!-- sdn-diagram:id=lean_auto_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lean_auto_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lean_auto_gen_spec -> spipe
lean_auto_gen_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lean_auto_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Auto Gen Specification

## Scenarios

### Lean Auto-Generation

#### AutoLeanMode

#### reports generation flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(structure_gen.AutoLeanMode.Full.generates_structures()).to_equal(true)
expect(structure_gen.AutoLeanMode.Full.generates_lookups()).to_equal(true)
expect(structure_gen.AutoLeanMode.Full.generates_beq()).to_equal(true)
expect(structure_gen.AutoLeanMode.StructureOnly.generates_structures()).to_equal(true)
expect(structure_gen.AutoLeanMode.StructureOnly.generates_lookups()).to_equal(false)
expect(structure_gen.AutoLeanMode.Skip.generates_structures()).to_equal(false)
expect(structure_gen.AutoLeanMode.Determinism.generates_theorems()).to_equal(true)
```

</details>

#### StructureGenerator

#### generates structures and inductives

1. var class def = structure gen SimpleClassDef new
2. class def = class def add field
3. class def = class def add field
4. var enum def = structure gen SimpleEnumDef new
5. enum def = enum def add variant
6. enum def = enum def add variant
7. var generator = structure gen StructureGenerator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var class_def = structure_gen.SimpleClassDef.new("TraitDef")
class_def = class_def.add_field(structure_gen.SimpleFieldDef.new("name", "text"))
class_def = class_def.add_field(structure_gen.SimpleFieldDef.new("methods", "TraitMethod").with_list())

var enum_def = structure_gen.SimpleEnumDef.new("Effect")
enum_def = enum_def.add_variant(structure_gen.SimpleEnumVariant.unit("Pure"))
enum_def = enum_def.add_variant(structure_gen.SimpleEnumVariant.unit("Io"))

var generator = structure_gen.StructureGenerator.new()
val class_out = generator.generate_structure(class_def)
val enum_out = generator.generate_inductive(enum_def)

expect(class_out).to_contain("structure TraitDef")
expect(class_out).to_contain("methods : List TraitMethod")
expect(enum_out).to_contain("inductive Effect")
expect(enum_out).to_contain("| pure")
expect(enum_out).to_contain("| io")
```

</details>

#### LookupGenerator

#### generates lookup scaffolding

1. var generator = lookup gen LookupGenerator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = lookup_gen.RegistryDef.new("Trait")
var generator = lookup_gen.LookupGenerator.new()
val env_out = generator.generate_env_type(registry)
val lookup_out = generator.generate_lookup(registry)
val contains_out = generator.generate_contains(registry)

expect(env_out).to_contain("def TraitEnv")
expect(lookup_out).to_contain("def lookupTrait")
expect(lookup_out).to_contain("Option TraitDef")
expect(contains_out).to_contain("def containsTrait")
expect(contains_out).to_contain("isSome")
```

</details>

#### InstantiationGenerator

#### generates instantiation scaffolding

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val generic_def = instantiation_gen.GenericTypeDef.new("Class")
val generator = instantiation_gen.InstantiationGenerator.new()
val out = generator.generate_instantiate(generic_def)

expect(out).to_contain("def instantiateClass")
expect(out).to_contain("typeArgs : List Ty")
expect(out).to_contain("Option ClassDef")
```

</details>

#### BeqGenerator

#### generates BEq functions and reflexivity proofs

1. var type def = beq gen BeqTypeDef new
2. type def = type def add variant
3. type def = type def add variant
4. var generator = beq gen BeqGenerator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var type_def = beq_gen.BeqTypeDef.new("Effect")
type_def = type_def.add_variant(beq_gen.BeqVariant.new("Pure", []))
type_def = type_def.add_variant(beq_gen.BeqVariant.new("Io", []))

var generator = beq_gen.BeqGenerator.new()
val fun_out = generator.generate_beq_function(type_def)
val inst_out = generator.generate_beq_instance(type_def)
val proof_out = generator.generate_reflexivity_proof(type_def)

expect(fun_out).to_contain("def Effect.beq")
expect(fun_out).to_contain(".pure, .pure => true")
expect(fun_out).to_contain("_, _ => false")
expect(inst_out).to_contain("instance : BEq Effect")
expect(proof_out).to_contain("theorem effect_beq_refl")
expect(proof_out).to_contain("rfl")
```

</details>

#### TheoremGenerator

#### generates determinism and empty lookup theorems

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val det = theorem_gen.generate_determinism_theorem("lookup_trait", [("env", "List TraitDef")], "TraitDef")
val lookup_empty = theorem_gen.generate_standard_lookup_theorems(["Trait"])

expect(det).to_contain("lookupTrait_deterministic")
expect(det).to_contain("= some r1")
expect(det).to_contain("= some r2")
expect(lookup_empty).to_contain("lookupTrait_empty")
expect(lookup_empty).to_contain("containsTrait_empty")
```

</details>

#### AutoGenerator

#### builds a proof-clean file set

1. var registry = auto gen TypeRegistry new
2. var class def = structure gen SimpleClassDef new
3. class def = class def add field
4. class def = class def add field
5. registry = registry add class
6. var enum def = structure gen SimpleEnumDef new
7. enum def = enum def add variant
8. enum def = enum def add variant
9. registry = registry add enum
10. var config = auto gen AutoGenConfig new
11. var generator = auto gen AutoGenerator new
12. generator = generator set registry
   - Expected: files.len() equals `4`
   - Expected: files[0].0 equals `Generated_Types.lean`
   - Expected: files[1].0 equals `Generated_Lookups.lean`
   - Expected: files[2].0 equals `Generated_BEq.lean`
   - Expected: files[3].0 equals `Generated_Theorems.lean`
   - Expected: files[0].1 does not contain `sorry`
   - Expected: files[1].1 does not contain `sorry`
   - Expected: files[2].1 does not contain `sorry`
   - Expected: files[3].1 does not contain `sorry`
   - Expected: files[0].1 does not contain `axiom`
   - Expected: files[1].1 does not contain `axiom`
   - Expected: files[2].1 does not contain `axiom`
   - Expected: files[3].1 does not contain `axiom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = auto_gen.TypeRegistry.new()
var class_def = structure_gen.SimpleClassDef.new("Person")
class_def = class_def.add_field(structure_gen.SimpleFieldDef.new("name", "text"))
class_def = class_def.add_field(structure_gen.SimpleFieldDef.new("age", "i32"))
registry = registry.add_class(class_def)

var enum_def = structure_gen.SimpleEnumDef.new("Mode")
enum_def = enum_def.add_variant(structure_gen.SimpleEnumVariant.unit("Online"))
enum_def = enum_def.add_variant(structure_gen.SimpleEnumVariant.unit("Offline"))
registry = registry.add_enum(enum_def)

var config = auto_gen.AutoGenConfig.new("build/lean-auto", "Demo")
var generator = auto_gen.AutoGenerator.new(config)
generator = generator.set_registry(registry)

val files = generator.generate_all()
expect(files.len()).to_equal(4)
expect(files[0].0).to_equal("Generated_Types.lean")
expect(files[1].0).to_equal("Generated_Lookups.lean")
expect(files[2].0).to_equal("Generated_BEq.lean")
expect(files[3].0).to_equal("Generated_Theorems.lean")
expect(files[0].1.contains("sorry")).to_equal(false)
expect(files[1].1.contains("sorry")).to_equal(false)
expect(files[2].1.contains("sorry")).to_equal(false)
expect(files[3].1.contains("sorry")).to_equal(false)
expect(files[0].1.contains("axiom")).to_equal(false)
expect(files[1].1.contains("axiom")).to_equal(false)
expect(files[2].1.contains("axiom")).to_equal(false)
expect(files[3].1.contains("axiom")).to_equal(false)
```

</details>

#### Type translation

#### maps Simple types to Lean types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(structure_gen.translate_type_to_lean("text", false, false)).to_equal("String")
expect(structure_gen.translate_type_to_lean("i32", false, false)).to_equal("Int")
expect(structure_gen.translate_type_to_lean("TraitDef", false, false)).to_equal("TraitDef")
```

</details>

#### Convenience functions

#### generate lookup and BEq helper output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lookups = lookup_gen.generate_standard_lookups("Trait")
val beq_output = beq_gen.generate_simple_enum_beq("Mode", ["Online", "Offline"])

expect(lookups).to_contain("lookupTrait")
expect(beq_output).to_contain("instance : BEq Mode")
expect(beq_output).to_contain("mode_beq_refl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/lean_auto_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean Auto-Generation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
