# Lean Auto Gen Specification

> Tests covering Lean Auto-Generation.

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

- reports generation flags
   - Expected: structure_gen.AutoLeanMode.Full.generates_structures() is true
   - Expected: structure_gen.AutoLeanMode.Full.generates_lookups() is true
   - Expected: structure_gen.AutoLeanMode.Full.generates_beq() is true
   - Expected: structure_gen.AutoLeanMode.StructureOnly.generates_structures() is true
   - Expected: structure_gen.AutoLeanMode.StructureOnly.generates_lookups() is false
   - Expected: structure_gen.AutoLeanMode.Skip.generates_structures() is false
   - Expected: structure_gen.AutoLeanMode.Determinism.generates_theorems() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports generation flags")
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

- generates structures and inductives


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates structures and inductives")
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

- generates lookup scaffolding


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates lookup scaffolding")
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

- generates instantiation scaffolding


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates instantiation scaffolding")
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

- generates BEq functions and reflexivity proofs


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates BEq functions and reflexivity proofs")
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

- generates determinism and empty lookup theorems


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates determinism and empty lookup theorems")
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

- builds a proof-clean file set
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

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds a proof-clean file set")
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

- maps Simple types to Lean types
   - Expected: structure_gen.translate_type_to_lean("text", false, false) equals `String`
   - Expected: structure_gen.translate_type_to_lean("i32", false, false) equals `Int`
   - Expected: structure_gen.translate_type_to_lean("TraitDef", false, false) equals `TraitDef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps Simple types to Lean types")
expect(structure_gen.translate_type_to_lean("text", false, false)).to_equal("String")
expect(structure_gen.translate_type_to_lean("i32", false, false)).to_equal("Int")
expect(structure_gen.translate_type_to_lean("TraitDef", false, false)).to_equal("TraitDef")
```

</details>

#### Convenience functions

#### generate lookup and BEq helper output

- generate lookup and BEq helper output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generate lookup and BEq helper output")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lean Auto-Generation.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ecc6d828e4e1edf57a5038d38e66d994b8d6b659a928620fcb951c9985b7c685`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecc6d828e4e1edf57a5038d38e66d994b8d6b659a928620fcb951c9985b7c685`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecc6d828e4e1edf57a5038d38e66d994b8d6b659a928620fcb951c9985b7c685`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/compiler/lean_auto_gen_spec.spl
mirror: doc/06_spec/03_system/compiler/lean_auto_gen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/lean_auto_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/lean_auto_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/lean_auto_gen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/lean_auto_gen_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports generation flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/lean_auto_gen_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates structures and inductives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/lean_auto_gen_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates lookup scaffolding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
