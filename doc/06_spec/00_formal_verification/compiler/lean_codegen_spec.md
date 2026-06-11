# Lean Codegen Specification

> <details>

<!-- sdn-diagram:id=lean_codegen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lean_codegen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lean_codegen_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lean_codegen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Codegen Specification

## Scenarios

### Lean Code Generation

#### LeanCodegenOptions

#### creates with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = LeanCodegenOptions.new()
expect(opts.module_name).to_equal("Main")
expect(opts.generate_stubs).to_equal(true)
expect(opts.output_dir).to_equal("build/lean")
```

</details>

#### updates module and output configuration

- var opts = LeanCodegenOptions new
- opts = opts with module name
- opts = opts with output dir
- opts = opts with stubs
   - Expected: opts.module_name equals `TestModule`
   - Expected: opts.output_dir equals `build/test-lean`
   - Expected: opts.generate_stubs is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = LeanCodegenOptions.new()
opts = opts.with_module_name("TestModule")
opts = opts.with_output_dir("build/test-lean")
opts = opts.with_stubs(false)
expect(opts.module_name).to_equal("TestModule")
expect(opts.output_dir).to_equal("build/test-lean")
expect(opts.generate_stubs).to_equal(false)
```

</details>

#### LeanStructure / LeanInductive / LeanFunction / LeanTheorem

#### builds structured artifacts

- var structure = LeanStructure new
- structure = structure add field
- structure = structure add field
- structure = structure derive
- var inductive = LeanInductive new
- inductive = inductive add constructor
- inductive = inductive add constructor
- var func = LeanFunction new
- func = func add param
- func = func with return type
- func = func with body
- var theorem = LeanTheorem new
- theorem = theorem add param
- theorem = theorem with proof
   - Expected: structure.name equals `Point`
   - Expected: structure.fields.len() equals `2`
   - Expected: inductive.constructors.len() equals `2`
   - Expected: func.params.len() equals `1`
   - Expected: theorem.proof equals `Some("rfl")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var structure = LeanStructure.new("Point")
structure = structure.add_field("x", "Int")
structure = structure.add_field("y", "Int")
structure = structure.derive("Repr")

var inductive = LeanInductive.new("Mode")
inductive = inductive.add_constructor("Online", [])
inductive = inductive.add_constructor("Offline", [])

var func = LeanFunction.new("identity")
func = func.add_param("x", "Nat")
func = func.with_return_type("Nat")
func = func.with_body("x")

var theorem = LeanTheorem.new("identity_refl", "identity x = x")
theorem = theorem.add_param("x", "Nat")
theorem = theorem.with_proof("rfl")

expect(structure.name).to_equal("Point")
expect(structure.fields.len()).to_equal(2)
expect(inductive.constructors.len()).to_equal(2)
expect(func.params.len()).to_equal(1)
expect(theorem.proof).to_equal(Some("rfl"))
```

</details>

#### LeanCodegen output

#### emits proof-clean Lean for explicit proofs

- var opts = LeanCodegenOptions new
- opts = opts with module name
- opts = opts with output dir
- opts = opts with stubs
- var cgen = LeanCodegen new
- cgen = cgen add structure
- cgen = cgen add inductive
- cgen = cgen add function
- cgen = cgen add theorem
   - Expected: output does not contain `sorry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = LeanCodegenOptions.new()
opts = opts.with_module_name("Demo")
opts = opts.with_output_dir("build/lean-test")
opts = opts.with_stubs(false)

var cgen = LeanCodegen.new(opts)
cgen = cgen.add_structure(build_class("point", [("x", "Int"), ("y", "Int")]))
cgen = cgen.add_inductive(build_enum_with_deriving("mode", [("online", []), ("offline", [])], ["Repr"]))
cgen = cgen.add_function(build_function("identity", [("x", "Nat")], "Nat", "x"))
cgen = cgen.add_theorem(build_theorem("identity_refl", [("x", "Nat")], "identity x = x", "rfl"))

val output = cgen.emit()
expect(output).to_contain("namespace Demo")
expect(output).to_contain("structure Point where")
expect(output).to_contain("inductive Mode where")
expect(output).to_contain("def identity")
expect(output).to_contain("theorem identity_refl")
expect(output.contains("sorry")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/lean_codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean Code Generation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
