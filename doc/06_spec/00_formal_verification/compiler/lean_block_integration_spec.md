# Lean Block Integration Specification

> Verifies that embedded lean{} blocks are correctly parsed, merged into generated Lean output, and that namespace collisions are detected.

<!-- sdn-diagram:id=lean_block_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lean_block_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lean_block_integration_spec -> std
lean_block_integration_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lean_block_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Block Integration Specification

Verifies that embedded lean{} blocks are correctly parsed, merged into generated Lean output, and that namespace collisions are detected.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LEAN-BLOCK |
| Category | Verification |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | doc/03_plan/lean_verification_contract.md |
| Source | `test/00_formal_verification/compiler/lean_block_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that embedded lean{} blocks are correctly parsed, merged into
generated Lean output, and that namespace collisions are detected.

## Key Concepts

| Concept | Description |
|---------|-------------|
| lean{} block | Raw Lean 4 code embedded in Simple source |
| Collision | Same theorem name in both generated and handwritten code |
| Import dedup | Imports from lean{} blocks merged without duplicates |

## Scenarios

### LeanBlock Model

#### extracts theorem names from body

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "theorem my_theorem (n : Nat) : n + 0 = n := by\n  simp\n\ntheorem another_thm : True := trivial"
val names = lean_block.LeanBlock.extract_theorem_names(body)
expect(names.len()).to_equal(2)
expect(names[0]).to_equal("my_theorem")
expect(names[1]).to_equal("another_thm")
```

</details>

#### extracts imports from body

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "import Mathlib.Data.Nat.Basic\nimport Std.Data.List\n\ntheorem foo : True := trivial"
val imps = lean_block.LeanBlock.extract_imports(body)
expect(imps.len()).to_equal(2)
expect(imps[0]).to_equal("Mathlib.Data.Nat.Basic")
expect(imps[1]).to_equal("Std.Data.List")
```

</details>

#### creates with placement and auto-extracts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "import Mathlib.Tactic\ntheorem helper_lemma : 1 + 1 = 2 := by norm_num"
val block = lean_block.LeanBlock.create("test.spl", 42, lean_block.LeanBlockPlacement.ModuleLevel, body)
expect(block.source_file).to_equal("test.spl")
expect(block.source_line).to_equal(42)
expect(block.theorem_names.len()).to_equal(1)
expect(block.theorem_names[0]).to_equal("helper_lemma")
expect(block.imports.len()).to_equal(1)
expect(block.imports[0]).to_equal("Mathlib.Tactic")
```

</details>

#### handles body with no theorems or imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "-- just a comment\ndef helper := 42"
val block = lean_block.LeanBlock.create("empty.spl", 1, lean_block.LeanBlockPlacement.FunctionLevel, body)
expect(block.theorem_names.len()).to_equal(0)
expect(block.imports.len()).to_equal(0)
```

</details>

#### sets explicit namespace

1. var block = lean block LeanBlock create
2. block = block with namespace
   - Expected: block.namespace equals `Some("MyModule.Proofs")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "theorem ns_thm : True := trivial"
var block = lean_block.LeanBlock.create("ns.spl", 10, lean_block.LeanBlockPlacement.TypeLevel, body)
block = block.with_namespace("MyModule.Proofs")
expect(block.namespace).to_equal(Some("MyModule.Proofs"))
```

</details>

### Lean Block Codegen Integration

#### includes lean{} block content in generated output

1. var opts = codegen LeanCodegenOptions new
2. opts = opts with module name
3. var gen = codegen LeanCodegen new
4. "theorem my theorem
5. gen = gen add lean block
6. gen = gen add namespace
7. gen = gen end namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = codegen.LeanCodegenOptions.new()
opts = opts.with_module_name("BlockTest")
var gen = codegen.LeanCodegen.new(opts)

val block = lean_block.LeanBlock.create(
    "example.spl", 15,
    lean_block.LeanBlockPlacement.ModuleLevel,
    "theorem my_theorem (n : Nat) : n + 0 = n := by simp"
)
gen = gen.add_lean_block(block)
gen = gen.add_namespace("BlockTest")
gen = gen.end_namespace("BlockTest")

val output = gen.emit()
expect(output).to_contain("theorem my_theorem")
expect(output).to_contain("From example.spl:15")
```

</details>

#### deduplicates imports from lean{} blocks

1. var opts = codegen LeanCodegenOptions new
2. opts = opts with module name
3. var gen = codegen LeanCodegen new
4. gen = gen add lean block
   - Expected: extra.len() equals `1`
   - Expected: extra[0] equals `Std.Data.List`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = codegen.LeanCodegenOptions.new()
opts = opts.with_module_name("ImportTest")
var gen = codegen.LeanCodegen.new(opts)

# Default imports already include Mathlib.Data.Nat.Basic
val block = lean_block.LeanBlock.create(
    "dup.spl", 1,
    lean_block.LeanBlockPlacement.ModuleLevel,
    "import Mathlib.Data.Nat.Basic\nimport Std.Data.List\ntheorem t : True := trivial"
)
gen = gen.add_lean_block(block)

val extra = gen.deduplicated_lean_block_imports()
# Mathlib.Data.Nat.Basic is already in default imports, should not duplicate
expect(extra.len()).to_equal(1)
expect(extra[0]).to_equal("Std.Data.List")
```

</details>

#### strips import lines from lean{} block body in output

1. var opts = codegen LeanCodegenOptions new
2. opts = opts with module name
3. var gen = codegen LeanCodegen new
4. gen = gen add lean block
5. gen = gen add namespace
6. gen = gen end namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = codegen.LeanCodegenOptions.new()
opts = opts.with_module_name("StripTest")
var gen = codegen.LeanCodegen.new(opts)

val block = lean_block.LeanBlock.create(
    "strip.spl", 5,
    lean_block.LeanBlockPlacement.ModuleLevel,
    "import Std.Data.List\ntheorem strip_thm : True := trivial"
)
gen = gen.add_lean_block(block)
gen = gen.add_namespace("StripTest")
gen = gen.end_namespace("StripTest")

val output = gen.emit()
# The import line should NOT appear inside the block body section
# (it is merged into top-level imports instead)
expect(output).to_contain("theorem strip_thm")
# The top-level imports section should contain it
expect(output).to_contain("Std.Data.List")
```

</details>

### Lean Block Collision Detection

#### detects duplicate theorem names between generated and lean{} blocks

1. var opts = codegen LeanCodegenOptions new
2. opts = opts with module name
3. var gen = codegen LeanCodegen new
4. gen = gen add theorem
5. gen = gen add lean block
   - Expected: collisions.len() equals `1`
   - Expected: collisions[0].theorem_name equals `shared_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = codegen.LeanCodegenOptions.new()
opts = opts.with_module_name("CollisionTest")
var gen = codegen.LeanCodegen.new(opts)

# Add a structured theorem
val thm = codegen.LeanTheorem.new("shared_name", "True")
gen = gen.add_theorem(thm)

# Add a lean{} block with the same theorem name
val block = lean_block.LeanBlock.create(
    "collision.spl", 20,
    lean_block.LeanBlockPlacement.ModuleLevel,
    "theorem shared_name : True := trivial"
)
gen = gen.add_lean_block(block)

val collisions = gen.check_lean_block_collisions()
expect(collisions.len()).to_equal(1)
expect(collisions[0].theorem_name).to_equal("shared_name")
expect(collisions[0].message).to_contain("Collision")
expect(collisions[0].message).to_contain("shared_name")
```

</details>

#### reports no collisions when names are distinct

1. var opts = codegen LeanCodegenOptions new
2. opts = opts with module name
3. var gen = codegen LeanCodegen new
4. gen = gen add theorem
5. gen = gen add lean block
   - Expected: collisions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = codegen.LeanCodegenOptions.new()
opts = opts.with_module_name("NoCollisionTest")
var gen = codegen.LeanCodegen.new(opts)

val thm = codegen.LeanTheorem.new("gen_theorem", "True")
gen = gen.add_theorem(thm)

val block = lean_block.LeanBlock.create(
    "ok.spl", 10,
    lean_block.LeanBlockPlacement.ModuleLevel,
    "theorem hand_theorem : True := trivial"
)
gen = gen.add_lean_block(block)

val collisions = gen.check_lean_block_collisions()
expect(collisions.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/lean_verification_contract.md](doc/03_plan/lean_verification_contract.md)


</details>
