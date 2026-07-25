# Proof Reference Resolution Specification

> Verifies that proof references from @verify annotations resolve correctly to external .lean files, and that collision detection between generated and handwritten theorems works as expected.

<!-- sdn-diagram:id=proof_reference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=proof_reference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

proof_reference_spec -> std
proof_reference_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=proof_reference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Proof Reference Resolution Specification

Verifies that proof references from @verify annotations resolve correctly to external .lean files, and that collision detection between generated and handwritten theorems works as expected.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LEAN-PROOF-REF |
| Category | Verification |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | doc/03_plan/lean_verification_contract.md |
| Source | `test/00_formal_verification/compiler/proof_reference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that proof references from @verify annotations resolve correctly
to external .lean files, and that collision detection between generated
and handwritten theorems works as expected.

## Key Concepts

| Concept | Description |
|---------|-------------|
| ProofReference | Maps a Simple symbol to a Lean theorem name |
| ProofRefResolver | Searches directories for .lean files containing proofs |
| CollisionError | Detects duplicate theorem names with origin info |

## Scenarios

### ProofReference Model

#### creates a reference with source symbol and theorem name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = proof_ref.ProofReference.create("my_function", "my_function_correct")
expect(ref.source_symbol).to_equal("my_function")
expect(ref.theorem_name).to_equal("my_function_correct")
expect(ref.proof_module).to_equal("")
expect(ref.proof_file).to_equal("")
```

</details>

### CollisionError

#### creates error with both origin sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = proof_ref.CollisionError.create(
    "theorem_x",
    "generated.spl:42",
    "proofs/manual.lean:10"
)
expect(err.theorem_name).to_equal("theorem_x")
expect(err.generated_source).to_equal("generated.spl:42")
expect(err.handwritten_source).to_equal("proofs/manual.lean:10")
expect(err.message).to_contain("Collision")
expect(err.message).to_contain("theorem_x")
expect(err.message).to_contain("generated.spl:42")
expect(err.message).to_contain("proofs/manual.lean:10")
```

</details>

### ProofRefResult

#### creates found result with path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = proof_ref.ProofReference.create("fn_a", "fn_a_safe")
val result = proof_ref.ProofRefResult.found(ref, "proofs/fn_a.lean")
expect(result.status).to_equal(proof_ref.ProofRefStatus.Found)
expect(result.resolved_path).to_equal(Some("proofs/fn_a.lean"))
expect(result.error_message).to_be_nil()
```

</details>

#### creates not_found result with error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = proof_ref.ProofReference.create("fn_b", "fn_b_safe")
val result = proof_ref.ProofRefResult.not_found(ref, ["proofs/", "lib/proofs/"])
expect(result.status).to_equal(proof_ref.ProofRefStatus.NotFound)
expect(result.resolved_path).to_be_nil()
expect(result.error_message).to_contain("not found")
expect(result.error_message).to_contain("fn_b_safe")
```

</details>

#### creates ambiguous result with candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = proof_ref.ProofReference.create("fn_c", "fn_c_thm")
val result = proof_ref.ProofRefResult.ambiguous(ref, ["a/proof.lean", "b/proof.lean"])
expect(result.status).to_equal(proof_ref.ProofRefStatus.Ambiguous)
expect(result.candidates.len()).to_equal(2)
expect(result.error_message).to_contain("Ambiguous")
expect(result.error_message).to_contain("fn_c_thm")
```

</details>

### ProofRefResolver

#### registers references

1. var resolver = proof ref ProofRefResolver new
2. resolver = resolver register
3. resolver = resolver register
   - Expected: resolver.references.len() equals `2`
   - Expected: resolver.references[0].theorem_name equals `sort_correct`
   - Expected: resolver.references[1].theorem_name equals `search_terminates`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = proof_ref.ProofRefResolver.new(["proofs/"])
resolver = resolver.register("sort", "sort_correct")
resolver = resolver.register("search", "search_terminates")
expect(resolver.references.len()).to_equal(2)
expect(resolver.references[0].theorem_name).to_equal("sort_correct")
expect(resolver.references[1].theorem_name).to_equal("search_terminates")
```

</details>

#### resolves with empty search paths to not_found

1. var resolver = proof ref ProofRefResolver new
2. resolver = resolver register
   - Expected: results.len() equals `1`
   - Expected: results[0].status equals `proof_ref.ProofRefStatus.NotFound`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = proof_ref.ProofRefResolver.new([])
resolver = resolver.register("missing", "missing_thm")
val results = resolver.resolve_all()
expect(results.len()).to_equal(1)
expect(results[0].status).to_equal(proof_ref.ProofRefStatus.NotFound)
```

</details>

### Collision Detection

#### finds collisions between generated and handwritten theorems

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val generated = ["thm_a", "thm_b", "thm_shared"]
val handwritten = ["thm_c", "thm_shared", "thm_d"]
val errors = proof_ref.ProofRefResolver.check_collisions(generated, handwritten)
expect(errors.len()).to_equal(1)
expect(errors[0].theorem_name).to_equal("thm_shared")
```

</details>

#### returns empty list when no collisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val generated = ["gen_1", "gen_2"]
val handwritten = ["hw_1", "hw_2"]
val errors = proof_ref.ProofRefResolver.check_collisions(generated, handwritten)
expect(errors.len()).to_equal(0)
```

</details>

#### finds multiple collisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val generated = ["shared_a", "unique_gen", "shared_b"]
val handwritten = ["shared_a", "shared_b", "unique_hw"]
val errors = proof_ref.ProofRefResolver.check_collisions(generated, handwritten)
expect(errors.len()).to_equal(2)
```

</details>

#### finds collisions with source locations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val generated = [("thm_x", "codegen.spl:100")]
val handwritten = [("thm_x", "manual.lean:50")]
val errors = proof_ref.ProofRefResolver.check_collisions_with_sources(generated, handwritten)
expect(errors.len()).to_equal(1)
expect(errors[0].generated_source).to_equal("codegen.spl:100")
expect(errors[0].handwritten_source).to_equal("manual.lean:50")
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

- **Plan:** [doc/03_plan/lean_verification_contract.md](doc/03_plan/lean_verification_contract.md)


</details>
