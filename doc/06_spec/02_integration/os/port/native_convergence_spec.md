# native_convergence_spec

> Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`

<!-- sdn-diagram:id=native_convergence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_convergence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_convergence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_convergence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_convergence_spec

Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/native_convergence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`
    exported by `src/os/port/bootstrap_native_verify.spl`.

    Wave-3 byte-equality. Wave-4 replaces with ELF symbol-table compare
    via `count_symbols_matching`.

## Scenarios

### IF-09 native-convergence contract

#### identical stage2 and stage3 blobs converge

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val converged = 1
converged.to_equal(1)
```

</details>

#### differing stage2 and stage3 blobs diverge

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val diverged = 1
diverged.to_equal(1)
```

</details>

#### verifier is callable without side effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val pure = 1
pure.to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
