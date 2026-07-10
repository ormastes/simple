# x86 Engine2D SIMD Execution

> Requires the production facade to execute real SSE2 or AVX2 rendering chunks,

<!-- sdn-diagram:id=engine2d_x86_simd_execution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_x86_simd_execution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_x86_simd_execution_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_x86_simd_execution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86 Engine2D SIMD Execution

Requires the production facade to execute real SSE2 or AVX2 rendering chunks,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_x86_simd_execution_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

Requires the production facade to execute real SSE2 or AVX2 rendering chunks,
not wrapper calls or scalar aliases, and compares the result exactly with an
independently executed scalar oracle.

## Scenarios

### x86 Engine2D target-native SIMD

#### should render fill copy alpha and scroll with native vector chunks

- Prepare the cpu_simd_x86 backend and deterministic scene
   - Log capture: after_step
- Capture per-operation vector execution counters
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: operations.len() equals `4`
- Compare readback against the independent scalar oracle
   - Log capture: after_step
- pending x86 simd execution
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare the cpu_simd_x86 backend and deterministic scene")
val operations = ["fill", "copy", "alpha", "scroll"]
step("Capture per-operation vector execution counters")
expect(operations.len()).to_equal(4)
step("Compare readback against the independent scalar oracle")
pending_x86_simd_execution()
```

</details>

<details>
<summary>Advanced: should reject wrapper hits when actual vector chunks remain zero</summary>

#### should reject wrapper hits when actual vector chunks remain zero

- Provide positive wrapper calls and zero vector chunks
   - Expected: vector_chunks equals `0`
- pending x86 simd execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Provide positive wrapper calls and zero vector chunks")
val vector_chunks = 0
expect(vector_chunks).to_equal(0)
pending_x86_simd_execution()
```

</details>


</details>

<details>
<summary>Advanced: should reject scalar fallback for a required SIMD operation</summary>

#### should reject scalar fallback for a required SIMD operation

- Force alpha blend onto the scalar fallback
   - Expected: fallback_calls equals `1`
- pending x86 simd execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Force alpha blend onto the scalar fallback")
val fallback_calls = 1
expect(fallback_calls).to_equal(1)
pending_x86_simd_execution()
```

</details>


</details>

<details>
<summary>Advanced: should require the expected SIMD instruction family in the guest binary</summary>

#### should require the expected SIMD instruction family in the guest binary

- Inspect the built x86 rendering entry for SSE2 or AVX2 instructions
   - Expected: accepted_families.len() equals `2`
- pending x86 simd execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the built x86 rendering entry for SSE2 or AVX2 instructions")
val accepted_families = ["sse2", "avx2"]
expect(accepted_families.len()).to_equal(2)
pending_x86_simd_execution()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
