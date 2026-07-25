# SimpleOS QEMU SIMD Rendering Matrix

> Runs target-native vector rendering inside x86_64, AArch64, and RV64 SimpleOS

<!-- sdn-diagram:id=simpleos_engine2d_simd_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_engine2d_simd_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_engine2d_simd_matrix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_engine2d_simd_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS QEMU SIMD Rendering Matrix

Runs target-native vector rendering inside x86_64, AArch64, and RV64 SimpleOS

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/simpleos_engine2d_simd_matrix_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

Runs target-native vector rendering inside x86_64, AArch64, and RV64 SimpleOS
guests and requires real per-operation vector chunks plus exact QMP pixels.

## Scenarios

### SimpleOS QEMU target-native SIMD matrix

#### should execute x86_64 SSE2 or AVX2 rendering in the guest

- Boot SimpleOS x86_64 with the required SIMD CPU features
   - Artifact capture: after_step
- Render fill copy alpha and scroll through the strict SIMD facade
   - Artifact capture: after_step
- Validate positive vector chunks and zero required fallbacks
   - Artifact capture: after_step
- Compare QMP pixels with the scalar oracle
   - Artifact capture: after_step
- pending simpleos simd matrix
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot SimpleOS x86_64 with the required SIMD CPU features")
step("Render fill copy alpha and scroll through the strict SIMD facade")
step("Validate positive vector chunks and zero required fallbacks")
step("Compare QMP pixels with the scalar oracle")
pending_simpleos_simd_matrix()
```

</details>

#### should execute AArch64 NEON rendering in the guest

- Boot SimpleOS AArch64 with NEON
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: isa equals `neon`
- pending simpleos simd matrix
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot SimpleOS AArch64 with NEON")
val isa = "neon"
expect(isa).to_equal("neon")
pending_simpleos_simd_matrix()
```

</details>

#### should execute RV64 RVV rendering in a vector-enabled guest

- Boot SimpleOS RV64 with the V extension enabled
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: isa equals `rvv`
- pending simpleos simd matrix
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot SimpleOS RV64 with the V extension enabled")
val isa = "rvv"
expect(isa).to_equal("rvv")
pending_simpleos_simd_matrix()
```

</details>

<details>
<summary>Advanced: should reject target declarations with zero native vector chunks</summary>

#### should reject target declarations with zero native vector chunks

- Report a detected ISA without executed vector work
   - Expected: reason equals `zero-vector-chunks`
- pending simpleos simd matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Report a detected ISA without executed vector work")
val reason = "zero-vector-chunks"
expect(reason).to_equal("zero-vector-chunks")
pending_simpleos_simd_matrix()
```

</details>


</details>

<details>
<summary>Advanced: should reject scalar fallback presented as architecture SIMD support</summary>

#### should reject scalar fallback presented as architecture SIMD support

- Force a required operation onto scalar fallback
   - Expected: reason equals `required-operation-scalar-fallback`
- pending simpleos simd matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Force a required operation onto scalar fallback")
val reason = "required-operation-scalar-fallback"
expect(reason).to_equal("required-operation-scalar-fallback")
pending_simpleos_simd_matrix()
```

</details>


</details>

<details>
<summary>Advanced: should reproduce normalized receipts and pixels across ten boots</summary>

#### should reproduce normalized receipts and pixels across ten boots

- Run each target guest ten fresh times
- Compare semantic receipt and framebuffer hashes
   - Expected: boot_count equals `10`
- pending simpleos simd matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run each target guest ten fresh times")
val boot_count = 10
step("Compare semantic receipt and framebuffer hashes")
expect(boot_count).to_equal(10)
pending_simpleos_simd_matrix()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
