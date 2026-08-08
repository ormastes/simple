# Simpleos Render Evidence Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Render Evidence Specification

## Scenarios

### SimpleOS portable rendering evidence

#### should validate a correlated QEMU target record

- Prepare correlated guest serial and QMP evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `pass`
   - Expected: simpleos_render_target_status(evidence) equals `qemu-verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare correlated guest serial and QMP evidence")
val evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("pass")
expect(simpleos_render_target_status(evidence)).to_equal("qemu-verified")
```

</details>

#### should validate a complete physical-board record

- Prepare identified board boot capture and transcript evidence
   - Expected: simpleos_render_target_status(evidence) equals `board-verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare identified board boot capture and transcript evidence")
val evidence = target_evidence("physical-board", "kv260-1", EVIDENCE_HASH, EVIDENCE_HASH, "boot-1")
expect(simpleos_render_target_status(evidence)).to_equal("board-verified")
```

</details>

<details>
<summary>Advanced: should reject physical-board evidence without board identity</summary>

#### should reject physical-board evidence without board identity

- Remove board identity from a physical run
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-board-identity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove board identity from a physical run")
val evidence = target_evidence("physical-board", "", "", EVIDENCE_HASH, "boot-1")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-board-identity")
```

</details>


</details>

<details>
<summary>Advanced: should reject guest and external capture hash disagreement</summary>

#### should reject guest and external capture hash disagreement

- Pair the guest receipt with another framebuffer
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `guest-capture-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair the guest receipt with another framebuffer")
val evidence = target_evidence("qemu", "", "", OTHER_HASH, "boot-1")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("guest-capture-mismatch")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing boot correlation</summary>

#### should reject missing boot correlation

- Remove the boot identity from QEMU evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-correlation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the boot identity from QEMU evidence")
val evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-correlation")
```

</details>


</details>

<details>
<summary>Advanced: should reject capture identity disagreement</summary>

#### should reject capture identity disagreement

- Pair a serial receipt with a different captured frame
- var evidence = target evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `frame-correlation-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair a serial receipt with a different captured frame")
var evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
evidence.capture_frame_id = "frame-2"
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("frame-correlation-mismatch")
```

</details>


</details>

#### should reject non-hex evidence hashes

- Replace a capture digest with a same-length non-hex string
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-capture-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace a capture digest with a same-length non-hex string")
val evidence = target_evidence("qemu", "", "", "gggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg", "boot-1")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-capture-evidence")
```

</details>

### SimpleOS target-native SIMD evidence

#### should validate x86 AVX2 vector chunks for every operation

- Prepare x86 AVX2 runtime-owner counters and exact pixels
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", required_kernels(), EVIDENCE_HASH)).code equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare x86 AVX2 runtime-owner counters and exact pixels")
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", required_kernels(), EVIDENCE_HASH)).code).to_equal("pass")
```

</details>

#### should validate AArch64 NEON vector chunks

- Prepare AArch64 NEON runtime-owner counters
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "neon", required_kernels(), EVIDENCE_HASH)).code equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare AArch64 NEON runtime-owner counters")
expect(validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "neon", required_kernels(), EVIDENCE_HASH)).code).to_equal("pass")
```

</details>

#### should validate RV64 RVV vector chunks

- Prepare vector-enabled RV64 runtime-owner counters
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)).code equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare vector-enabled RV64 runtime-owner counters")
expect(validate_simpleos_simd_render_evidence(simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)).code).to_equal("pass")
```

</details>

<details>
<summary>Advanced: should reject wrapper dispatch without actual vector chunks</summary>

#### should reject wrapper dispatch without actual vector chunks

- Set fill dispatch positive while its vector chunks remain zero
   - Expected: result.code equals `zero-vector-chunks`
   - Expected: result.operation equals `fill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set fill dispatch positive while its vector chunks remain zero")
val kernels = [make_simd_kernel_evidence("fill", 0, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, ""), make_simd_kernel_evidence("scroll", 4, 0, "")]
val result = validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", kernels, EVIDENCE_HASH))
expect(result.code).to_equal("zero-vector-chunks")
expect(result.operation).to_equal("fill")
```

</details>


</details>

<details>
<summary>Advanced: should reject required scalar fallback</summary>

#### should reject required scalar fallback

- Force alpha onto scalar fallback
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "neon", kernels, EVIDENCE_HASH)).code equals `required-operation-scalar-fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Force alpha onto scalar fallback")
val kernels = [make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 1, "scalar"), make_simd_kernel_evidence("scroll", 4, 0, "")]
expect(validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "neon", kernels, EVIDENCE_HASH)).code).to_equal("required-operation-scalar-fallback")
```

</details>


</details>

<details>
<summary>Advanced: should reject exact-pixel disagreement</summary>

#### should reject exact-pixel disagreement

- Change the SIMD output hash while counters remain positive
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("rv64", "rvv", required_kernels(), OTHER_HASH)).code equals `simd-oracle-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the SIMD output hash while counters remain positive")
expect(validate_simpleos_simd_render_evidence(simd_evidence("rv64", "rvv", required_kernels(), OTHER_HASH)).code).to_equal("simd-oracle-mismatch")
```

</details>


</details>

<details>
<summary>Advanced: should reject duplicate SIMD operations</summary>

#### should reject duplicate SIMD operations

- Duplicate fill while omitting scroll
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", kernels, EVIDENCE_HASH)).code equals `duplicate-required-operation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Duplicate fill while omitting scroll")
val kernels = [make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, "")]
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", kernels, EVIDENCE_HASH)).code).to_equal("duplicate-required-operation")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/renderdoc/simpleos_render_evidence_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS portable rendering evidence
- SimpleOS target-native SIMD evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
