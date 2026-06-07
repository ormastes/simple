# avx512_abs_spec

> AVX-512 VPABSD/Q — byte-level emit golden tests

<!-- sdn-diagram:id=avx512_abs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx512_abs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx512_abs_spec -> std
avx512_abs_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx512_abs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_abs_spec

AVX-512 VPABSD/Q — byte-level emit golden tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_abs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

AVX-512 VPABSD/Q — byte-level emit golden tests

Tests emit_avx512_vpabsd and emit_avx512_vpabsq from
src/compiler/70.backend/backend/native/x86_64_avx512.spl
against Intel SDM Vol 2C §VPABSD/§VPABSQ encoding.
Register ID convention: zmm_to_index uses id-48, so zmm0=48, zmm1=49, etc.
Golden bytes verified via llvm-mc -triple=x86_64 -mattr=+avx512f --show-encoding.

## Scenarios

### AVX-512 VPABSD byte-level emit

#### VPABSD zmm0, zmm0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpabsd(X86_ZMM0, X86_ZMM0)
expect(_list_hex(bytes)).to_equal("62f27d481ec0")
```

</details>

#### VPABSD zmm1, zmm3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpabsd(X86_ZMM1, X86_ZMM3)
expect(_list_hex(bytes)).to_equal("62f27d481ecb")
```

</details>

#### VPABSD output length is 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpabsd(X86_ZMM0, X86_ZMM0)
expect(bytes.len()).to_equal(6)
```

</details>

### AVX-512 VPABSQ byte-level emit

#### VPABSQ zmm0, zmm0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpabsq(X86_ZMM0, X86_ZMM0)
expect(_list_hex(bytes)).to_equal("62f2fd481ec0")
```

</details>

#### VPABSQ zmm2, zmm0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpabsq(X86_ZMM2, X86_ZMM0)
expect(_list_hex(bytes)).to_equal("62f2fd481ed0")
```

</details>

#### VPABSQ output length is 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpabsq(X86_ZMM0, X86_ZMM0)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPABSQ W-bit differs from VPABSD (byte index 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d_bytes = emit_avx512_vpabsd(X86_ZMM0, X86_ZMM0)
val q_bytes = emit_avx512_vpabsq(X86_ZMM0, X86_ZMM0)
expect(d_bytes[2] == q_bytes[2]).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
