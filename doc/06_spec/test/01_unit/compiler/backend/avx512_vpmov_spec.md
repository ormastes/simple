# avx512_vpmov_spec

> AVX-512 VPMOVZX/SX — byte-level emit golden tests

<!-- sdn-diagram:id=avx512_vpmov_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx512_vpmov_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx512_vpmov_spec -> std
avx512_vpmov_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx512_vpmov_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_vpmov_spec

AVX-512 VPMOVZX/SX — byte-level emit golden tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_vpmov_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

AVX-512 VPMOVZX/SX — byte-level emit golden tests

Tests emit_avx512_vpmovzxbd, emit_avx512_vpmovzxwd,
      emit_avx512_vpmovsxbd, emit_avx512_vpmovsxwd
from src/compiler/70.backend/backend/native/x86_64_avx512.spl
against Intel SDM Vol 2C encoding.

Encoding: EVEX.512.66.0F38.WIG <opcode> /r
  EVEX bytes: 62 F2 7D 48  (P0=F2, P1=7D, P2=48)
  vvvv unused (not_vvvv=1111), L'L=10 (512-bit), no mask.
  BD src=XMM index 0-15; WD src=YMM index 0-15.
  Opcodes: VPMOVZXBD=31, VPMOVZXWD=33, VPMOVSXBD=21, VPMOVSXWD=23.

Register ID convention: zmm_to_index uses id-48, so zmm0=48, zmm1=49, etc.
  XMM/YMM src passed as raw index 0-15 (not offset by X86_XMM base).

Golden bytes verified via llvm-mc:
  llvm-mc -triple=x86_64 -mattr=+avx512f,+avx512bw --show-encoding

## Scenarios

### AVX-512 VPMOVZXBD byte-level emit

#### VPMOVZXBD zmm0, xmm0 — golden bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4831c0")
```

</details>

#### VPMOVZXBD zmm1, xmm1 — golden bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxbd(X86_ZMM1, XMM1_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4831c9")
```

</details>

#### VPMOVZXBD output length is 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPMOVZXBD EVEX escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
expect(bytes[0]).to_equal(0x62)
```

</details>

#### VPMOVZXBD opcode byte is 0x31

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
expect(bytes[4]).to_equal(0x31)
```

</details>

### AVX-512 VPMOVZXWD byte-level emit

#### VPMOVZXWD zmm0, ymm0 — golden bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4833c0")
```

</details>

#### VPMOVZXWD zmm1, ymm1 — golden bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxwd(X86_ZMM1, YMM1_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4833c9")
```

</details>

#### VPMOVZXWD output length is 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPMOVZXWD opcode byte is 0x33

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
expect(bytes[4]).to_equal(0x33)
```

</details>

### AVX-512 VPMOVSXBD byte-level emit

#### VPMOVSXBD zmm0, xmm0 — golden bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4821c0")
```

</details>

#### VPMOVSXBD zmm1, xmm1 — golden bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovsxbd(X86_ZMM1, XMM1_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4821c9")
```

</details>

#### VPMOVSXBD output length is 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPMOVSXBD opcode byte is 0x21

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
expect(bytes[4]).to_equal(0x21)
```

</details>

### AVX-512 VPMOVSXWD byte-level emit

#### VPMOVSXWD zmm0, ymm0 — golden bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4823c0")
```

</details>

#### VPMOVSXWD zmm1, ymm1 — golden bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovsxwd(X86_ZMM1, YMM1_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4823c9")
```

</details>

#### VPMOVSXWD output length is 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPMOVSXWD opcode byte is 0x23

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(bytes[4]).to_equal(0x23)
```

</details>

### AVX-512 VPMOV opcode differentiation

#### zero-extend vs sign-extend BD differ only in opcode byte (byte index 4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zx = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
val sx = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
expect(zx[0]).to_equal(sx[0])
expect(zx[1]).to_equal(sx[1])
expect(zx[2]).to_equal(sx[2])
expect(zx[3]).to_equal(sx[3])
expect(zx[4] == sx[4]).to_equal(false)
expect(zx[5]).to_equal(sx[5])
```

</details>

#### zero-extend vs sign-extend WD differ only in opcode byte (byte index 4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zx = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
val sx = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(zx[0]).to_equal(sx[0])
expect(zx[1]).to_equal(sx[1])
expect(zx[2]).to_equal(sx[2])
expect(zx[3]).to_equal(sx[3])
expect(zx[4] == sx[4]).to_equal(false)
expect(zx[5]).to_equal(sx[5])
```

</details>

#### BD vs WD zero-extend differ only in opcode byte (byte index 4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bd = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
val wd = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
expect(bd[0]).to_equal(wd[0])
expect(bd[1]).to_equal(wd[1])
expect(bd[2]).to_equal(wd[2])
expect(bd[3]).to_equal(wd[3])
expect(bd[4] == wd[4]).to_equal(false)
expect(bd[5]).to_equal(wd[5])
```

</details>

#### BD vs WD sign-extend differ only in opcode byte (byte index 4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bd = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
val wd = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(bd[0]).to_equal(wd[0])
expect(bd[1]).to_equal(wd[1])
expect(bd[2]).to_equal(wd[2])
expect(bd[3]).to_equal(wd[3])
expect(bd[4] == wd[4]).to_equal(false)
expect(bd[5]).to_equal(wd[5])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
