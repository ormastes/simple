# Sve2 Wmul Specification

> <details>

<!-- sdn-diagram:id=sve2_wmul_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sve2_wmul_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sve2_wmul_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sve2_wmul_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sve2 Wmul Specification

## Scenarios

### SVE2 emit_smullb_z_s golden Z0 Z0 Z0

#### SMULLB Z0.S Z0.H Z0.H emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_s(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### SMULLB Z0.S Z0.H Z0.H byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_s(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### SMULLB Z0.S Z0.H Z0.H byte1 is 0x70

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0x70: widening multiply opcode sub-field
val result = emit_smullb_z_s(0, 0, 0)
expect(result[1]).to_equal(112)
```

</details>

#### SMULLB Z0.S Z0.H Z0.H byte2 is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x80: size=10 (S result) with Zm=0
val result = emit_smullb_z_s(0, 0, 0)
expect(result[2]).to_equal(128)
```

</details>

#### SMULLB Z0.S Z0.H Z0.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]=0x45: SVE2 integer multiply group
val result = emit_smullb_z_s(0, 0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_smullb_z_s register field Z0 Z1 Z2

#### SMULLB Z0.S Z1.H Z2.H byte0 encodes Zn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=0, Zn=1 in bits[9:5]=32 → byte0 = 0 + 32 = 32 = 0x20
val result = emit_smullb_z_s(0, 1, 2)
expect(result[0]).to_equal(32)
```

</details>

#### SMULLB Z0.S Z1.H Z2.H byte1 is 0x70

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_s(0, 1, 2)
expect(result[1]).to_equal(112)
```

</details>

#### SMULLB Z0.S Z1.H Z2.H byte2 encodes Zm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=2 in bits[20:16]=2 → byte2 = 0x80 + 2 = 0x82 = 130
val result = emit_smullb_z_s(0, 1, 2)
expect(result[2]).to_equal(130)
```

</details>

#### SMULLB Z0.S Z1.H Z2.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_s(0, 1, 2)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_smullb_z_s Z3 Z5 Z7

#### SMULLB Z3.S Z5.H Z7.H byte0 encodes Zd and Zn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=3, Zn=5 → byte0 = 3 + 5*32 = 3 + 160 = 163 = 0xA3
val result = emit_smullb_z_s(3, 5, 7)
expect(result[0]).to_equal(163)
```

</details>

#### SMULLB Z3.S Z5.H Z7.H byte2 encodes Zm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=7 → byte2 = 0x80 + 7 = 135 = 0x87
val result = emit_smullb_z_s(3, 5, 7)
expect(result[2]).to_equal(135)
```

</details>

### SVE2 emit_smullb_z_s boundary Z31 Z31 Z31

#### SMULLB Z31.S Z31.H Z31.H byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=31, Zn=31 → byte0 = (31 + 31*32) % 256 = 1023 % 256 = 255 = 0xFF
val result = emit_smullb_z_s(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### SMULLB Z31.S Z31.H Z31.H byte1 is 0x73

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: opcode 0x70 + Zn overflow (1023/256=3 carry + 0x70) = 0x73 = 115
val result = emit_smullb_z_s(31, 31, 31)
expect(result[1]).to_equal(115)
```

</details>

#### SMULLB Z31.S Z31.H Z31.H byte2 is 0x9F

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=31 in bits[20:16] → byte2 = 0x80 + 31 = 0x9F = 159
val result = emit_smullb_z_s(31, 31, 31)
expect(result[2]).to_equal(159)
```

</details>

#### SMULLB Z31.S Z31.H Z31.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_s(31, 31, 31)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_smullt_z_s golden Z0 Z0 Z0

#### SMULLT Z0.S Z0.H Z0.H emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### SMULLT Z0.S Z0.H Z0.H byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### SMULLT Z0.S Z0.H Z0.H byte1 is 0x74

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0x74: top-half variant (T bit set vs SMULLB's 0x70)
val result = emit_smullt_z_s(0, 0, 0)
expect(result[1]).to_equal(116)
```

</details>

#### SMULLT Z0.S Z0.H Z0.H byte2 is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(0, 0, 0)
expect(result[2]).to_equal(128)
```

</details>

#### SMULLT Z0.S Z0.H Z0.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(0, 0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_smullt_z_s Z3 Z5 Z7

#### SMULLT Z3.S Z5.H Z7.H byte0 is 0xA3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(3, 5, 7)
expect(result[0]).to_equal(163)
```

</details>

#### SMULLT Z3.S Z5.H Z7.H byte1 is 0x74

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(3, 5, 7)
expect(result[1]).to_equal(116)
```

</details>

#### SMULLT Z3.S Z5.H Z7.H byte2 is 0x87

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(3, 5, 7)
expect(result[2]).to_equal(135)
```

</details>

### SVE2 emit_smullt_z_s boundary Z31 Z31 Z31

#### SMULLT Z31.S Z31.H Z31.H byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### SMULLT Z31.S Z31.H Z31.H byte1 is 0x77

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x74 + carry 3 from Zn=31 overflow = 0x77 = 119
val result = emit_smullt_z_s(31, 31, 31)
expect(result[1]).to_equal(119)
```

</details>

#### SMULLT Z31.S Z31.H Z31.H byte2 is 0x9F

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(31, 31, 31)
expect(result[2]).to_equal(159)
```

</details>

#### SMULLT Z31.S Z31.H Z31.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_s(31, 31, 31)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_umullb_z_s golden Z0 Z0 Z0

#### UMULLB Z0.S Z0.H Z0.H emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### UMULLB Z0.S Z0.H Z0.H byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### UMULLB Z0.S Z0.H Z0.H byte1 is 0x78

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0x78: unsigned bottom-half variant
val result = emit_umullb_z_s(0, 0, 0)
expect(result[1]).to_equal(120)
```

</details>

#### UMULLB Z0.S Z0.H Z0.H byte2 is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(0, 0, 0)
expect(result[2]).to_equal(128)
```

</details>

#### UMULLB Z0.S Z0.H Z0.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(0, 0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_umullb_z_s Z0 Z1 Z2

#### UMULLB Z0.S Z1.H Z2.H byte0 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(0, 1, 2)
expect(result[0]).to_equal(32)
```

</details>

#### UMULLB Z0.S Z1.H Z2.H byte1 is 0x78

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(0, 1, 2)
expect(result[1]).to_equal(120)
```

</details>

#### UMULLB Z0.S Z1.H Z2.H byte2 is 0x82

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(0, 1, 2)
expect(result[2]).to_equal(130)
```

</details>

### SVE2 emit_umullb_z_s Z3 Z5 Z7

#### UMULLB Z3.S Z5.H Z7.H byte0 is 0xA3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(3, 5, 7)
expect(result[0]).to_equal(163)
```

</details>

#### UMULLB Z3.S Z5.H Z7.H byte1 is 0x78

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(3, 5, 7)
expect(result[1]).to_equal(120)
```

</details>

#### UMULLB Z3.S Z5.H Z7.H byte2 is 0x87

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(3, 5, 7)
expect(result[2]).to_equal(135)
```

</details>

### SVE2 emit_umullb_z_s boundary Z31 Z31 Z31

#### UMULLB Z31.S Z31.H Z31.H byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### UMULLB Z31.S Z31.H Z31.H byte1 is 0x7B

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x78 + carry 3 = 0x7B = 123
val result = emit_umullb_z_s(31, 31, 31)
expect(result[1]).to_equal(123)
```

</details>

#### UMULLB Z31.S Z31.H Z31.H byte2 is 0x9F

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(31, 31, 31)
expect(result[2]).to_equal(159)
```

</details>

#### UMULLB Z31.S Z31.H Z31.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullb_z_s(31, 31, 31)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_umullt_z_s golden Z0 Z0 Z0

#### UMULLT Z0.S Z0.H Z0.H emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### UMULLT Z0.S Z0.H Z0.H byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### UMULLT Z0.S Z0.H Z0.H byte1 is 0x7C

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0x7C: unsigned top-half variant
val result = emit_umullt_z_s(0, 0, 0)
expect(result[1]).to_equal(124)
```

</details>

#### UMULLT Z0.S Z0.H Z0.H byte2 is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(0, 0, 0)
expect(result[2]).to_equal(128)
```

</details>

#### UMULLT Z0.S Z0.H Z0.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(0, 0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_umullt_z_s Z3 Z5 Z7

#### UMULLT Z3.S Z5.H Z7.H byte0 is 0xA3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(3, 5, 7)
expect(result[0]).to_equal(163)
```

</details>

#### UMULLT Z3.S Z5.H Z7.H byte1 is 0x7C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(3, 5, 7)
expect(result[1]).to_equal(124)
```

</details>

#### UMULLT Z3.S Z5.H Z7.H byte2 is 0x87

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(3, 5, 7)
expect(result[2]).to_equal(135)
```

</details>

### SVE2 emit_umullt_z_s boundary Z31 Z31 Z31

#### UMULLT Z31.S Z31.H Z31.H byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### UMULLT Z31.S Z31.H Z31.H byte1 is 0x7F

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x7C + carry 3 = 0x7F = 127
val result = emit_umullt_z_s(31, 31, 31)
expect(result[1]).to_equal(127)
```

</details>

#### UMULLT Z31.S Z31.H Z31.H byte2 is 0x9F

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(31, 31, 31)
expect(result[2]).to_equal(159)
```

</details>

#### UMULLT Z31.S Z31.H Z31.H byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_umullt_z_s(31, 31, 31)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_smullb_z_d golden Z0 Z0 Z0

#### SMULLB Z0.D Z0.S Z0.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_d(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### SMULLB Z0.D Z0.S Z0.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_d(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### SMULLB Z0.D Z0.S Z0.S byte1 is 0x70

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0x70: same widening multiply sub-field as S form
val result = emit_smullb_z_d(0, 0, 0)
expect(result[1]).to_equal(112)
```

</details>

#### SMULLB Z0.D Z0.S Z0.S byte2 is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0xC0: size=11 (D result) with Zm=0 → 0xC0 vs 0x80 for S
val result = emit_smullb_z_d(0, 0, 0)
expect(result[2]).to_equal(192)
```

</details>

#### SMULLB Z0.D Z0.S Z0.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_d(0, 0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_smullb_z_d Z0 Z1 Z2

#### SMULLB Z0.D Z1.S Z2.S byte0 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=0, Zn=1 → byte0 = 1*32 = 32
val result = emit_smullb_z_d(0, 1, 2)
expect(result[0]).to_equal(32)
```

</details>

#### SMULLB Z0.D Z1.S Z2.S byte2 is 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=2, size=D base=0xC0 → byte2 = 0xC0 + 2 = 194 = 0xC2
val result = emit_smullb_z_d(0, 1, 2)
expect(result[2]).to_equal(194)
```

</details>

### SVE2 emit_smullb_z_d Z3 Z5 Z7

#### SMULLB Z3.D Z5.S Z7.S byte0 is 0xA3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_d(3, 5, 7)
expect(result[0]).to_equal(163)
```

</details>

#### SMULLB Z3.D Z5.S Z7.S byte2 is 0xC7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=7, base 0xC0 → 0xC7 = 199
val result = emit_smullb_z_d(3, 5, 7)
expect(result[2]).to_equal(199)
```

</details>

### SVE2 emit_smullb_z_d boundary Z31 Z31 Z31

#### SMULLB Z31.D Z31.S Z31.S byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_d(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### SMULLB Z31.D Z31.S Z31.S byte1 is 0x73

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_d(31, 31, 31)
expect(result[1]).to_equal(115)
```

</details>

#### SMULLB Z31.D Z31.S Z31.S byte2 is 0xDF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=31, base 0xC0 → 0xC0 + 31 = 0xDF = 223
val result = emit_smullb_z_d(31, 31, 31)
expect(result[2]).to_equal(223)
```

</details>

#### SMULLB Z31.D Z31.S Z31.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullb_z_d(31, 31, 31)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_smullt_z_d golden Z0 Z0 Z0

#### SMULLT Z0.D Z0.S Z0.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### SMULLT Z0.D Z0.S Z0.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### SMULLT Z0.D Z0.S Z0.S byte1 is 0x74

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0x74: top-half D-result variant
val result = emit_smullt_z_d(0, 0, 0)
expect(result[1]).to_equal(116)
```

</details>

#### SMULLT Z0.D Z0.S Z0.S byte2 is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(0, 0, 0)
expect(result[2]).to_equal(192)
```

</details>

#### SMULLT Z0.D Z0.S Z0.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(0, 0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_smullt_z_d Z0 Z1 Z2

#### SMULLT Z0.D Z1.S Z2.S byte0 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(0, 1, 2)
expect(result[0]).to_equal(32)
```

</details>

#### SMULLT Z0.D Z1.S Z2.S byte1 is 0x74

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(0, 1, 2)
expect(result[1]).to_equal(116)
```

</details>

#### SMULLT Z0.D Z1.S Z2.S byte2 is 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(0, 1, 2)
expect(result[2]).to_equal(194)
```

</details>

### SVE2 emit_smullt_z_d Z3 Z5 Z7

#### SMULLT Z3.D Z5.S Z7.S byte0 is 0xA3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(3, 5, 7)
expect(result[0]).to_equal(163)
```

</details>

#### SMULLT Z3.D Z5.S Z7.S byte1 is 0x74

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(3, 5, 7)
expect(result[1]).to_equal(116)
```

</details>

#### SMULLT Z3.D Z5.S Z7.S byte2 is 0xC7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(3, 5, 7)
expect(result[2]).to_equal(199)
```

</details>

### SVE2 emit_smullt_z_d boundary Z31 Z31 Z31

#### SMULLT Z31.D Z31.S Z31.S byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### SMULLT Z31.D Z31.S Z31.S byte1 is 0x77

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x74 + carry 3 from Zn=31 = 0x77 = 119
val result = emit_smullt_z_d(31, 31, 31)
expect(result[1]).to_equal(119)
```

</details>

#### SMULLT Z31.D Z31.S Z31.S byte2 is 0xDF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(31, 31, 31)
expect(result[2]).to_equal(223)
```

</details>

#### SMULLT Z31.D Z31.S Z31.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_smullt_z_d(31, 31, 31)
expect(result[3]).to_equal(69)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/sve2_wmul_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SVE2 emit_smullb_z_s golden Z0 Z0 Z0
- SVE2 emit_smullb_z_s register field Z0 Z1 Z2
- SVE2 emit_smullb_z_s Z3 Z5 Z7
- SVE2 emit_smullb_z_s boundary Z31 Z31 Z31
- SVE2 emit_smullt_z_s golden Z0 Z0 Z0
- SVE2 emit_smullt_z_s Z3 Z5 Z7
- SVE2 emit_smullt_z_s boundary Z31 Z31 Z31
- SVE2 emit_umullb_z_s golden Z0 Z0 Z0
- SVE2 emit_umullb_z_s Z0 Z1 Z2
- SVE2 emit_umullb_z_s Z3 Z5 Z7
- SVE2 emit_umullb_z_s boundary Z31 Z31 Z31
- SVE2 emit_umullt_z_s golden Z0 Z0 Z0
- SVE2 emit_umullt_z_s Z3 Z5 Z7
- SVE2 emit_umullt_z_s boundary Z31 Z31 Z31
- SVE2 emit_smullb_z_d golden Z0 Z0 Z0
- SVE2 emit_smullb_z_d Z0 Z1 Z2
- SVE2 emit_smullb_z_d Z3 Z5 Z7
- SVE2 emit_smullb_z_d boundary Z31 Z31 Z31
- SVE2 emit_smullt_z_d golden Z0 Z0 Z0
- SVE2 emit_smullt_z_d Z0 Z1 Z2
- SVE2 emit_smullt_z_d Z3 Z5 Z7
- SVE2 emit_smullt_z_d boundary Z31 Z31 Z31

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
