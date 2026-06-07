# Sve2 Crypto Specification

> <details>

<!-- sdn-diagram:id=sve2_crypto_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sve2_crypto_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sve2_crypto_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sve2_crypto_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sve2 Crypto Specification

## Scenarios

### SVE2 emit_sm4e_z golden Z0 Z0

#### SM4E Z0.S Z0.S Z0.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### SM4E Z0.S Z0.S Z0.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### SM4E Z0.S Z0.S Z0.S byte1 is 0xE0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0xE0: SM4E opcode sub-field
val result = emit_sm4e_z(0, 0)
expect(result[1]).to_equal(224)
```

</details>

#### SM4E Z0.S Z0.S Z0.S byte2 is 0x23

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x23: SVE2-SM4 encrypt group fixed field
val result = emit_sm4e_z(0, 0)
expect(result[2]).to_equal(35)
```

</details>

#### SM4E Z0.S Z0.S Z0.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]=0x45: SVE2 crypto group
val result = emit_sm4e_z(0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_sm4e_z Zn field Z0 Z1

#### SM4E Z0.S Z0.S Z1.S byte0 encodes Zn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=0, Zn=1 → byte0 = 1*32 = 32 = 0x20
val result = emit_sm4e_z(0, 1)
expect(result[0]).to_equal(32)
```

</details>

#### SM4E Z0.S Z0.S Z1.S byte1 is 0xE0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(0, 1)
expect(result[1]).to_equal(224)
```

</details>

#### SM4E Z0.S Z0.S Z1.S byte2 is 0x23

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(0, 1)
expect(result[2]).to_equal(35)
```

</details>

#### SM4E Z0.S Z0.S Z1.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(0, 1)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_sm4e_z register fields Z1 Z2

#### SM4E Z1.S Z1.S Z2.S byte0 encodes Zd and Zn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=1, Zn=2 → byte0 = 2*32 + 1 = 65 = 0x41
val result = emit_sm4e_z(1, 2)
expect(result[0]).to_equal(65)
```

</details>

#### SM4E Z1.S Z1.S Z2.S byte1 is 0xE0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(1, 2)
expect(result[1]).to_equal(224)
```

</details>

#### SM4E Z1.S Z1.S Z2.S byte2 is 0x23

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(1, 2)
expect(result[2]).to_equal(35)
```

</details>

### SVE2 emit_sm4e_z Z3 Z5

#### SM4E Z3.S Z3.S Z5.S byte0 is 0xA3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=3, Zn=5 → 5*32 + 3 = 163 = 0xA3
val result = emit_sm4e_z(3, 5)
expect(result[0]).to_equal(163)
```

</details>

#### SM4E Z3.S Z3.S Z5.S byte1 is 0xE0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(3, 5)
expect(result[1]).to_equal(224)
```

</details>

#### SM4E Z3.S Z3.S Z5.S byte2 is 0x23

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(3, 5)
expect(result[2]).to_equal(35)
```

</details>

#### SM4E Z3.S Z3.S Z5.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(3, 5)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_sm4e_z boundary Z31 Z31

#### SM4E Z31.S Z31.S Z31.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(31, 31)
expect(result.len()).to_equal(4)
```

</details>

#### SM4E Z31.S Z31.S Z31.S byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=31, Zn=31 → 31*32 + 31 = 1023; 1023 % 256 = 255 = 0xFF
val result = emit_sm4e_z(31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### SM4E Z31.S Z31.S Z31.S byte1 is 0xE3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xE0 + carry 3 from Zn=31 overflow (1023/256=3) = 0xE3 = 227
val result = emit_sm4e_z(31, 31)
expect(result[1]).to_equal(227)
```

</details>

#### SM4E Z31.S Z31.S Z31.S byte2 is 0x23

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(31, 31)
expect(result[2]).to_equal(35)
```

</details>

#### SM4E Z31.S Z31.S Z31.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4e_z(31, 31)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_sm4ekey_z golden Z0 Z0 Z0

#### SM4EKEY Z0.S Z0.S Z0.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### SM4EKEY Z0.S Z0.S Z0.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### SM4EKEY Z0.S Z0.S Z0.S byte1 is 0xF0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0xF0: SM4EKEY opcode sub-field
val result = emit_sm4ekey_z(0, 0, 0)
expect(result[1]).to_equal(240)
```

</details>

#### SM4EKEY Z0.S Z0.S Z0.S byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x20: SVE2-SM4 key schedule group fixed field with Zm=0
val result = emit_sm4ekey_z(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### SM4EKEY Z0.S Z0.S Z0.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(0, 0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_sm4ekey_z Zm field Z0 Z0 Z1

#### SM4EKEY Z0.S Z0.S Z1.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(0, 0, 1)
expect(result[0]).to_equal(0)
```

</details>

#### SM4EKEY Z0.S Z0.S Z1.S byte1 is 0xF0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(0, 0, 1)
expect(result[1]).to_equal(240)
```

</details>

#### SM4EKEY Z0.S Z0.S Z1.S byte2 encodes Zm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=1 in bits[20:16]: byte2 = 0x20 + 1 = 0x21 = 33
val result = emit_sm4ekey_z(0, 0, 1)
expect(result[2]).to_equal(33)
```

</details>

#### SM4EKEY Z0.S Z0.S Z1.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(0, 0, 1)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_sm4ekey_z register fields Z1 Z2 Z3

#### SM4EKEY Z1.S Z2.S Z3.S byte0 encodes Zn and Zd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=1, Zn=2 → byte0 = 2*32 + 1 = 65 = 0x41
val result = emit_sm4ekey_z(1, 2, 3)
expect(result[0]).to_equal(65)
```

</details>

#### SM4EKEY Z1.S Z2.S Z3.S byte1 is 0xF0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(1, 2, 3)
expect(result[1]).to_equal(240)
```

</details>

#### SM4EKEY Z1.S Z2.S Z3.S byte2 encodes Zm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=3 → byte2 = 0x20 + 3 = 0x23 = 35
val result = emit_sm4ekey_z(1, 2, 3)
expect(result[2]).to_equal(35)
```

</details>

#### SM4EKEY Z1.S Z2.S Z3.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(1, 2, 3)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_sm4ekey_z Z3 Z5 Z7

#### SM4EKEY Z3.S Z5.S Z7.S byte0 is 0xA3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=3, Zn=5 → 5*32 + 3 = 163 = 0xA3
val result = emit_sm4ekey_z(3, 5, 7)
expect(result[0]).to_equal(163)
```

</details>

#### SM4EKEY Z3.S Z5.S Z7.S byte1 is 0xF0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(3, 5, 7)
expect(result[1]).to_equal(240)
```

</details>

#### SM4EKEY Z3.S Z5.S Z7.S byte2 is 0x27

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=7 → byte2 = 0x20 + 7 = 0x27 = 39
val result = emit_sm4ekey_z(3, 5, 7)
expect(result[2]).to_equal(39)
```

</details>

#### SM4EKEY Z3.S Z5.S Z7.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(3, 5, 7)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_sm4ekey_z boundary Z31 Z31 Z31

#### SM4EKEY Z31.S Z31.S Z31.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(31, 31, 31)
expect(result.len()).to_equal(4)
```

</details>

#### SM4EKEY Z31.S Z31.S Z31.S byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=31, Zn=31 → 31*32 + 31 = 1023; 1023 % 256 = 255 = 0xFF
val result = emit_sm4ekey_z(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### SM4EKEY Z31.S Z31.S Z31.S byte1 is 0xF3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xF0 + carry 3 from Zn overflow = 0xF3 = 243
val result = emit_sm4ekey_z(31, 31, 31)
expect(result[1]).to_equal(243)
```

</details>

#### SM4EKEY Z31.S Z31.S Z31.S byte2 is 0x3F

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=31, base 0x20 → 0x20 + 31 = 0x3F = 63
val result = emit_sm4ekey_z(31, 31, 31)
expect(result[2]).to_equal(63)
```

</details>

#### SM4EKEY Z31.S Z31.S Z31.S byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sm4ekey_z(31, 31, 31)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_rax1_z golden Z0 Z0 Z0

#### RAX1 Z0.D Z0.D Z0.D emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### RAX1 Z0.D Z0.D Z0.D byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### RAX1 Z0.D Z0.D Z0.D byte1 is 0xF4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0xF4: RAX1 opcode sub-field (differs from SM4EKEY's 0xF0)
val result = emit_rax1_z(0, 0, 0)
expect(result[1]).to_equal(244)
```

</details>

#### RAX1 Z0.D Z0.D Z0.D byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x20: SVE2-SHA3 group fixed field with Zm=0
val result = emit_rax1_z(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### RAX1 Z0.D Z0.D Z0.D byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(0, 0, 0)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_rax1_z Zm field Z0 Z0 Z1

#### RAX1 Z0.D Z0.D Z1.D byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(0, 0, 1)
expect(result[0]).to_equal(0)
```

</details>

#### RAX1 Z0.D Z0.D Z1.D byte1 is 0xF4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(0, 0, 1)
expect(result[1]).to_equal(244)
```

</details>

#### RAX1 Z0.D Z0.D Z1.D byte2 encodes Zm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=1 in bits[20:16]: byte2 = 0x20 + 1 = 0x21 = 33
val result = emit_rax1_z(0, 0, 1)
expect(result[2]).to_equal(33)
```

</details>

#### RAX1 Z0.D Z0.D Z1.D byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(0, 0, 1)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_rax1_z register fields Z1 Z2 Z3

#### RAX1 Z1.D Z2.D Z3.D byte0 encodes Zn and Zd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=1, Zn=2 → byte0 = 2*32 + 1 = 65 = 0x41
val result = emit_rax1_z(1, 2, 3)
expect(result[0]).to_equal(65)
```

</details>

#### RAX1 Z1.D Z2.D Z3.D byte1 is 0xF4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(1, 2, 3)
expect(result[1]).to_equal(244)
```

</details>

#### RAX1 Z1.D Z2.D Z3.D byte2 encodes Zm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=3 → byte2 = 0x20 + 3 = 0x23 = 35
val result = emit_rax1_z(1, 2, 3)
expect(result[2]).to_equal(35)
```

</details>

#### RAX1 Z1.D Z2.D Z3.D byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(1, 2, 3)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_rax1_z Z3 Z5 Z7

#### RAX1 Z3.D Z5.D Z7.D byte0 is 0xA3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=3, Zn=5 → 5*32 + 3 = 163 = 0xA3
val result = emit_rax1_z(3, 5, 7)
expect(result[0]).to_equal(163)
```

</details>

#### RAX1 Z3.D Z5.D Z7.D byte1 is 0xF4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(3, 5, 7)
expect(result[1]).to_equal(244)
```

</details>

#### RAX1 Z3.D Z5.D Z7.D byte2 is 0x27

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=7 → byte2 = 0x20 + 7 = 0x27 = 39
val result = emit_rax1_z(3, 5, 7)
expect(result[2]).to_equal(39)
```

</details>

#### RAX1 Z3.D Z5.D Z7.D byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(3, 5, 7)
expect(result[3]).to_equal(69)
```

</details>

### SVE2 emit_rax1_z boundary Z31 Z31 Z31

#### RAX1 Z31.D Z31.D Z31.D emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(31, 31, 31)
expect(result.len()).to_equal(4)
```

</details>

#### RAX1 Z31.D Z31.D Z31.D byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=31, Zn=31 → 31*32 + 31 = 1023; 1023 % 256 = 255 = 0xFF
val result = emit_rax1_z(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### RAX1 Z31.D Z31.D Z31.D byte1 is 0xF7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xF4 + carry 3 from Zn overflow = 0xF7 = 247
val result = emit_rax1_z(31, 31, 31)
expect(result[1]).to_equal(247)
```

</details>

#### RAX1 Z31.D Z31.D Z31.D byte2 is 0x3F

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=31, base 0x20 → 0x20 + 31 = 0x3F = 63
val result = emit_rax1_z(31, 31, 31)
expect(result[2]).to_equal(63)
```

</details>

#### RAX1 Z31.D Z31.D Z31.D byte3 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_rax1_z(31, 31, 31)
expect(result[3]).to_equal(69)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/sve2_crypto_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SVE2 emit_sm4e_z golden Z0 Z0
- SVE2 emit_sm4e_z Zn field Z0 Z1
- SVE2 emit_sm4e_z register fields Z1 Z2
- SVE2 emit_sm4e_z Z3 Z5
- SVE2 emit_sm4e_z boundary Z31 Z31
- SVE2 emit_sm4ekey_z golden Z0 Z0 Z0
- SVE2 emit_sm4ekey_z Zm field Z0 Z0 Z1
- SVE2 emit_sm4ekey_z register fields Z1 Z2 Z3
- SVE2 emit_sm4ekey_z Z3 Z5 Z7
- SVE2 emit_sm4ekey_z boundary Z31 Z31 Z31
- SVE2 emit_rax1_z golden Z0 Z0 Z0
- SVE2 emit_rax1_z Zm field Z0 Z0 Z1
- SVE2 emit_rax1_z register fields Z1 Z2 Z3
- SVE2 emit_rax1_z Z3 Z5 Z7
- SVE2 emit_rax1_z boundary Z31 Z31 Z31

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 65 |
| Active scenarios | 65 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
