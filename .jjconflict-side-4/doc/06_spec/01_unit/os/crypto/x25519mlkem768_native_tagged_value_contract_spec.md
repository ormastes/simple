# x25519mlkem768_native_tagged_value_contract_spec

> Regression contract for ML-KEM canonical-key validation on native arrays.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_native_tagged_value_contract_spec

Regression contract for ML-KEM canonical-key validation on native arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

Regression contract for ML-KEM canonical-key validation on native arrays.

## Scenarios

### X25519MLKEM768 native tagged-value validation boundary

#### uses typed packed-byte reads before modulo q

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/os/crypto/ml_kem.spl")
expect(source).to_contain(
    "val b0 = values[byte_offset] & 0xFF")
expect(source).to_contain(
    "val b2 = values[byte_offset + 2] & 0xFF")
expect(source.contains(
    "decoded.get(coeff).to_i64() % 3329")).to_be(false)
expect(source.contains("val decoded = byte_decode(encoded, 12)")).to_be(false)
```

</details>

#### accepts the largest canonical coefficient in both packed positions

- var ek =  zero encapsulation key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ek = _zero_encapsulation_key()
ek[0] = 0x00
ek[1] = 0x0D
ek[2] = 0xD0
expect(ml_kem_768_encapsulation_key_valid(ek)).to_be(true)
```

</details>

#### rejects q in the first packed coefficient

- var ek =  zero encapsulation key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ek = _zero_encapsulation_key()
ek[0] = 0x01
ek[1] = 0x0D
expect(ml_kem_768_encapsulation_key_valid(ek)).to_be(false)
```

</details>

#### rejects q in the second packed coefficient

- var ek =  zero encapsulation key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ek = _zero_encapsulation_key()
ek[1] = 0x10
ek[2] = 0xD0
expect(ml_kem_768_encapsulation_key_valid(ek)).to_be(false)
```

</details>

#### checks canonical coefficients in every packed polynomial

- var second poly =  zero encapsulation key
- var final pair =  zero encapsulation key


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var second_poly = _zero_encapsulation_key()
second_poly[384] = 0x01
second_poly[385] = 0x0D
expect(ml_kem_768_encapsulation_key_valid(second_poly)).to_be(false)

var final_pair = _zero_encapsulation_key()
final_pair[1150] = 0x10
final_pair[1151] = 0xD0
expect(ml_kem_768_encapsulation_key_valid(final_pair)).to_be(false)
```

</details>

#### rejects non-octet list elements without exempting rho

- var high packed =  zero encapsulation key
- var negative packed =  zero encapsulation key
- var high rho =  zero encapsulation key
- var maximal rho =  zero encapsulation key


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var high_packed = _zero_encapsulation_key()
high_packed[0] = 256
expect(ml_kem_768_encapsulation_key_valid(high_packed)).to_be(false)

var negative_packed = _zero_encapsulation_key()
negative_packed[0] = -1
expect(ml_kem_768_encapsulation_key_valid(negative_packed)).to_be(false)

var high_rho = _zero_encapsulation_key()
high_rho[1183] = 256
expect(ml_kem_768_encapsulation_key_valid(high_rho)).to_be(false)

var maximal_rho = _zero_encapsulation_key()
maximal_rho[1183] = 255
expect(ml_kem_768_encapsulation_key_valid(maximal_rho)).to_be(true)
```

</details>

#### rejects a key with the wrong encoded length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_kem_768_encapsulation_key_valid([])).to_be(false)
```

</details>

#### records why chained to_i64 is not native unboxing evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = file_read(
    "doc/08_tracking/bug/x25519mlkem768_pure_native_probe_closure_nil_2026-08-02.md")
expect(report).to_contain(
    "there is no `sar $3`")
expect(report).to_contain(
    "`rt_value_as_int` call")
expect(report).to_contain(
    "`list.get` compiler defect remains open")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
