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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression contract for ML-KEM canonical-key validation on native arrays.

## Scenarios

### X25519MLKEM768 native tagged-value validation boundary

#### uses typed packed-byte reads before modulo q

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses typed packed-byte reads before modulo q


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses typed packed-byte reads before modulo q")
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

- accepts the largest canonical coefficient in both packed positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts the largest canonical coefficient in both packed positions")
var ek = _zero_encapsulation_key()
ek[0] = 0x00
ek[1] = 0x0D
ek[2] = 0xD0
expect(ml_kem_768_encapsulation_key_valid(ek)).to_be(true)
```

</details>

#### rejects q in the first packed coefficient

- rejects q in the first packed coefficient


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects q in the first packed coefficient")
var ek = _zero_encapsulation_key()
ek[0] = 0x01
ek[1] = 0x0D
expect(ml_kem_768_encapsulation_key_valid(ek)).to_be(false)
```

</details>

#### rejects q in the second packed coefficient

- rejects q in the second packed coefficient


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects q in the second packed coefficient")
var ek = _zero_encapsulation_key()
ek[1] = 0x10
ek[2] = 0xD0
expect(ml_kem_768_encapsulation_key_valid(ek)).to_be(false)
```

</details>

#### checks canonical coefficients in every packed polynomial

- checks canonical coefficients in every packed polynomial


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("checks canonical coefficients in every packed polynomial")
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

- rejects non-octet list elements without exempting rho


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects non-octet list elements without exempting rho")
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

- rejects a key with the wrong encoded length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a key with the wrong encoded length")
expect(ml_kem_768_encapsulation_key_valid([])).to_be(false)
```

</details>

#### records why chained to_i64 is not native unboxing evidence

- records why chained to_i64 is not native unboxing evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("records why chained to_i64 is not native unboxing evidence")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26dd8158471e674d1a98472b9f772426dbd805ac271097522dcc5fae3d3169b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26dd8158471e674d1a98472b9f772426dbd805ac271097522dcc5fae3d3169b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26dd8158471e674d1a98472b9f772426dbd805ac271097522dcc5fae3d3169b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses typed packed-byte reads before modulo q' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the largest canonical coefficient in both packed positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects q in the first packed coefficient' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
