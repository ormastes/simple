# Encrypted Extensions Specification

> Tests covering parse_encrypted_extensions happy paths, parse_encrypted_extensions rejections.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encrypted Extensions Specification

## Scenarios

### parse_encrypted_extensions happy paths

#### accepts an empty extensions list

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts an empty extensions list
   - Expected: value.server_name_acknowledged is false
   - Expected: value.selected_alpn equals ``
   - Expected: value.max_fragment_length equals `0u8`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts an empty extensions list")
val res = parse_encrypted_extensions(_ee_empty())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.server_name_acknowledged).to_equal(false)
    expect(value.selected_alpn).to_equal("")
    expect(value.max_fragment_length).to_equal(0u8)
else:
    expect(false).to_equal(true)
```

</details>

#### records server_name acknowledgement

- records server_name acknowledgement
   - Expected: value.server_name_acknowledged is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records server_name acknowledgement")
val res = parse_encrypted_extensions(_ee_server_name_ack())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.server_name_acknowledged).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### extracts the selected ALPN protocol

- extracts the selected ALPN protocol
   - Expected: value.selected_alpn equals `h2`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the selected ALPN protocol")
val res = parse_encrypted_extensions(_ee_alpn_h2())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.selected_alpn).to_equal("h2")
else:
    expect(false).to_equal(true)
```

</details>

#### ignores unknown extension types and continues parsing

- ignores unknown extension types and continues parsing
   - Expected: value.selected_alpn equals `h2`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores unknown extension types and continues parsing")
val res = parse_encrypted_extensions(_ee_unknown_then_alpn())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.selected_alpn).to_equal("h2")
else:
    expect(false).to_equal(true)
```

</details>

#### echoes max_fragment_length byte

- echoes max_fragment_length byte
   - Expected: value.max_fragment_length equals `0x04u8`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("echoes max_fragment_length byte")
val res = parse_encrypted_extensions(_ee_mfl())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.max_fragment_length).to_equal(0x04u8)
else:
    expect(false).to_equal(true)
```

</details>

### parse_encrypted_extensions rejections

#### rejects duplicate extension_type as illegal_parameter

- rejects duplicate extension_type as illegal_parameter
   - Expected: reason contains `illegal_parameter`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate extension_type as illegal_parameter")
val res = parse_encrypted_extensions(_ee_dup_sni())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects truncated body as decode_error

- rejects truncated body as decode_error
   - Expected: reason contains `decode_error`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated body as decode_error")
val res = parse_encrypted_extensions(_ee_truncated_outer())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("decode_error")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects non-empty server_name in EE

- rejects non-empty server_name in EE
   - Expected: reason contains `illegal_parameter`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-empty server_name in EE")
val res = parse_encrypted_extensions(_ee_server_name_nonempty())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects early_data extension (0-RTT not implemented)

- rejects early_data extension (0-RTT not implemented)
   - Expected: reason contains `unsupported_extension`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects early_data extension (0-RTT not implemented)")
val res = parse_encrypted_extensions(_ee_early_data())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("unsupported_extension")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects ALPN with multiple ProtocolNames

- rejects ALPN with multiple ProtocolNames
   - Expected: reason contains `illegal_parameter`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects ALPN with multiple ProtocolNames")
val res = parse_encrypted_extensions(_ee_alpn_two_names())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects malformed max_fragment_length

- rejects malformed max_fragment_length
   - Expected: reason contains `illegal_parameter`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed max_fragment_length")
val res = parse_encrypted_extensions(_ee_mfl_bad_len())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/encrypted_extensions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parse_encrypted_extensions happy paths, parse_encrypted_extensions rejections.
- parse_encrypted_extensions happy paths
- parse_encrypted_extensions rejections

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a00cf43ebe35a1dd8ff2247636fe5e55ec9ff104a3901f2dbcf1746a0b85f1bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a00cf43ebe35a1dd8ff2247636fe5e55ec9ff104a3901f2dbcf1746a0b85f1bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a00cf43ebe35a1dd8ff2247636fe5e55ec9ff104a3901f2dbcf1746a0b85f1bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/encrypted_extensions_spec.spl
mirror: doc/06_spec/unit/os/tls13/encrypted_extensions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/encrypted_extensions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/encrypted_extensions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/encrypted_extensions_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an empty extensions list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/encrypted_extensions_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records server_name acknowledgement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/encrypted_extensions_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the selected ALPN protocol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
