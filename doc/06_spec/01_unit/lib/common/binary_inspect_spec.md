# Binary Inspect Specification

> Tests covering binary_inspect canonical helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Binary Inspect Specification

## Scenarios

### binary_inspect canonical helpers

#### hex_digit and byte_to_hex cover bounds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hex_digit and byte_to_hex cover bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hex_digit and byte_to_hex cover bounds")
assert_equal(hex_digit(0), "0")
assert_equal(hex_digit(15), "f")
assert_equal(hex_digit(16), "")
assert_equal(byte_to_hex(0), "00")
assert_equal(byte_to_hex(255), "ff")
assert_equal(byte_to_hex(171), "ab")
assert_equal(byte_to_hex(256), "")
```

</details>

#### bytes_to_hex round-trips with hex_to_bytes

- bytes_to_hex round-trips with hex_to_bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bytes_to_hex round-trips with hex_to_bytes")
val bytes = [0, 1, 15, 16, 127, 128, 255]
val hex = bytes_to_hex(bytes)
assert_equal(hex, "00010f107f80ff")
val back = hex_to_bytes(hex)
assert_equal(back.len(), bytes.len())
var i = 0
while i < bytes.len():
    assert_equal(back[i], bytes[i])
    i = i + 1
```

</details>

#### rejects out-of-range and malformed input

- rejects out-of-range and malformed input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects out-of-range and malformed input")
assert_equal(bytes_to_hex([300]), "")
assert_equal(hex_to_bytes("abc").len(), 0)
assert_equal(hex_to_bytes("zz").len(), 0)
```

</details>

#### hex_char_value handles both cases

- hex_char_value handles both cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hex_char_value handles both cases")
assert_equal(hex_char_value("a"), 10)
assert_equal(hex_char_value("F"), 15)
assert_equal(hex_char_value("9"), 9)
assert_equal(hex_char_value("g"), 0 - 1)
assert_true(is_hex_digit("e"))
assert_false(is_hex_digit("x"))
```

</details>

#### format_bytes matches the perf.spl contract

- format_bytes matches the perf.spl contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("format_bytes matches the perf.spl contract")
assert_equal(format_bytes(512), "512 B")
assert_equal(format_bytes(2048), "2 KB")
assert_equal(format_bytes(3145728), "3 MB")
assert_equal(format_bytes(5368709120), "5 GB")
```

</details>

#### percent_hex_encode_byte/decode_pair match the http/url.spl to_hex/from_hex contract

- percent_hex_encode_byte/decode_pair match the http/url.spl to_hex/from_hex contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("percent_hex_encode_byte/decode_pair match the http/url.spl to_hex/from_hex contract")
assert_equal(percent_hex_encode_byte(0), "00")
assert_equal(percent_hex_encode_byte(255), "FF")
assert_equal(percent_hex_encode_byte(171), "AB")
assert_equal(percent_hex_decode_pair("0", "0"), 0)
assert_equal(percent_hex_decode_pair("F", "F"), 255)
assert_equal(percent_hex_decode_pair("f", "f"), 255)
assert_equal(percent_hex_decode_pair("A", "B"), 171)
# invalid digit falls through to 15 (matches the triplicated
# hex_digit_to_int fallthrough, not a fail-closed -1)
assert_equal(percent_hex_decode_pair("z", "0"), 240)
assert_equal(percent_hex_decode_pair("0", "z"), 15)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/binary_inspect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering binary_inspect canonical helpers.
- binary_inspect canonical helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BINARY-INSPECT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7bf95aceb5bb47a2c2d6cecb3f02d93d83c479a959eacd0b5b3f0b3a999175b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bf95aceb5bb47a2c2d6cecb3f02d93d83c479a959eacd0b5b3f0b3a999175b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bf95aceb5bb47a2c2d6cecb3f02d93d83c479a959eacd0b5b3f0b3a999175b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/binary_inspect_spec.spl
mirror: doc/06_spec/01_unit/lib/common/binary_inspect_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/binary_inspect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/binary_inspect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/binary_inspect_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/binary_inspect_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hex_digit and byte_to_hex cover bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/binary_inspect_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bytes_to_hex round-trips with hex_to_bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/binary_inspect_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects out-of-range and malformed input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
