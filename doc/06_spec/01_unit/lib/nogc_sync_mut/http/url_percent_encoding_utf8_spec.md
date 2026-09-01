# Url Percent Encoding Utf8 Specification

> Tests covering HTTP URL percent-encoding operates on UTF-8 octets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Url Percent Encoding Utf8 Specification

## Scenarios

### HTTP URL percent-encoding operates on UTF-8 octets

#### leaves unreserved ASCII untouched (control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- leaves unreserved ASCII untouched (control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves unreserved ASCII untouched (control)")
assert_equal(url_encode("abcXYZ019-_.~"), "abcXYZ019-_.~")
```

</details>

#### percent-encodes reserved ASCII

- percent-encodes reserved ASCII


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("percent-encodes reserved ASCII")
assert_equal(url_encode("a b"), "a%20b")
assert_equal(url_encode("a/b?c=d"), "a%2Fb%3Fc%3Dd")
```

</details>

#### percent-encodes each UTF-8 octet of a non-ASCII character

- percent-encodes each UTF-8 octet of a non-ASCII character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("percent-encodes each UTF-8 octet of a non-ASCII character")
assert_equal(url_encode("é"), "%C3%A9")
assert_equal(url_encode("中"), "%E4%B8%AD")
```

</details>

#### decodes multi-octet percent escapes back to the character

- decodes multi-octet percent escapes back to the character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes multi-octet percent escapes back to the character")
assert_equal(url_decode("%C3%A9"), "é")
assert_equal(url_decode("%E4%B8%AD"), "中")
```

</details>

#### round-trips ASCII and non-ASCII alike

- round-trips ASCII and non-ASCII alike


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips ASCII and non-ASCII alike")
assert_equal(url_decode(url_encode("a b/c")), "a b/c")
assert_equal(url_decode(url_encode("café 中")), "café 中")
```

</details>

#### still decodes plain ASCII escapes (control)

- still decodes plain ASCII escapes (control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still decodes plain ASCII escapes (control)")
assert_equal(url_decode("a%20b%2Fc"), "a b/c")
assert_equal(url_decode("a+b"), "a b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/http/url_percent_encoding_utf8_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HTTP URL percent-encoding operates on UTF-8 octets.
- HTTP URL percent-encoding operates on UTF-8 octets

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eded75459047468aae68fed09312462d5fd7f5b27e5248bba7ecfae6bf805b80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eded75459047468aae68fed09312462d5fd7f5b27e5248bba7ecfae6bf805b80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eded75459047468aae68fed09312462d5fd7f5b27e5248bba7ecfae6bf805b80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/http/url_percent_encoding_utf8_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/http/url_percent_encoding_utf8_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/http/url_percent_encoding_utf8_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/http/url_percent_encoding_utf8_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/http/url_percent_encoding_utf8_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves unreserved ASCII untouched (control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/http/url_percent_encoding_utf8_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'percent-encodes reserved ASCII' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/http/url_percent_encoding_utf8_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'percent-encodes each UTF-8 octet of a non-ASCII character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
