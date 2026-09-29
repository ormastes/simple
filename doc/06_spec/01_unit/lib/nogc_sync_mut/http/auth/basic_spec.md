# Basic Specification

> Tests covering RFC 7617 Basic — encode, RFC 7617 Basic — parse round-trip, RFC 7617 Basic — parse tamper-reject, RFC 7617 Basic — constant-time verify.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Specification

## Scenarios

### RFC 7617 Basic — encode

#### encodes Aladdin:open sesame to RFC 7617 §2 example value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes Aladdin:open sesame to RFC 7617 §2 example value
   - Expected: bytes_to_text(header) equals `Basic QWxhZGRpbjpvcGVuIHNlc2FtZQ==`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes Aladdin:open sesame to RFC 7617 §2 example value")
# RFC 7617 §2: base64("Aladdin:open sesame") = "QWxhZGRpbjpvcGVuIHNlc2FtZQ=="
val header = http_basic_encode(_user_aladdin(), text_to_bytes("open sesame"))
expect(bytes_to_text(header)).to_equal("Basic QWxhZGRpbjpvcGVuIHNlc2FtZQ==")
```

</details>

#### encodes user:pass to known base64

- encodes user:pass to known base64
   - Expected: bytes_to_text(header) equals `Basic dXNlcjpwYXNz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes user:pass to known base64")
val header = http_basic_encode(_user_user(), _pw_pass())
expect(bytes_to_text(header)).to_equal("Basic dXNlcjpwYXNz")
```

</details>

#### encodes empty password

- encodes empty password
   - Expected: bytes_to_text(header) equals `Basic YWxpY2U6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty password")
val header = http_basic_encode(text_to_bytes("alice"), text_to_bytes(""))
# base64("alice:") = "YWxpY2U6"
expect(bytes_to_text(header)).to_equal("Basic YWxpY2U6")
```

</details>

### RFC 7617 Basic — parse round-trip

#### parses user:pass header back to original bytes

- parses user:pass header back to original bytes
   - Expected: result equals `(_user_user(), _pw_pass())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses user:pass header back to original bytes")
val result = http_basic_parse(_header_user_pass())
expect(result).to_equal((_user_user(), _pw_pass()))
```

</details>

#### parse then encode round-trips to same header value

- parse then encode round-trips to same header value
   - Expected: bytes_to_text(re_encoded) equals `bytes_to_text(original)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse then encode round-trips to same header value")
val original = http_basic_encode(_user_user(), _pw_pass())
val parsed = http_basic_parse(original)!
val re_encoded = http_basic_encode(parsed.0, parsed.1)
expect(bytes_to_text(re_encoded)).to_equal(bytes_to_text(original))
```

</details>

#### parse extracts correct user bytes

- parse extracts correct user bytes
   - Expected: bytes_to_text(result.0) equals `user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse extracts correct user bytes")
val result = http_basic_parse(_header_user_pass())!
expect(bytes_to_text(result.0)).to_equal("user")
```

</details>

#### parse extracts correct password bytes

- parse extracts correct password bytes
   - Expected: bytes_to_text(result.1) equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse extracts correct password bytes")
val result = http_basic_parse(_header_user_pass())!
expect(bytes_to_text(result.1)).to_equal("pass")
```

</details>

### RFC 7617 Basic — parse tamper-reject

#### rejects header without 'Basic ' prefix

- rejects header without 'Basic ' prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects header without 'Basic ' prefix")
val bad = text_to_bytes("Bearer dXNlcjpwYXNz")
expect(http_basic_parse(bad)).to_be_nil()
```

</details>

#### rejects header with malformed base64 (odd length)

- rejects header with malformed base64 (odd length)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects header with malformed base64 (odd length)")
# "Basic XYZ" — base64 payload "XYZ" is length 3, not multiple of 4
val bad = text_to_bytes("Basic XYZ")
expect(http_basic_parse(bad)).to_be_nil()
```

</details>

#### rejects header where base64 decodes to no colon

- rejects header where base64 decodes to no colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects header where base64 decodes to no colon")
# base64("nocolon") — no ':' in decoded bytes → must return nil
# base64("nocolon") = "bm9jb2xvbg=="
val bad = text_to_bytes("Basic bm9jb2xvbg==")
expect(http_basic_parse(bad)).to_be_nil()
```

</details>

#### rejects empty header

- rejects empty header


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty header")
val bad = text_to_bytes("")
expect(http_basic_parse(bad)).to_be_nil()
```

</details>

### RFC 7617 Basic — constant-time verify

#### accepts correct user and password

- accepts correct user and password


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts correct user and password")
expect(http_basic_ct_verify(
    _user_user(), _pw_pass(),
    _user_user(), _pw_pass()
)).to_equal(true)
```

</details>

#### rejects wrong password

- rejects wrong password


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects wrong password")
expect(not http_basic_ct_verify(
    _user_user(), text_to_bytes("wrong"),
    _user_user(), _pw_pass()
)).to_equal(true)
```

</details>

#### rejects wrong user

- rejects wrong user


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects wrong user")
expect(not http_basic_ct_verify(
    text_to_bytes("evil"), _pw_pass(),
    _user_user(), _pw_pass()
)).to_equal(true)
```

</details>

#### rejects both wrong

- rejects both wrong


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects both wrong")
expect(not http_basic_ct_verify(
    text_to_bytes("evil"), text_to_bytes("wrong"),
    _user_user(), _pw_pass()
)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/http/auth/basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RFC 7617 Basic — encode, RFC 7617 Basic — parse round-trip, RFC 7617 Basic — parse tamper-reject, RFC 7617 Basic — constant-time verify.
- RFC 7617 Basic — encode
- RFC 7617 Basic — parse round-trip
- RFC 7617 Basic — parse tamper-reject
- RFC 7617 Basic — constant-time verify

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `a5c9d370148893e75c65e68ebc2a1387c161e0a8df83dbcb8bf20b238131bb18`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5c9d370148893e75c65e68ebc2a1387c161e0a8df83dbcb8bf20b238131bb18`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5c9d370148893e75c65e68ebc2a1387c161e0a8df83dbcb8bf20b238131bb18`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/http/auth/basic_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/http/auth/basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/http/auth/basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/http/auth/basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/http/auth/basic_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes Aladdin:open sesame to RFC 7617 §2 example value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/http/auth/basic_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes user:pass to known base64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/http/auth/basic_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes empty password' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
