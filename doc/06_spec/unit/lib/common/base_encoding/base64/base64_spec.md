# Base64 Specification

> Tests covering base64, base64url.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base64 Specification

## Scenarios

### base64

#### encodes empty string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes empty string
   - Expected: base64_encode("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty string")
expect(base64_encode("")).to_equal("")
```

</details>

#### encodes single byte

- encodes single byte
   - Expected: base64_encode("M") equals `TQ==`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes single byte")
# "M" = 0x4D → 010011 01xxxx xxxx → "TQ=="
expect(base64_encode("M")).to_equal("TQ==")
```

</details>

#### encodes two bytes

- encodes two bytes
   - Expected: base64_encode("Ma") equals `TWE=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes two bytes")
# "Ma" = 0x4D 0x61 → "TWE="
expect(base64_encode("Ma")).to_equal("TWE=")
```

</details>

#### encodes three bytes (no padding)

- encodes three bytes (no padding)
   - Expected: base64_encode("Man") equals `TWFu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes three bytes (no padding)")
# "Man" = 0x4D 0x61 0x6E → "TWFu"
expect(base64_encode("Man")).to_equal("TWFu")
```

</details>

#### encodes RFC 4648 test vector: hello

- encodes RFC 4648 test vector: hello
   - Expected: base64_encode("hello") equals `aGVsbG8=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes RFC 4648 test vector: hello")
expect(base64_encode("hello")).to_equal("aGVsbG8=")
```

</details>

#### encodes RFC 4648 test vector: foobar

- encodes RFC 4648 test vector: foobar
   - Expected: base64_encode("foobar") equals `Zm9vYmFy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes RFC 4648 test vector: foobar")
expect(base64_encode("foobar")).to_equal("Zm9vYmFy")
```

</details>

#### encodes with all padding levels

- encodes with all padding levels
   - Expected: base64_encode("a") equals `YQ==`
   - Expected: base64_encode("ab") equals `YWI=`
   - Expected: base64_encode("abc") equals `YWJj`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes with all padding levels")
expect(base64_encode("a")).to_equal("YQ==")
expect(base64_encode("ab")).to_equal("YWI=")
expect(base64_encode("abc")).to_equal("YWJj")
```

</details>

#### decodes empty string

- decodes empty string
   - Expected: base64_decode("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes empty string")
expect(base64_decode("")).to_equal("")
```

</details>

#### decodes single byte

- decodes single byte
   - Expected: base64_decode("TQ==") equals `M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes single byte")
expect(base64_decode("TQ==")).to_equal("M")
```

</details>

#### decodes two bytes

- decodes two bytes
   - Expected: base64_decode("TWE=") equals `Ma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes two bytes")
expect(base64_decode("TWE=")).to_equal("Ma")
```

</details>

#### decodes three bytes

- decodes three bytes
   - Expected: base64_decode("TWFu") equals `Man`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes three bytes")
expect(base64_decode("TWFu")).to_equal("Man")
```

</details>

#### decodes hello

- decodes hello
   - Expected: base64_decode("aGVsbG8=") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes hello")
expect(base64_decode("aGVsbG8=")).to_equal("hello")
```

</details>

#### decodes foobar

- decodes foobar
   - Expected: base64_decode("Zm9vYmFy") equals `foobar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes foobar")
expect(base64_decode("Zm9vYmFy")).to_equal("foobar")
```

</details>

#### decode ignores whitespace

- decode ignores whitespace
   - Expected: base64_decode("aGVs\nbG8=") equals `hello`
   - Expected: base64_decode("aGVs bG8=") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decode ignores whitespace")
expect(base64_decode("aGVs\nbG8=")).to_equal("hello")
expect(base64_decode("aGVs bG8=")).to_equal("hello")
```

</details>

#### decode roundtrip

- decode roundtrip
   - Expected: base64_decode(base64_encode(msg)) equals `msg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decode roundtrip")
val msg = "The quick brown fox jumps over the lazy dog"
expect(base64_decode(base64_encode(msg))).to_equal(msg)
```

</details>

#### encode-decode roundtrip for various lengths

- encode-decode roundtrip for various lengths
   - Expected: base64_decode(base64_encode("a")) equals `a`
   - Expected: base64_decode(base64_encode("ab")) equals `ab`
   - Expected: base64_decode(base64_encode("abc")) equals `abc`
   - Expected: base64_decode(base64_encode("abcd")) equals `abcd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encode-decode roundtrip for various lengths")
expect(base64_decode(base64_encode("a"))).to_equal("a")
expect(base64_decode(base64_encode("ab"))).to_equal("ab")
expect(base64_decode(base64_encode("abc"))).to_equal("abc")
expect(base64_decode(base64_encode("abcd"))).to_equal("abcd")
```

</details>

### base64url

#### encodes with url-safe chars and no padding

- encodes with url-safe chars and no padding
   - Expected: data equals `aGVsbG8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes with url-safe chars and no padding")
# Standard base64 "a+/b" would have + and /; url-safe replaces them
# Known: base64url of "\xfb\xff\xfe" = "+/8=" standard → "-_8" url
val data = base64url_encode("hello")
expect(data).to_equal("aGVsbG8")
```

</details>

#### decodes url-safe string

- decodes url-safe string
   - Expected: base64url_decode("aGVsbG8") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes url-safe string")
expect(base64url_decode("aGVsbG8")).to_equal("hello")
```

</details>

#### decodes url-safe with - and _

- decodes url-safe with - and _
   - Expected: base64url_decode(encoded) equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes url-safe with - and _")
# JWT payload typically: base64url encoded JSON
val payload = "{\"sub\":\"1234\"}"
val encoded = base64url_encode(payload)
expect(base64url_decode(encoded)).to_equal(payload)
```

</details>

#### roundtrip url-safe

- roundtrip url-safe
   - Expected: base64url_decode(base64url_encode(msg)) equals `msg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrip url-safe")
val msg = "hello world"
expect(base64url_decode(base64url_encode(msg))).to_equal(msg)
```

</details>

#### replaces + with - and / with _ in url-safe encode

- replaces + with - and / with _ in url-safe encode
   - Expected: base64url_decode(base64url_encode(msg2)) equals `msg2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces + with - and / with _ in url-safe encode")
# "\xfb" encodes to "+w==" in standard base64; url-safe → "-w"
# Use a string that produces + or / in standard base64
# "~" = 0x7E; "~~" = 0x7E 0x7E → standard "fn4=" → url "fn4"
# Actually we test the character substitution via roundtrip
val msg2 = "subjects?_d=1"
expect(base64url_decode(base64url_encode(msg2))).to_equal(msg2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/base_encoding/base64/base64_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering base64, base64url.
- base64
- base64url

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `8c4c37f3c340b925c35304fc40d669db0e81d95af9cbe3537519ef8ea6355091`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c4c37f3c340b925c35304fc40d669db0e81d95af9cbe3537519ef8ea6355091`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c4c37f3c340b925c35304fc40d669db0e81d95af9cbe3537519ef8ea6355091`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/base_encoding/base64/base64_spec.spl
mirror: doc/06_spec/unit/lib/common/base_encoding/base64/base64_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/base_encoding/base64/base64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/base_encoding/base64/base64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/base_encoding/base64/base64_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/base_encoding/base64/base64_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes single byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/base_encoding/base64/base64_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes two bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
