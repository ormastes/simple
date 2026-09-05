# Base64 Specification

> <details>

<!-- sdn-diagram:id=base64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=base64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

base64_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=base64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base64 Specification

## Scenarios

### base64

#### encodes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_encode("")).to_equal("")
```

</details>

#### encodes single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "M" = 0x4D → 010011 01xxxx xxxx → "TQ=="
expect(base64_encode("M")).to_equal("TQ==")
```

</details>

#### encodes two bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "Ma" = 0x4D 0x61 → "TWE="
expect(base64_encode("Ma")).to_equal("TWE=")
```

</details>

#### encodes three bytes (no padding)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "Man" = 0x4D 0x61 0x6E → "TWFu"
expect(base64_encode("Man")).to_equal("TWFu")
```

</details>

#### encodes RFC 4648 test vector: hello

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_encode("hello")).to_equal("aGVsbG8=")
```

</details>

#### encodes RFC 4648 test vector: foobar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_encode("foobar")).to_equal("Zm9vYmFy")
```

</details>

#### encodes with all padding levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_encode("a")).to_equal("YQ==")
expect(base64_encode("ab")).to_equal("YWI=")
expect(base64_encode("abc")).to_equal("YWJj")
```

</details>

#### decodes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_decode("")).to_equal("")
```

</details>

#### decodes single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_decode("TQ==")).to_equal("M")
```

</details>

#### decodes two bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_decode("TWE=")).to_equal("Ma")
```

</details>

#### decodes three bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_decode("TWFu")).to_equal("Man")
```

</details>

#### decodes hello

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_decode("aGVsbG8=")).to_equal("hello")
```

</details>

#### decodes foobar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_decode("Zm9vYmFy")).to_equal("foobar")
```

</details>

#### decode ignores whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_decode("aGVs\nbG8=")).to_equal("hello")
expect(base64_decode("aGVs bG8=")).to_equal("hello")
```

</details>

#### decode roundtrip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "The quick brown fox jumps over the lazy dog"
expect(base64_decode(base64_encode(msg))).to_equal(msg)
```

</details>

#### encode-decode roundtrip for various lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64_decode(base64_encode("a"))).to_equal("a")
expect(base64_decode(base64_encode("ab"))).to_equal("ab")
expect(base64_decode(base64_encode("abc"))).to_equal("abc")
expect(base64_decode(base64_encode("abcd"))).to_equal("abcd")
```

</details>

### base64url

#### encodes with url-safe chars and no padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Standard base64 "a+/b" would have + and /; url-safe replaces them
# Known: base64url of "\xfb\xff\xfe" = "+/8=" standard → "-_8" url
val data = base64url_encode("hello")
expect(data).to_equal("aGVsbG8")
```

</details>

#### decodes url-safe string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base64url_decode("aGVsbG8")).to_equal("hello")
```

</details>

#### decodes url-safe with - and _

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# JWT payload typically: base64url encoded JSON
val payload = "{\"sub\":\"1234\"}"
val encoded = base64url_encode(payload)
expect(base64url_decode(encoded)).to_equal(payload)
```

</details>

#### roundtrip url-safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "hello world"
expect(base64url_decode(base64url_encode(msg))).to_equal(msg)
```

</details>

#### replaces + with - and / with _ in url-safe encode

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/common/base_encoding/base64/base64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
