# Base32 Rfc4648 Kat Specification

> <details>

<!-- sdn-diagram:id=base32_rfc4648_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=base32_rfc4648_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

base32_rfc4648_kat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=base32_rfc4648_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base32 Rfc4648 Kat Specification

## Scenarios

### RFC 4648 §10 Base32 standard encode (padded)

#### empty input encodes to empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode(_empty())).to_equal("")
```

</details>

#### 'f' encodes to 'MY======'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode(_bytes_f())).to_equal("MY======")
```

</details>

#### 'fo' encodes to 'MZXQ===='

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode(_bytes_fo())).to_equal("MZXQ====")
```

</details>

#### 'foo' encodes to 'MZXW6==='

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode(_bytes_foo())).to_equal("MZXW6===")
```

</details>

#### 'foob' encodes to 'MZXW6YQ='

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode(_bytes_foob())).to_equal("MZXW6YQ=")
```

</details>

#### 'fooba' encodes to 'MZXW6YTB'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode(_bytes_fooba())).to_equal("MZXW6YTB")
```

</details>

#### 'foobar' encodes to 'MZXW6YTBOI======'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode(_bytes_foobar())).to_equal("MZXW6YTBOI======")
```

</details>

### RFC 4648 §10 Base32 standard decode

#### empty string decodes to empty bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_decode("").len()).to_equal(0)
```

</details>

#### 'MY======' decodes to 'f'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode("MY======"))).to_equal("f")
```

</details>

#### 'MZXQ====' decodes to 'fo'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode("MZXQ===="))).to_equal("fo")
```

</details>

#### 'MZXW6===' decodes to 'foo'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode("MZXW6==="))).to_equal("foo")
```

</details>

#### 'MZXW6YQ=' decodes to 'foob'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode("MZXW6YQ="))).to_equal("foob")
```

</details>

#### 'MZXW6YTB' decodes to 'fooba'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode("MZXW6YTB"))).to_equal("fooba")
```

</details>

#### 'MZXW6YTBOI======' decodes to 'foobar'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode("MZXW6YTBOI======"))).to_equal("foobar")
```

</details>

### RFC 4648 §10 Base32hex encode (padded)

#### empty input encodes to empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex(_empty())).to_equal("")
```

</details>

#### 'f' encodes to 'CO======'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex(_bytes_f())).to_equal("CO======")
```

</details>

#### 'fo' encodes to 'CPNG===='

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex(_bytes_fo())).to_equal("CPNG====")
```

</details>

#### 'foo' encodes to 'CPNMU==='

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex(_bytes_foo())).to_equal("CPNMU===")
```

</details>

#### 'foob' encodes to 'CPNMUOG='

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex(_bytes_foob())).to_equal("CPNMUOG=")
```

</details>

#### 'fooba' encodes to 'CPNMUOJ1'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex(_bytes_fooba())).to_equal("CPNMUOJ1")
```

</details>

#### 'foobar' encodes to 'CPNMUOJ1E8======'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex(_bytes_foobar())).to_equal("CPNMUOJ1E8======")
```

</details>

### RFC 4648 §10 Base32hex decode

#### empty string decodes to empty bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_decode_hex("").len()).to_equal(0)
```

</details>

#### 'CO======' decodes to 'f'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode_hex("CO======"))).to_equal("f")
```

</details>

#### 'CPNG====' decodes to 'fo'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode_hex("CPNG===="))).to_equal("fo")
```

</details>

#### 'CPNMU===' decodes to 'foo'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode_hex("CPNMU==="))).to_equal("foo")
```

</details>

#### 'CPNMUOG=' decodes to 'foob'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode_hex("CPNMUOG="))).to_equal("foob")
```

</details>

#### 'CPNMUOJ1' decodes to 'fooba'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode_hex("CPNMUOJ1"))).to_equal("fooba")
```

</details>

#### 'CPNMUOJ1E8======' decodes to 'foobar'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text(base32_decode_hex("CPNMUOJ1E8======"))).to_equal("foobar")
```

</details>

### Base32 standard round-trip

#### empty round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = base32_encode(_empty())
val decoded = base32_decode(encoded)
expect(decoded.len()).to_equal(0)
```

</details>

#### 'f' round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = base32_encode(_bytes_f())
val decoded = base32_decode(encoded)
expect(bytes_to_text(decoded)).to_equal("f")
```

</details>

#### 'foobar' round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = base32_encode(_bytes_foobar())
val decoded = base32_decode(encoded)
expect(bytes_to_text(decoded)).to_equal("foobar")
```

</details>

### Base32hex round-trip

#### empty round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = base32_encode_hex(_empty())
val decoded = base32_decode_hex(encoded)
expect(decoded.len()).to_equal(0)
```

</details>

#### 'foobar' round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = base32_encode_hex(_bytes_foobar())
val decoded = base32_decode_hex(encoded)
expect(bytes_to_text(decoded)).to_equal("foobar")
```

</details>

### Base32 no-padding encode

#### empty input encodes to empty string (no-pad)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_no_pad(_empty())).to_equal("")
```

</details>

#### 'f' no-pad encodes to 'MY'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_no_pad(_bytes_f())).to_equal("MY")
```

</details>

#### 'fooba' no-pad encodes to 'MZXW6YTB' (already full block)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_no_pad(_bytes_fooba())).to_equal("MZXW6YTB")
```

</details>

#### 'foobar' no-pad encodes to 'MZXW6YTBOI'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_no_pad(_bytes_foobar())).to_equal("MZXW6YTBOI")
```

</details>

### Base32hex no-padding encode

#### 'f' no-pad encodes to 'CO'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex_no_pad(_bytes_f())).to_equal("CO")
```

</details>

#### 'foobar' no-pad encodes to 'CPNMUOJ1E8'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base32_encode_hex_no_pad(_bytes_foobar())).to_equal("CPNMUOJ1E8")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/base32_rfc4648_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RFC 4648 §10 Base32 standard encode (padded)
- RFC 4648 §10 Base32 standard decode
- RFC 4648 §10 Base32hex encode (padded)
- RFC 4648 §10 Base32hex decode
- Base32 standard round-trip
- Base32hex round-trip
- Base32 no-padding encode
- Base32hex no-padding encode

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
