# Basic Specification

> <details>

<!-- sdn-diagram:id=basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

basic_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Specification

## Scenarios

### RFC 7617 Basic — encode

#### encodes Aladdin:open sesame to RFC 7617 §2 example value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 7617 §2: base64("Aladdin:open sesame") = "QWxhZGRpbjpvcGVuIHNlc2FtZQ=="
val header = http_basic_encode(_user_aladdin(), text_to_bytes("open sesame"))
expect(bytes_to_text(header)).to_equal("Basic QWxhZGRpbjpvcGVuIHNlc2FtZQ==")
```

</details>

#### encodes user:pass to known base64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = http_basic_encode(_user_user(), _pw_pass())
expect(bytes_to_text(header)).to_equal("Basic dXNlcjpwYXNz")
```

</details>

#### encodes empty password

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = http_basic_encode(text_to_bytes("alice"), text_to_bytes(""))
# base64("alice:") = "YWxpY2U6"
expect(bytes_to_text(header)).to_equal("Basic YWxpY2U6")
```

</details>

### RFC 7617 Basic — parse round-trip

#### parses user:pass header back to original bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = http_basic_parse(_header_user_pass())
expect(result).to_equal((_user_user(), _pw_pass()))
```

</details>

#### parse then encode round-trips to same header value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = http_basic_encode(_user_user(), _pw_pass())
val parsed = http_basic_parse(original)
val re_encoded = http_basic_encode(parsed.0, parsed.1)
expect(bytes_to_text(re_encoded)).to_equal(bytes_to_text(original))
```

</details>

#### parse extracts correct user bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = http_basic_parse(_header_user_pass())
expect(bytes_to_text(result.0)).to_equal("user")
```

</details>

#### parse extracts correct password bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = http_basic_parse(_header_user_pass())
expect(bytes_to_text(result.1)).to_equal("pass")
```

</details>

### RFC 7617 Basic — parse tamper-reject

#### rejects header without 'Basic ' prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = text_to_bytes("Bearer dXNlcjpwYXNz")
expect(http_basic_parse(bad)).to_be_nil()
```

</details>

#### rejects header with malformed base64 (odd length)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "Basic XYZ" — base64 payload "XYZ" is length 3, not multiple of 4
val bad = text_to_bytes("Basic XYZ")
expect(http_basic_parse(bad)).to_be_nil()
```

</details>

#### rejects header where base64 decodes to no colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# base64("nocolon") — no ':' in decoded bytes → must return nil
# base64("nocolon") = "bm9jb2xvbg=="
val bad = text_to_bytes("Basic bm9jb2xvbg==")
expect(http_basic_parse(bad)).to_be_nil()
```

</details>

#### rejects empty header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = text_to_bytes("")
expect(http_basic_parse(bad)).to_be_nil()
```

</details>

### RFC 7617 Basic — constant-time verify

#### accepts correct user and password

1.  user user
2.  user user


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(http_basic_ct_verify(
    _user_user(), _pw_pass(),
    _user_user(), _pw_pass()
)).to_equal(true)
```

</details>

#### rejects wrong password

1.  user user
2.  user user


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(not http_basic_ct_verify(
    _user_user(), text_to_bytes("wrong"),
    _user_user(), _pw_pass()
)).to_equal(true)
```

</details>

#### rejects wrong user

1. text to bytes
2.  user user


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(not http_basic_ct_verify(
    text_to_bytes("evil"), _pw_pass(),
    _user_user(), _pw_pass()
)).to_equal(true)
```

</details>

#### rejects both wrong

1. text to bytes
2.  user user


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
