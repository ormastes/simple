# Ldap Specification

> <details>

<!-- sdn-diagram:id=ldap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ldap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ldap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ldap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ldap Specification

## Scenarios

### LDAP BindRequest encode (pyasn1 vector)

#### anonymous simple bind v3 mid1 exact bytes

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pw: [u8] = []
val req = LdapBindRequest.new(3, LdapDn.new(""), LDAP_AUTH_SIMPLE, pw)
val enc = ldap_encode_bind_request(1, req)
val expected = [0x30, 0x0c, 0x02, 0x01, 0x01, 0x60, 0x07, 0x02, 0x01, 0x03, 0x04, 0x00, 0x80, 0x00]
expect(enc.len()).to_equal(14)
assert_true(bytes_match(enc, expected))
```

</details>

#### named simple bind exact bytes mid2

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pw = ldap_text_bytes("secret")
val req = LdapBindRequest.new(3, LdapDn.new("cn=admin,dc=example,dc=com"), LDAP_AUTH_SIMPLE, pw)
val enc = ldap_encode_bind_request(2, req)
# 30 2c 02 01 02 60 27 02 01 03 04 1a <26 dn bytes> 80 06 <secret>
expect(enc[0]).to_equal(0x30)
expect(enc[1]).to_equal(0x2c)
expect(enc[5]).to_equal(0x60)
expect(enc[6]).to_equal(0x27)
expect(enc[enc.len() - 8]).to_equal(0x80)
expect(enc[enc.len() - 7]).to_equal(0x06)
```

</details>

### LDAP SearchRequest encode (pyasn1 vector)

#### present filter exact bytes mid2

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev: [u8] = []
val ec: [LdapFilter] = []
val filt = LdapFilter.new(LDAP_FILTER_PRESENT, "objectClass", ev, ec)
val req = LdapSearchRequest.new(LdapDn.new("dc=example,dc=com"), LDAP_SCOPE_WHOLE_SUBTREE, LDAP_DEREF_NEVER, 0, 0, false, filt, ["cn"])
val enc = ldap_encode_search_request(2, req)
val expected = [0x30, 0x3a, 0x02, 0x01, 0x02, 0x63, 0x35, 0x04, 0x11, 0x64, 0x63, 0x3d, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2c, 0x64, 0x63, 0x3d, 0x63, 0x6f, 0x6d, 0x0a, 0x01, 0x02, 0x0a, 0x01, 0x00, 0x02, 0x01, 0x00, 0x02, 0x01, 0x00, 0x01, 0x01, 0x00, 0x87, 0x0b, 0x6f, 0x62, 0x6a, 0x65, 0x63, 0x74, 0x43, 0x6c, 0x61, 0x73, 0x73, 0x30, 0x04, 0x04, 0x02, 0x63, 0x6e]
assert_true(bytes_match(enc, expected))
```

</details>

#### scope and deref encode as ENUMERATED 0x0a not INTEGER

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev: [u8] = []
val ec: [LdapFilter] = []
val filt = LdapFilter.new(LDAP_FILTER_PRESENT, "objectClass", ev, ec)
val req = LdapSearchRequest.new(LdapDn.new("dc=example,dc=com"), LDAP_SCOPE_WHOLE_SUBTREE, LDAP_DEREF_NEVER, 0, 0, false, filt, ["cn"])
val enc = ldap_encode_search_request(2, req)
expect(enc[26]).to_equal(0x0a)
expect(enc[27]).to_equal(0x01)
expect(enc[28]).to_equal(0x02)
```

</details>

### LDAP filter encode (pyasn1 vectors)

#### AND of two equalityMatch exact bytes

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ec: [LdapFilter] = []
val c0 = LdapFilter.new(LDAP_FILTER_EQUALITY, "objectClass", ldap_text_bytes("person"), ec)
val c1 = LdapFilter.new(LDAP_FILTER_EQUALITY, "cn", ldap_text_bytes("jdoe"), ec)
val ev: [u8] = []
val f = LdapFilter.new(LDAP_FILTER_AND, "", ev, [c0, c1])
val enc = ldap_encode_filter_bytes(f)
val expected = [0xa0, 0x23, 0xa3, 0x15, 0x04, 0x0b, 0x6f, 0x62, 0x6a, 0x65, 0x63, 0x74, 0x43, 0x6c, 0x61, 0x73, 0x73, 0x04, 0x06, 0x70, 0x65, 0x72, 0x73, 0x6f, 0x6e, 0xa3, 0x0a, 0x04, 0x02, 0x63, 0x6e, 0x04, 0x04, 0x6a, 0x64, 0x6f, 0x65]
assert_true(bytes_match(enc, expected))
```

</details>

#### NOT(present) exact bytes

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev: [u8] = []
val ec: [LdapFilter] = []
val inner = LdapFilter.new(LDAP_FILTER_PRESENT, "mail", ev, ec)
val f = LdapFilter.new(LDAP_FILTER_NOT, "", ev, [inner])
val enc = ldap_encode_filter_bytes(f)
val expected = [0xa2, 0x06, 0x87, 0x04, 0x6d, 0x61, 0x69, 0x6c]
assert_true(bytes_match(enc, expected))
```

</details>

#### equalityMatch leaf uses context tag 0xa3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ec: [LdapFilter] = []
val f = LdapFilter.new(LDAP_FILTER_EQUALITY, "cn", ldap_text_bytes("jdoe"), ec)
val enc = ldap_encode_filter_bytes(f)
expect(enc[0]).to_equal(0xa3)
```

</details>

#### present leaf uses context tag 0x87

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev: [u8] = []
val ec: [LdapFilter] = []
val f = LdapFilter.new(LDAP_FILTER_PRESENT, "cn", ev, ec)
val enc = ldap_encode_filter_bytes(f)
expect(enc[0]).to_equal(0x87)
```

</details>

### LDAP filter round-trip

#### equalityMatch decodes back

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ec: [LdapFilter] = []
val f = LdapFilter.new(LDAP_FILTER_EQUALITY, "cn", ldap_text_bytes("jdoe"), ec)
val enc = ldap_encode_filter_bytes(f)
val back = ldap_decode_filter(enc)
expect(back.kind).to_equal(LDAP_FILTER_EQUALITY)
expect(back.attribute).to_equal("cn")
expect(ldap_bytes_to_text(back.value)).to_equal("jdoe")
```

</details>

#### present decodes back

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev: [u8] = []
val ec: [LdapFilter] = []
val f = LdapFilter.new(LDAP_FILTER_PRESENT, "objectClass", ev, ec)
val enc = ldap_encode_filter_bytes(f)
val back = ldap_decode_filter(enc)
expect(back.kind).to_equal(LDAP_FILTER_PRESENT)
expect(back.attribute).to_equal("objectClass")
```

</details>

#### AND of two children decodes back

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ec: [LdapFilter] = []
val c0 = LdapFilter.new(LDAP_FILTER_EQUALITY, "objectClass", ldap_text_bytes("person"), ec)
val c1 = LdapFilter.new(LDAP_FILTER_EQUALITY, "cn", ldap_text_bytes("jdoe"), ec)
val ev: [u8] = []
val f = LdapFilter.new(LDAP_FILTER_AND, "", ev, [c0, c1])
val enc = ldap_encode_filter_bytes(f)
val back = ldap_decode_filter(enc)
expect(back.kind).to_equal(LDAP_FILTER_AND)
expect(back.children.len()).to_equal(2)
expect(back.children[0].attribute).to_equal("objectClass")
expect(back.children[1].attribute).to_equal("cn")
```

</details>

#### NOT decodes back

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev: [u8] = []
val ec: [LdapFilter] = []
val inner = LdapFilter.new(LDAP_FILTER_PRESENT, "mail", ev, ec)
val f = LdapFilter.new(LDAP_FILTER_NOT, "", ev, [inner])
val enc = ldap_encode_filter_bytes(f)
val back = ldap_decode_filter(enc)
expect(back.kind).to_equal(LDAP_FILTER_NOT)
expect(back.children.len()).to_equal(1)
expect(back.children[0].kind).to_equal(LDAP_FILTER_PRESENT)
expect(back.children[0].attribute).to_equal("mail")
```

</details>

### LDAP message + result parsing (pyasn1 vectors)

#### parses bind response success mid1

- assert true
   - Expected: msg.message_id equals `1`
   - Expected: msg.op_kind equals `LDAP_OP_BIND_RESPONSE`
   - Expected: res.code equals `LDAP_RESULT_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x30, 0x0c, 0x02, 0x01, 0x01, 0x61, 0x07, 0x0a, 0x01, 0x00, 0x04, 0x00, 0x04, 0x00]
val msg = ldap_parse_message(data)
assert_true(msg.ok)
expect(msg.message_id).to_equal(1)
expect(msg.op_kind).to_equal(LDAP_OP_BIND_RESPONSE)
val res = ldap_decode_result(msg.op_content)
expect(res.code).to_equal(LDAP_RESULT_SUCCESS)
```

</details>

#### parses bind response invalidCredentials(49) with diagnostic

- assert true
   - Expected: res.code equals `LDAP_RESULT_INVALID_CREDENTIALS`
   - Expected: res.diagnostic_message equals `invalid credentials`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x30, 0x1f, 0x02, 0x01, 0x01, 0x61, 0x1a, 0x0a, 0x01, 0x31, 0x04, 0x00, 0x04, 0x13, 0x69, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x20, 0x63, 0x72, 0x65, 0x64, 0x65, 0x6e, 0x74, 0x69, 0x61, 0x6c, 0x73]
val msg = ldap_parse_message(data)
assert_true(msg.ok)
val res = ldap_decode_result(msg.op_content)
expect(res.code).to_equal(LDAP_RESULT_INVALID_CREDENTIALS)
expect(res.diagnostic_message).to_equal("invalid credentials")
```

</details>

#### parses search result done success mid2

- assert true
   - Expected: msg.message_id equals `2`
   - Expected: msg.op_kind equals `LDAP_OP_SEARCH_RES_DONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x30, 0x0c, 0x02, 0x01, 0x02, 0x65, 0x07, 0x0a, 0x01, 0x00, 0x04, 0x00, 0x04, 0x00]
val msg = ldap_parse_message(data)
assert_true(msg.ok)
expect(msg.message_id).to_equal(2)
expect(msg.op_kind).to_equal(LDAP_OP_SEARCH_RES_DONE)
```

</details>

### LDAP message round-trip via own encoder

#### bind request envelope decodes message id + op kind

- assert true
   - Expected: msg.message_id equals `7`
   - Expected: msg.op_kind equals `LDAP_OP_BIND_REQUEST`
   - Expected: br.version equals `3`
   - Expected: br.name.value equals `cn=u,dc=x`
   - Expected: ldap_bytes_to_text(br.password) equals `pw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = LdapBindRequest.new(3, LdapDn.new("cn=u,dc=x"), LDAP_AUTH_SIMPLE, ldap_text_bytes("pw"))
val enc = ldap_encode_bind_request(7, req)
val msg = ldap_parse_message(enc)
assert_true(msg.ok)
expect(msg.message_id).to_equal(7)
expect(msg.op_kind).to_equal(LDAP_OP_BIND_REQUEST)
val br = ldap_decode_bind_request(msg.op_content)
expect(br.version).to_equal(3)
expect(br.name.value).to_equal("cn=u,dc=x")
expect(ldap_bytes_to_text(br.password)).to_equal("pw")
```

</details>

#### search request envelope round-trips fields

- assert true
   - Expected: msg.op_kind equals `LDAP_OP_SEARCH_REQUEST`
   - Expected: sr.base_dn.value equals `ou=people,dc=x`
   - Expected: sr.scope equals `LDAP_SCOPE_SINGLE_LEVEL`
   - Expected: sr.size_limit equals `50`
   - Expected: sr.time_limit equals `10`
   - Expected: sr.types_only is true
   - Expected: sr.filter.kind equals `LDAP_FILTER_EQUALITY`
   - Expected: sr.filter.attribute equals `uid`
   - Expected: sr.attributes.len() equals `2`
   - Expected: sr.attributes[1] equals `mail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ec: [LdapFilter] = []
val filt = LdapFilter.new(LDAP_FILTER_EQUALITY, "uid", ldap_text_bytes("alice"), ec)
val req = LdapSearchRequest.new(LdapDn.new("ou=people,dc=x"), LDAP_SCOPE_SINGLE_LEVEL, LDAP_DEREF_NEVER, 50, 10, true, filt, ["cn", "mail"])
val enc = ldap_encode_search_request(9, req)
val msg = ldap_parse_message(enc)
assert_true(msg.ok)
expect(msg.op_kind).to_equal(LDAP_OP_SEARCH_REQUEST)
val sr = ldap_decode_search_request(msg.op_content)
expect(sr.base_dn.value).to_equal("ou=people,dc=x")
expect(sr.scope).to_equal(LDAP_SCOPE_SINGLE_LEVEL)
expect(sr.size_limit).to_equal(50)
expect(sr.time_limit).to_equal(10)
expect(sr.types_only).to_equal(true)
expect(sr.filter.kind).to_equal(LDAP_FILTER_EQUALITY)
expect(sr.filter.attribute).to_equal("uid")
expect(sr.attributes.len()).to_equal(2)
expect(sr.attributes[1]).to_equal("mail")
```

</details>

#### search result entry round-trips dn + attributes

- assert true
   - Expected: msg.op_kind equals `LDAP_OP_SEARCH_RES_ENTRY`
   - Expected: back.dn.value equals `cn=jdoe,dc=example,dc=com`
   - Expected: back.attributes.len() equals `2`
   - Expected: back.attributes[0].attr_type equals `cn`
   - Expected: ldap_bytes_to_text(back.attributes[0].values[0]) equals `jdoe`
   - Expected: ldap_bytes_to_text(back.attributes[1].values[0]) equals `jdoe@example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a0 = LdapAttribute.new("cn", [ldap_text_bytes("jdoe")])
val a1 = LdapAttribute.new("mail", [ldap_text_bytes("jdoe@example.com")])
val entry = LdapEntry.new(LdapDn.new("cn=jdoe,dc=example,dc=com"), [a0, a1])
val enc = ldap_encode_search_entry_bytes(entry)
val msg_enc = ldap_encode_message(2, enc)
val msg = ldap_parse_message(msg_enc)
assert_true(msg.ok)
expect(msg.op_kind).to_equal(LDAP_OP_SEARCH_RES_ENTRY)
val back = ldap_decode_search_entry(msg.op_content)
expect(back.dn.value).to_equal("cn=jdoe,dc=example,dc=com")
expect(back.attributes.len()).to_equal(2)
expect(back.attributes[0].attr_type).to_equal("cn")
expect(ldap_bytes_to_text(back.attributes[0].values[0])).to_equal("jdoe")
expect(ldap_bytes_to_text(back.attributes[1].values[0])).to_equal("jdoe@example.com")
```

</details>

### LDAP UnbindRequest

#### encodes mid5 exact bytes

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = ldap_encode_unbind_request(5)
val expected = [0x30, 0x05, 0x02, 0x01, 0x05, 0x42, 0x00]
assert_true(bytes_match(enc, expected))
```

</details>

#### envelope reports unbind op kind

- assert true
   - Expected: msg.op_kind equals `LDAP_OP_UNBIND_REQUEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = ldap_encode_unbind_request(5)
val msg = ldap_parse_message(enc)
assert_true(msg.ok)
expect(msg.op_kind).to_equal(LDAP_OP_UNBIND_REQUEST)
```

</details>

### LDAP decode error handling

#### truncated envelope errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v1: [u8] = [0x30]
val msg = ldap_parse_message(v1)
expect(msg.ok).to_equal(false)
```

</details>

#### truncated content length errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v2: [u8] = [0x30, 0x10, 0x02, 0x01]
val msg = ldap_parse_message(v2)
expect(msg.ok).to_equal(false)
```

</details>

#### non-sequence envelope errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v3: [u8] = [0x02, 0x01, 0x01]
val msg = ldap_parse_message(v3)
expect(msg.ok).to_equal(false)
```

</details>

### LDAPS secure wrapper

#### default port is 636

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ldaps_default_port()).to_equal(636)
```

</details>

#### cleartext default port is 389

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ldap_default_port()).to_equal(389)
```

</details>

#### implicit-TLS session is secure

- assert true
   - Expected: s.ldap.server_port equals `636`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = LdapsSession.new(7, "dir.example.com")
assert_true(s.is_secure())
expect(s.ldap.server_port).to_equal(636)
```

</details>

#### starttls session is pending until upgrade

- assert false
   - Expected: s.ldap.server_port equals `389`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = LdapsSession.new_starttls(7, "dir.example.com")
assert_false(s.is_secure())
expect(s.ldap.server_port).to_equal(389)
```

</details>

#### starttls oid marker present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ldap_starttls_oid()).to_equal("1.3.6.1.4.1.1466.20037")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/ldap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LDAP BindRequest encode (pyasn1 vector)
- LDAP SearchRequest encode (pyasn1 vector)
- LDAP filter encode (pyasn1 vectors)
- LDAP filter round-trip
- LDAP message + result parsing (pyasn1 vectors)
- LDAP message round-trip via own encoder
- LDAP UnbindRequest
- LDAP decode error handling
- LDAPS secure wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
