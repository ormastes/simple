# Encoder Decoder Specification

> <details>

<!-- sdn-diagram:id=encoder_decoder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encoder_decoder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encoder_decoder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encoder_decoder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encoder Decoder Specification

## Scenarios

### RFC 7541 C.2.1 — Literal Header Field with Indexing

#### encoder produces expected bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(4096, false)
val headers = _c21_headers()
val result = hpack_encode(headers, state)
val encoded = result.0
val expected = _c21_bytes()
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### encoder inserts into dynamic table

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(4096, false)
val headers = _c21_headers()
val result = hpack_encode(headers, state)
val new_state = result.1
expect(_enc_table_len(new_state)).to_equal(1)
expect(_enc_entry_name(new_state, 0)).to_equal("custom-key")
expect(_enc_entry_value(new_state, 0)).to_equal("custom-header")
```

</details>

#### decoder recovers the header

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val bytes = _c21_bytes()
val result = hpack_decode(bytes, state)
expect(result.is_ok()).to_equal(true)
val pair = result.unwrap()
val headers = pair.0
expect(headers.len()).to_equal(1)
expect(headers[0].name).to_equal("custom-key")
expect(headers[0].value).to_equal("custom-header")
expect(headers[0].sensitive).to_equal(false)
```

</details>

#### decoder inserts into dynamic table

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val bytes = _c21_bytes()
val result = hpack_decode(bytes, state).unwrap()
val new_state = result.1
expect(_dec_table_len(new_state)).to_equal(1)
expect(_dec_entry_name(new_state, 0)).to_equal("custom-key")
expect(_dec_entry_value(new_state, 0)).to_equal("custom-header")
```

</details>

### RFC 7541 C.2.2 — Literal Header Field without Indexing

#### decoder recovers the header

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val bytes = _c22_bytes()
val result = hpack_decode(bytes, state)
expect(result.is_ok()).to_equal(true)
val headers = result.unwrap().0
expect(headers.len()).to_equal(1)
expect(headers[0].name).to_equal(":path")
expect(headers[0].value).to_equal("/sample/path")
```

</details>

#### decoder does NOT insert into dynamic table

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val bytes = _c22_bytes()
val result = hpack_decode(bytes, state).unwrap()
val new_state = result.1
expect(_dec_table_len(new_state)).to_equal(0)
```

</details>

### RFC 7541 C.2.3 — Literal Header Field Never Indexed

#### encoder produces expected bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(4096, false)
val headers = _c23_headers()
val result = hpack_encode(headers, state)
val encoded = result.0
val expected = _c23_bytes()
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### decoder sets sensitive=true on the decoded header

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val bytes = _c23_bytes()
val result = hpack_decode(bytes, state)
expect(result.is_ok()).to_equal(true)
val headers = result.unwrap().0
expect(headers.len()).to_equal(1)
expect(headers[0].name).to_equal("password")
expect(headers[0].value).to_equal("secret")
expect(headers[0].sensitive).to_equal(true)
```

</details>

#### decoder does NOT insert sensitive header into dynamic table

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val bytes = _c23_bytes()
val result = hpack_decode(bytes, state).unwrap()
val new_state = result.1
expect(_dec_table_len(new_state)).to_equal(0)
```

</details>

### RFC 7541 C.2.4 — Indexed Header Field

#### encoder produces single byte 0x82 for :method=GET

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(4096, false)
val headers = _c24_headers()
val result = hpack_encode(headers, state)
val encoded = result.0
expect(encoded.len()).to_equal(1)
expect(encoded[0]).to_equal(0x82u8)
```

</details>

#### decoder recovers :method=GET from 0x82

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val bytes = _c24_bytes()
val result = hpack_decode(bytes, state)
expect(result.is_ok()).to_equal(true)
val headers = result.unwrap().0
expect(headers.len()).to_equal(1)
expect(headers[0].name).to_equal(":method")
expect(headers[0].value).to_equal("GET")
```

</details>

### RFC 7541 C.3.1 — First request without Huffman

#### encoder bytes match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(4096, false)
val headers = _c31_headers()
val result = hpack_encode(headers, state)
val encoded = result.0
val expected = _c31_bytes()
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### encoder dynamic table has 1 entry: :authority=www.example.com

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(4096, false)
val headers = _c31_headers()
val result = hpack_encode(headers, state)
val new_state = result.1
expect(_enc_table_len(new_state)).to_equal(1)
expect(_enc_entry_name(new_state, 0)).to_equal(":authority")
expect(_enc_entry_value(new_state, 0)).to_equal("www.example.com")
```

</details>

#### decoder bytes match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val bytes = _c31_bytes()
val result = hpack_decode(bytes, state)
expect(result.is_ok()).to_equal(true)
val headers = result.unwrap().0
expect(headers.len()).to_equal(4)
expect(headers[0].name).to_equal(":method")
expect(headers[0].value).to_equal("GET")
expect(headers[3].name).to_equal(":authority")
expect(headers[3].value).to_equal("www.example.com")
```

</details>

### RFC 7541 C.3.2 — Second request without Huffman

#### encoder bytes match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(4096, false)
val h1 = _c31_headers()
val r1 = hpack_encode(h1, state0)
val state1 = r1.1
val h2 = _c32_headers()
val r2 = hpack_encode(h2, state1)
val encoded = r2.0
val expected = _c32_bytes()
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### encoder dynamic table has 2 entries after second request

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(4096, false)
val h1 = _c31_headers()
val r1 = hpack_encode(h1, state0)
val state1 = r1.1
val h2 = _c32_headers()
val r2 = hpack_encode(h2, state1)
val state2 = r2.1
expect(_enc_table_len(state2)).to_equal(2)
# newest entry at index 0: cache-control=no-cache
expect(_enc_entry_name(state2, 0)).to_equal("cache-control")
expect(_enc_entry_value(state2, 0)).to_equal("no-cache")
```

</details>

#### decoder recovers second request headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(4096)
val r1 = hpack_decode(_c31_bytes(), state0)
val state1 = r1.unwrap().1
val r2 = hpack_decode(_c32_bytes(), state1)
expect(r2.is_ok()).to_equal(true)
val headers = r2.unwrap().0
expect(headers.len()).to_equal(5)
expect(headers[4].name).to_equal("cache-control")
expect(headers[4].value).to_equal("no-cache")
```

</details>

### RFC 7541 C.3.3 — Third request without Huffman

#### encoder bytes match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(4096, false)
val r1 = hpack_encode(_c31_headers(), state0)
val r2 = hpack_encode(_c32_headers(), r1.1)
val r3 = hpack_encode(_c33_headers(), r2.1)
val encoded = r3.0
val expected = _c33_bytes()
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### encoder dynamic table has 3 entries after third request

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(4096, false)
val r1 = hpack_encode(_c31_headers(), state0)
val r2 = hpack_encode(_c32_headers(), r1.1)
val r3 = hpack_encode(_c33_headers(), r2.1)
val state3 = r3.1
expect(_enc_table_len(state3)).to_equal(3)
expect(_enc_entry_name(state3, 0)).to_equal("custom-key")
expect(_enc_entry_value(state3, 0)).to_equal("custom-value")
```

</details>

#### decoder recovers third request headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(4096)
val r1 = hpack_decode(_c31_bytes(), state0)
val r2 = hpack_decode(_c32_bytes(), r1.unwrap().1)
val r3 = hpack_decode(_c33_bytes(), r2.unwrap().1)
expect(r3.is_ok()).to_equal(true)
val headers = r3.unwrap().0
expect(headers.len()).to_equal(5)
expect(headers[4].name).to_equal("custom-key")
expect(headers[4].value).to_equal("custom-value")
```

</details>

### RFC 7541 C.4 — Request Examples with Huffman

#### C.4.1 decoder recovers first request from Huffman bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val result = hpack_decode(_c41_bytes(), state)
expect(result.is_ok()).to_equal(true)
val headers = result.unwrap().0
expect(headers.len()).to_equal(4)
expect(headers[0].name).to_equal(":method")
expect(headers[0].value).to_equal("GET")
expect(headers[3].name).to_equal(":authority")
expect(headers[3].value).to_equal("www.example.com")
```

</details>

#### C.4.1 encoder with huffman=true produces expected bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(4096, true)
val headers = _c31_headers()
val result = hpack_encode(headers, state)
val encoded = result.0
val expected = _c41_bytes()
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### C.4.2 decoder recovers second request from Huffman bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(4096)
val r1 = hpack_decode(_c41_bytes(), state0)
val r2 = hpack_decode(_c42_bytes(), r1.unwrap().1)
expect(r2.is_ok()).to_equal(true)
val headers = r2.unwrap().0
expect(headers.len()).to_equal(5)
expect(headers[4].name).to_equal("cache-control")
expect(headers[4].value).to_equal("no-cache")
```

</details>

#### C.4.2 encoder with huffman=true produces expected bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(4096, true)
val r1 = hpack_encode(_c31_headers(), state0)
val r2 = hpack_encode(_c32_headers(), r1.1)
val expected = _c42_bytes()
expect(_bytes_eq(r2.0, expected)).to_equal(true)
```

</details>

#### C.4.3 decoder recovers third request from Huffman bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(4096)
val r1 = hpack_decode(_c41_bytes(), state0)
val r2 = hpack_decode(_c42_bytes(), r1.unwrap().1)
val r3 = hpack_decode(_c43_bytes(), r2.unwrap().1)
expect(r3.is_ok()).to_equal(true)
val headers = r3.unwrap().0
expect(headers.len()).to_equal(5)
expect(headers[4].name).to_equal("custom-key")
expect(headers[4].value).to_equal("custom-value")
```

</details>

#### C.4.3 encoder with huffman=true produces expected bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(4096, true)
val r1 = hpack_encode(_c31_headers(), state0)
val r2 = hpack_encode(_c32_headers(), r1.1)
val r3 = hpack_encode(_c33_headers(), r2.1)
val expected = _c43_bytes()
expect(_bytes_eq(r3.0, expected)).to_equal(true)
```

</details>

#### C.4 Huffman output is shorter than C.3 raw output for first request

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c31_len = _c31_bytes().len()
val c41_len = _c41_bytes().len()
expect(c41_len < c31_len).to_equal(true)
```

</details>

### RFC 7541 C.5.1 — First response (max_size=256) without Huffman

#### encoder bytes match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(256, false)
val result = hpack_encode(_c51_headers(), state)
val expected = _c51_bytes()
expect(_bytes_eq(result.0, expected)).to_equal(true)
```

</details>

#### decoder recovers first response

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(256)
val result = hpack_decode(_c51_bytes(), state)
expect(result.is_ok()).to_equal(true)
val headers = result.unwrap().0
expect(headers.len()).to_equal(4)
expect(headers[0].name).to_equal(":status")
expect(headers[0].value).to_equal("302")
```

</details>

### RFC 7541 C.5.2 — Second response (eviction) without Huffman

#### encoder bytes match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(256, false)
val r1 = hpack_encode(_c51_headers(), state0)
val r2 = hpack_encode(_c52_headers(), r1.1)
val expected = _c52_bytes()
expect(_bytes_eq(r2.0, expected)).to_equal(true)
```

</details>

#### decoder recovers second response

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(256)
val r1 = hpack_decode(_c51_bytes(), state0)
val r2 = hpack_decode(_c52_bytes(), r1.unwrap().1)
expect(r2.is_ok()).to_equal(true)
val headers = r2.unwrap().0
expect(headers.len()).to_equal(4)
expect(headers[0].name).to_equal(":status")
expect(headers[0].value).to_equal("307")
```

</details>

### RFC 7541 C.5.3 — Third response (eviction + small table) without Huffman

#### encoder bytes match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(256, false)
val r1 = hpack_encode(_c51_headers(), state0)
val r2 = hpack_encode(_c52_headers(), r1.1)
val r3 = hpack_encode(_c53_headers(), r2.1)
val expected = _c53_bytes()
expect(_bytes_eq(r3.0, expected)).to_equal(true)
```

</details>

#### decoder recovers third response

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(256)
val r1 = hpack_decode(_c51_bytes(), state0)
val r2 = hpack_decode(_c52_bytes(), r1.unwrap().1)
val r3 = hpack_decode(_c53_bytes(), r2.unwrap().1)
expect(r3.is_ok()).to_equal(true)
val headers = r3.unwrap().0
expect(headers.len()).to_equal(6)
expect(headers[0].name).to_equal(":status")
expect(headers[0].value).to_equal("200")
```

</details>

#### dynamic table has only 3 entries (eviction due to max_size=256)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(256)
val r1 = hpack_decode(_c51_bytes(), state0)
val r2 = hpack_decode(_c52_bytes(), r1.unwrap().1)
val r3 = hpack_decode(_c53_bytes(), r2.unwrap().1)
val state3 = r3.unwrap().1
expect(_dec_table_len(state3)).to_equal(3)
```

</details>

### RFC 7541 C.6 — Response Examples with Huffman

#### C.6.1 decoder recovers first response from Huffman bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(256)
val result = hpack_decode(_c61_bytes(), state)
expect(result.is_ok()).to_equal(true)
val headers = result.unwrap().0
expect(headers.len()).to_equal(4)
expect(headers[0].name).to_equal(":status")
expect(headers[0].value).to_equal("302")
```

</details>

#### C.6.1 encoder with huffman=true produces expected bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(256, true)
val result = hpack_encode(_c51_headers(), state)
val expected = _c61_bytes()
expect(_bytes_eq(result.0, expected)).to_equal(true)
```

</details>

#### C.6.2 decoder recovers second response from Huffman bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(256)
val r1 = hpack_decode(_c61_bytes(), state0)
val r2 = hpack_decode(_c62_bytes(), r1.unwrap().1)
expect(r2.is_ok()).to_equal(true)
val headers = r2.unwrap().0
expect(headers.len()).to_equal(4)
expect(headers[0].value).to_equal("307")
```

</details>

#### C.6.2 encoder with huffman=true produces expected bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(256, true)
val r1 = hpack_encode(_c51_headers(), state0)
val r2 = hpack_encode(_c52_headers(), r1.1)
val expected = _c62_bytes()
expect(_bytes_eq(r2.0, expected)).to_equal(true)
```

</details>

#### C.6.3 decoder recovers third response from Huffman bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_decoder_new(256)
val r1 = hpack_decode(_c61_bytes(), state0)
val r2 = hpack_decode(_c62_bytes(), r1.unwrap().1)
val r3 = hpack_decode(_c63_bytes(), r2.unwrap().1)
expect(r3.is_ok()).to_equal(true)
val headers = r3.unwrap().0
expect(headers.len()).to_equal(6)
expect(headers[0].value).to_equal("200")
```

</details>

#### C.6.3 encoder with huffman=true produces expected bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state0 = hpack_encoder_new(256, true)
val r1 = hpack_encode(_c51_headers(), state0)
val r2 = hpack_encode(_c52_headers(), r1.1)
val r3 = hpack_encode(_c53_headers(), r2.1)
val expected = _c63_bytes()
expect(_bytes_eq(r3.0, expected)).to_equal(true)
```

</details>

### HPACK round-trip — 5 typical request headers

#### encode → decode produces equal headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = _make_5_headers()
val enc_state = hpack_encoder_new(4096, false)
val enc_result = hpack_encode(original, enc_state)
val encoded_bytes = enc_result.0
val dec_state = hpack_decoder_new(4096)
val dec_result = hpack_decode(encoded_bytes, dec_state)
expect(dec_result.is_ok()).to_equal(true)
val decoded = dec_result.unwrap().0
expect(_headers_eq(original, decoded)).to_equal(true)
```

</details>

### HPACK round-trip — sensitive header survives

#### sensitive flag is preserved through encode → decode

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = _make_sensitive_headers()
val enc_state = hpack_encoder_new(4096, false)
val enc_result = hpack_encode(original, enc_state)
val dec_state = hpack_decoder_new(4096)
val dec_result = hpack_decode(enc_result.0, dec_state)
expect(dec_result.is_ok()).to_equal(true)
val decoded = dec_result.unwrap().0
expect(decoded.len()).to_equal(2)
expect(decoded[1].sensitive).to_equal(true)
```

</details>

#### sensitive header is NOT in dynamic table after decode

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = _make_sensitive_headers()
val enc_state = hpack_encoder_new(4096, false)
val enc_result = hpack_encode(original, enc_state)
val dec_state = hpack_decoder_new(4096)
val dec_result = hpack_decode(enc_result.0, dec_state)
val new_dec_state = dec_result.unwrap().1
# :method=POST is indexed (static), auth=sensitive is never indexed
# only entries actually inserted should appear
var found_auth = false
var i: i64 = 0
while i < _dec_table_len(new_dec_state):
    if _dec_entry_name(new_dec_state, i) == "authorization":
        found_auth = true
    i = i + 1
expect(found_auth).to_equal(false)
```

</details>

### HPACK round-trip — huffman=false byte size matches raw

#### encoded length equals raw literal size for simple headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = _c21_headers()
val enc_state = hpack_encoder_new(4096, false)
val result = hpack_encode(headers, enc_state)
val encoded = result.0
# C.2.1 raw bytes = 26 bytes (from RFC)
expect(encoded.len()).to_equal(26)
```

</details>

### HPACK decoder — adversarial inputs

#### rejects Indexed Header Field with index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
# 0x80 = 1xxxxxxx with index 0
val bytes: [u8] = [0x80u8]
val result = hpack_decode(bytes, state)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects out-of-range static index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
# 0x80 | 62 = 0xbe; but dynamic table is empty so index 62 is out of range
val bytes: [u8] = [0xbeu8]
val result = hpack_decode(bytes, state)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects truncated input mid-string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
# 0x40 = literal incremental, 0x05 = 5-byte name, but only 2 bytes follow
val bytes: [u8] = [0x40u8, 0x05u8, 0x61u8, 0x62u8]
val result = hpack_decode(bytes, state)
expect(result.is_err()).to_equal(true)
```

</details>

#### honours Dynamic Table Size Update

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
# First encode C.3.1 to put :authority=www.example.com in the decoder table
val r1 = hpack_decode(_c31_bytes(), state)
val state1 = r1.unwrap().1
expect(_dec_table_len(state1)).to_equal(1)
# §6.3 Dynamic Table Size Update: 001xxxxx with new_size=0 → 0x20
val resize_bytes: [u8] = [0x20u8]
val r2 = hpack_decode(resize_bytes, state1)
expect(r2.is_ok()).to_equal(true)
val state2 = r2.unwrap().1
expect(_dec_table_len(state2)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hpack/encoder_decoder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RFC 7541 C.2.1 — Literal Header Field with Indexing
- RFC 7541 C.2.2 — Literal Header Field without Indexing
- RFC 7541 C.2.3 — Literal Header Field Never Indexed
- RFC 7541 C.2.4 — Indexed Header Field
- RFC 7541 C.3.1 — First request without Huffman
- RFC 7541 C.3.2 — Second request without Huffman
- RFC 7541 C.3.3 — Third request without Huffman
- RFC 7541 C.4 — Request Examples with Huffman
- RFC 7541 C.5.1 — First response (max_size=256) without Huffman
- RFC 7541 C.5.2 — Second response (eviction) without Huffman
- RFC 7541 C.5.3 — Third response (eviction + small table) without Huffman
- RFC 7541 C.6 — Response Examples with Huffman
- HPACK round-trip — 5 typical request headers
- HPACK round-trip — sensitive header survives
- HPACK round-trip — huffman=false byte size matches raw
- HPACK decoder — adversarial inputs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
