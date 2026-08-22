# brotli_lz77_round_trip_spec

> Verifies the brotli lz77 round trip behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# brotli_lz77_round_trip_spec

Verifies the brotli lz77 round trip behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the brotli lz77 round trip behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### brotli_encode (LZ77) — round-trip

#### round-trips 24-byte 'ABC' x8 via LZ77 backref at distance 3

- Verify: round-trips 24-byte 'ABC' x8 via LZ77 backref at distance 3
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips 24-byte 'ABC' x8 via LZ77 backref at distance 3")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _abc_rep_24()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips 60-byte 'ABC' x20 via LZ77 backref at distance 3

- Verify: round-trips 60-byte 'ABC' x20 via LZ77 backref at distance 3
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips 60-byte 'ABC' x20 via LZ77 backref at distance 3")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _abc_rep_60()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips 12-byte 'AB' x6 via LZ77 backref at distance 2

- Verify: round-trips 12-byte 'AB' x6 via LZ77 backref at distance 2
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips 12-byte 'AB' x6 via LZ77 backref at distance 2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _ab_rep_12()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the minimum 4-byte 'AB' x2 payload at copy_len=2

- Verify: round-trips the minimum 4-byte 'AB' x2 payload at copy_len=2
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the minimum 4-byte 'AB' x2 payload at copy_len=2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _ab_rep_4()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips 16-byte run-length 'X' x16 via overlapping copy d=1

- Verify: round-trips 16-byte run-length 'X' x16 via overlapping copy d=1
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips 16-byte run-length 'X' x16 via overlapping copy d=1")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _xxxx_16()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips mixed 'AAAB' x2 via 4-byte insert + 4-byte copy at d=4

- Verify: round-trips mixed 'AAAB' x2 via 4-byte insert + 4-byte copy at d=4
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips mixed 'AAAB' x2 via 4-byte insert + 4-byte copy at d=4")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _aaab_aaab_8()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips an 8-byte insert prefix via the extended single-backref tier

- Verify: round-trips an 8-byte insert prefix via the extended single-backref tier
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips an 8-byte insert prefix via the extended single-backref tier")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _abcdabcc_twice_16()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a forced 16-byte insert prefix

- Verify: round-trips a forced 16-byte insert prefix
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a forced 16-byte insert prefix")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a15b_twice_32()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a forced 23-byte insert prefix at the former search bound

- Verify: round-trips a forced 23-byte insert prefix at the former search bound
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a forced 23-byte insert prefix at the former search bound")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a22b_twice_46()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a forced 26-byte insert prefix in the next decoder-supported bucket

- Verify: round-trips a forced 26-byte insert prefix in the next decoder-supported bucket
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a forced 26-byte insert prefix in the next decoder-supported bucket")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a25b_twice_52()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a forced 33-byte insert prefix at the new bounded limit

- Verify: round-trips a forced 33-byte insert prefix at the new bounded limit
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a forced 33-byte insert prefix at the new bounded limit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a32b_twice_66()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a 34-byte-period repeat now covered by the widened prefix-search window

- Verify: round-trips a 34-byte-period repeat now covered by the widened prefix-search window
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a 34-byte-period repeat now covered by the widened prefix-search window")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a33b_twice_68()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the 102-byte single-command copy-length boundary

- Verify: round-trips the 102-byte single-command copy-length boundary
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the 102-byte single-command copy-length boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a32b_periodic_102()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a 103-byte repeat just beyond the single-command copy budget

- Verify: round-trips a 103-byte repeat just beyond the single-command copy budget
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a 103-byte repeat just beyond the single-command copy budget")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a32b_periodic_103()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the 231-byte first copy-code-16 case

- Verify: round-trips the 231-byte first copy-code-16 case
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the 231-byte first copy-code-16 case")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_231()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a 232-byte repeat in the next decoder-supported copy bucket

- Verify: round-trips a 232-byte repeat in the next decoder-supported copy bucket
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a 232-byte repeat in the next decoder-supported copy bucket")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_232()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the 263-byte top of the copy-code-17 range

- Verify: round-trips the 263-byte top of the copy-code-17 range
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the 263-byte top of the copy-code-17 range")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_263()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the 264-byte first copy-code-18 case

- Verify: round-trips the 264-byte first copy-code-18 case
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the 264-byte first copy-code-18 case")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_264()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the 295-byte widened copy-length boundary

- Verify: round-trips the 295-byte widened copy-length boundary
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the 295-byte widened copy-length boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_295()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the 296-byte first copy-code-19 case

- Verify: round-trips the 296-byte first copy-code-19 case
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the 296-byte first copy-code-19 case")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_296()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the 328-byte first copy-code-19 base case

- Verify: round-trips the 328-byte first copy-code-19 base case
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the 328-byte first copy-code-19 base case")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_328()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips the 391-byte widened copy-length boundary

- Verify: round-trips the 391-byte widened copy-length boundary
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips the 391-byte widened copy-length boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_391()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a 392-byte repeat just beyond the widened copy-length boundary

- Verify: round-trips a 392-byte repeat just beyond the widened copy-length boundary
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a 392-byte repeat just beyond the widened copy-length boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_392()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips a 264-byte 131-period repeat just beyond the widened prefix-search window

- Verify: round-trips a 264-byte 131-period repeat just beyond the widened prefix-search window
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips a 264-byte 131-period repeat just beyond the widened prefix-search window")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a130b_periodic_264_window_miss()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

#### round-trips English text via uncompressed fallback (>4 distinct)

- Verify: round-trips English text via uncompressed fallback (>4 distinct)
   - Expected: result.is_err() is false
   - Expected: _bytes_equal(out, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: round-trips English text via uncompressed fallback (>4 distinct)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _quick_fox_20()
val encoded = brotli_encode(payload)
val result = brotli_decode(encoded)
expect(result.is_err()).to_equal(false)
val out = result.unwrap()
expect(_bytes_equal(out, payload)).to_equal(true)
```

</details>

### brotli_encode (LZ77) — size advantage

#### LZ77 path beats literal-only on 60-byte 'ABC' x20

- Verify: LZ77 path beats literal-only on 60-byte 'ABC' x20
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: LZ77 path beats literal-only on 60-byte 'ABC' x20")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Literal-only would emit 60 * 1-bit + 2-bit codewords ~= 120 bits + header.
# LZ77 emits 3 literals + ICP + distance + extras ~= 3 bytes + ~60 bits header.
# Should be smaller.
val payload = _abc_rep_60()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 8-byte-prefix repeat beats the former 17-byte fallback encoding

- Verify: 8-byte-prefix repeat beats the former 17-byte fallback encoding
   - Expected: compressed.len() < 17 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 8-byte-prefix repeat beats the former 17-byte fallback encoding")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _abcdabcc_twice_16()
val compressed = brotli_encode(payload)
expect(compressed.len() < 17).to_equal(true)
```

</details>

#### 16-byte-prefix repeat compresses below the old literal-only fallback

- Verify: 16-byte-prefix repeat compresses below the old literal-only fallback
   - Expected: compressed.len() < 15 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 16-byte-prefix repeat compresses below the old literal-only fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a15b_twice_32()
val compressed = brotli_encode(payload)
expect(compressed.len() < 15).to_equal(true)
```

</details>

#### 23-byte-prefix repeat still chooses the single-backref path

- Verify: 23-byte-prefix repeat still chooses the single-backref path
   - Expected: compressed.len() < 17 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 23-byte-prefix repeat still chooses the single-backref path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a22b_twice_46()
val compressed = brotli_encode(payload)
expect(compressed.len() < 17).to_equal(true)
```

</details>

#### 33-byte-prefix repeat still chooses the single-backref path

- Verify: 33-byte-prefix repeat still chooses the single-backref path
   - Expected: compressed.len() < 20 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 33-byte-prefix repeat still chooses the single-backref path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a32b_twice_66()
val compressed = brotli_encode(payload)
expect(compressed.len() < 20).to_equal(true)
```

</details>

#### 34-byte-period repeat now chooses the widened single-backref path

- Verify: 34-byte-period repeat now chooses the widened single-backref path
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 34-byte-period repeat now chooses the widened single-backref path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a33b_twice_68()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 102-byte boundary case stays smaller than uncompressed fallback

- Verify: 102-byte boundary case stays smaller than uncompressed fallback
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 102-byte boundary case stays smaller than uncompressed fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a32b_periodic_102()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 103-byte over-budget repeat is larger than the 102-byte boundary case

- Verify: 103-byte over-budget repeat is larger than the 102-byte boundary case
   - Expected: over_limit.len() > at_limit.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 103-byte over-budget repeat is larger than the 102-byte boundary case")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val at_limit = brotli_encode(_a32b_periodic_102())
val over_limit = brotli_encode(_a32b_periodic_103())
expect(over_limit.len() > at_limit.len()).to_equal(true)
```

</details>

#### 231-byte first kind-10 case stays smaller than uncompressed fallback

- Verify: 231-byte first kind-10 case stays smaller than uncompressed fallback
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 231-byte first kind-10 case stays smaller than uncompressed fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_231()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 263-byte top-of-copy-code-17 case stays smaller than uncompressed fallback

- Verify: 263-byte top-of-copy-code-17 case stays smaller than uncompressed fallback
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 263-byte top-of-copy-code-17 case stays smaller than uncompressed fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_263()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 264-byte first copy-code-18 case stays smaller than uncompressed fallback

- Verify: 264-byte first copy-code-18 case stays smaller than uncompressed fallback
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 264-byte first copy-code-18 case stays smaller than uncompressed fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_264()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 295-byte widened boundary stays smaller than uncompressed fallback

- Verify: 295-byte widened boundary stays smaller than uncompressed fallback
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 295-byte widened boundary stays smaller than uncompressed fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_295()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 296-byte first copy-code-19 case stays smaller than uncompressed fallback

- Verify: 296-byte first copy-code-19 case stays smaller than uncompressed fallback
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 296-byte first copy-code-19 case stays smaller than uncompressed fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_296()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 391-byte widened boundary stays smaller than uncompressed fallback

- Verify: 391-byte widened boundary stays smaller than uncompressed fallback
   - Expected: compressed.len() < raw.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 391-byte widened boundary stays smaller than uncompressed fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _a129b_periodic_391()
val raw = brotli_encode_uncompressed(payload)
val compressed = brotli_encode(payload)
expect(compressed.len() < raw.len()).to_equal(true)
```

</details>

#### 392-byte over-budget repeat is no smaller than the 391-byte boundary case

- Verify: 392-byte over-budget repeat is no smaller than the 391-byte boundary case
   - Expected: over_limit.len() >= at_limit.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 392-byte over-budget repeat is no smaller than the 391-byte boundary case")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val at_limit = brotli_encode(_a129b_periodic_391())
val over_limit = brotli_encode(_a129b_periodic_392())
expect(over_limit.len() >= at_limit.len()).to_equal(true)
```

</details>

#### 264-byte 131-period repeat is no smaller than the 263-byte boundary case

- Verify: 264-byte 131-period repeat is no smaller than the 263-byte boundary case
   - Expected: past_window.len() >= in_window.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_LZ77_ROUND_TRI-001
step("Verify: 264-byte 131-period repeat is no smaller than the 263-byte boundary case")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val in_window = brotli_encode(_a129b_periodic_263())
val past_window = brotli_encode(_a130b_periodic_264_window_miss())
expect(past_window.len() >= in_window.len()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d70a003bb3943706b8319f3cdb77c4c31ddf22d25eb52e412434686eb4681f1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d70a003bb3943706b8319f3cdb77c4c31ddf22d25eb52e412434686eb4681f1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d70a003bb3943706b8319f3cdb77c4c31ddf22d25eb52e412434686eb4681f1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
