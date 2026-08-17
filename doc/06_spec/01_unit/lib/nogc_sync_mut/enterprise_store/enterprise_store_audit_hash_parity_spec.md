# Enterprise Store audit-hash parity — the duplicate SHA-256 must never drift

> The repo deliberately carries **two** SHA-256 implementations:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Store audit-hash parity — the duplicate SHA-256 must never drift

The repo deliberately carries **two** SHA-256 implementations:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_hash_parity_spec.spl` |
| Updated | 2026-08-17 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The repo deliberately carries **two** SHA-256 implementations:

1. `std.common.crypto.sha256.sha256_text` — the shared stdlib one.
2. `std.nogc_sync_mut.enterprise_store.audit_hash.audit_sha256_hex` — a
   self-contained duplicate added by lane W4-B, because importing the shared
   one drags `std.common.string_core` slice helpers (`s[a:b]` -> CollectionOps)
   and the sized literal `[0; n]` in `sha256_bytes` (CollectionLiteral) into the
   compile closure, and standalone-SMF cross-compilation rejects both. Without
   the duplicate, every enterprise vertical's `--target=x86_64-unknown-simpleos`
   probe fails to compile.

Two implementations of the same hash are a correctness hazard: the audit
chain's integrity depends on the digest, and a silent drift between the two
would mean SimpleOS and host builds compute *different* audit chains from the
same records while both look healthy. This spec is the fence.

It does **not** merely assert that the two agree with each other — mutual
agreement is satisfied by two identically-wrong implementations. Every vector
is pinned to an **externally computed reference digest** (FIPS 180-4 published
vectors, and `python3 hashlib` for the rest), so each implementation is checked
against ground truth independently, and against the other.

Vector set, chosen for where SHA-256 implementations classically diverge:

- the empty string (padding-only block),
- the FIPS 180-4 published vectors `"abc"` and the 56-byte two-block vector,
- **55 bytes** — the last length whose padding still fits in one block,
- **56 bytes** — the first length that forces a second block for the length
  field (the classic off-by-one),
- **63 / 64 / 65 bytes** — the block boundary from both sides plus exact fit,
- **119 / 120 bytes** — the same padding edge one block further out,
- **1000 bytes** — deep multi-block, exercising the message schedule across
  many iterations,
- **high-bit-set bytes** — non-ASCII UTF-8, where a sign-extending `u8 -> i64`
  conversion (`data[j] as i64` in `ah_padded_byte`) would corrupt the digest,
- a realistic audit-record JSON payload.

## Troubleshooting

- **A `to_equal(reference)` failure on one implementation only** — that
  implementation is wrong; the reference digests are ground truth. Fix the
  failing side, do not adjust the expected value.
- **Both fail the same vector identically** — suspect the shared `rt_text_to_bytes`
  extern or the test harness, not the hash cores.
- **Parity holds but a reference fails** — both implementations drifted the
  same way; treat as a live audit-chain integrity bug.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (Goal Set v2, W12-C).

## Scenarios

### audit-hash parity — FIPS 180-4 published vectors

#### matches the published digest for the empty string on both implementations

- Hash the empty string with the stdlib and the enterprise duplicate
- Check each against the published FIPS digest, then against each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hash the empty string with the stdlib and the enterprise duplicate")
val reference = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
val shared = sha256_text("")
val duplicate = audit_sha256_hex("")
step("Check each against the published FIPS digest, then against each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

#### matches the published digest for \

- Hash the FIPS 180-4 one-block vector
- Check each against the published FIPS digest, then against each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hash the FIPS 180-4 one-block vector")
val reference = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
val shared = sha256_text("abc")
val duplicate = audit_sha256_hex("abc")
step("Check each against the published FIPS digest, then against each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

#### matches the published digest for the 56-byte two-block FIPS vector

- Hash the FIPS 180-4 multi-block vector
- Check each against the published FIPS digest, then against each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hash the FIPS 180-4 multi-block vector")
val payload = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
val reference = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check each against the published FIPS digest, then against each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

### audit-hash parity — padding edge cases at the block boundary

#### agrees at 55 bytes, the last length whose padding fits one block

- Build a 55-byte payload and confirm its length
   - Expected: payload.len() equals `55`
- Hash it with both implementations
- Check both against the reference digest and each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a 55-byte payload and confirm its length")
val payload = repeat_char("a", 55)
expect(payload.len()).to_equal(55)
step("Hash it with both implementations")
val reference = "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check both against the reference digest and each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

#### agrees at 56 bytes, the first length that forces a second block

- Build a 56-byte payload and confirm its length
   - Expected: payload.len() equals `56`
- Hash it with both implementations
- Check both against the reference digest and each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a 56-byte payload and confirm its length")
val payload = repeat_char("a", 56)
expect(payload.len()).to_equal(56)
step("Hash it with both implementations")
val reference = "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check both against the reference digest and each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

#### agrees at 63 bytes, one short of an exact block

- Build a 63-byte payload
   - Expected: payload.len() equals `63`
- Hash it with both implementations
- Check both against the reference digest and each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a 63-byte payload")
val payload = repeat_char("a", 63)
expect(payload.len()).to_equal(63)
step("Hash it with both implementations")
val reference = "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check both against the reference digest and each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

<details>
<summary>Advanced: agrees at exactly 64 bytes, a whole block with no room for padding</summary>

#### agrees at exactly 64 bytes, a whole block with no room for padding

- Build a 64-byte payload
   - Expected: payload.len() equals `64`
- Hash it with both implementations
- Check both against the reference digest and each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a 64-byte payload")
val payload = repeat_char("a", 64)
expect(payload.len()).to_equal(64)
step("Hash it with both implementations")
val reference = "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check both against the reference digest and each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>


</details>

#### agrees at 65 bytes, just past the block boundary

- Build a 65-byte payload
   - Expected: payload.len() equals `65`
- Hash it with both implementations
- Check both against the reference digest and each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a 65-byte payload")
val payload = repeat_char("a", 65)
expect(payload.len()).to_equal(65)
step("Hash it with both implementations")
val reference = "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check both against the reference digest and each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

#### agrees at 119 and 120 bytes, the same padding edge one block further out

- Build the 119-byte payload and hash it
   - Expected: p119.len() equals `119`
   - Expected: sha256_text(p119) equals `ref119`
   - Expected: audit_sha256_hex(p119) equals `ref119`
- Build the 120-byte payload, which spills into a third block, and hash it
   - Expected: p120.len() equals `120`
   - Expected: sha256_text(p120) equals `ref120`
   - Expected: audit_sha256_hex(p120) equals `ref120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the 119-byte payload and hash it")
val p119 = repeat_char("a", 119)
expect(p119.len()).to_equal(119)
val ref119 = "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb"
expect(sha256_text(p119)).to_equal(ref119)
expect(audit_sha256_hex(p119)).to_equal(ref119)
step("Build the 120-byte payload, which spills into a third block, and hash it")
val p120 = repeat_char("a", 120)
expect(p120.len()).to_equal(120)
val ref120 = "2f3d335432c70b580af0e8e1b3674a7c020d683aa5f73aaaedfdc55af904c21c"
expect(sha256_text(p120)).to_equal(ref120)
expect(audit_sha256_hex(p120)).to_equal(ref120)
```

</details>

### audit-hash parity — deep multi-block and high-bit input

#### agrees on a 1000-byte payload spanning sixteen blocks

- Build a 1000-byte payload
   - Expected: payload.len() equals `1000`
- Hash it with both implementations
- Check both against the reference digest and each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a 1000-byte payload")
val payload = repeat_char("a", 1000)
expect(payload.len()).to_equal(1000)
step("Hash it with both implementations")
val reference = "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check both against the reference digest and each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

#### agrees on non-ASCII bytes with the high bit set

- Hash a UTF-8 payload whose bytes exceed 0x7f
- Check both against the reference digest, catching any sign-extension bug
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hash a UTF-8 payload whose bytes exceed 0x7f")
val payload = "héllo wörld ✓ ünïcødé"
val reference = "9b502626f1db27c225a0d19c78d8b79aa215da78799444f5677f17118eabe4f9"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check both against the reference digest, catching any sign-extension bug")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

#### agrees on a realistic audit-record payload

- Hash a JSON audit record of the shape the audit chain actually hashes
- Check both against the reference digest and each other
   - Expected: shared equals `reference`
   - Expected: duplicate equals `reference`
   - Expected: duplicate equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hash a JSON audit record of the shape the audit chain actually hashes")
val payload = "{\"actor\":\"admin\",\"op\":\"delete\",\"id\":42}"
val reference = "beab1980891e2b52299b2e46cc9ae1a34c1caf0df28c465f8f943b38e54189cd"
val shared = sha256_text(payload)
val duplicate = audit_sha256_hex(payload)
step("Check both against the reference digest and each other")
expect(shared).to_equal(reference)
expect(duplicate).to_equal(reference)
expect(duplicate).to_equal(shared)
```

</details>

### audit-hash parity — digest shape and sensitivity

#### produces a 64-character lowercase hex digest from both implementations

- Hash a sample payload with both implementations
- Verify both digests are 64 hex characters and identical
   - Expected: shared.len() equals `64`
   - Expected: duplicate.len() equals `64`
   - Expected: duplicate equals `shared`
   - Expected: duplicate equals `duplicate.to_lower()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hash a sample payload with both implementations")
val shared = sha256_text("enterprise")
val duplicate = audit_sha256_hex("enterprise")
step("Verify both digests are 64 hex characters and identical")
expect(shared.len()).to_equal(64)
expect(duplicate.len()).to_equal(64)
expect(duplicate).to_equal(shared)
expect(duplicate).to_equal(duplicate.to_lower())
```

</details>

#### changes both digests identically for a one-bit input difference

- Hash two payloads differing in a single character
- Verify the digests differ, and that both implementations agree on each
   - Expected: a_shared == b_shared is false
   - Expected: a_dup == b_dup is false
   - Expected: a_dup equals `a_shared`
   - Expected: b_dup equals `b_shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hash two payloads differing in a single character")
val a_shared = sha256_text("audit-record-a")
val b_shared = sha256_text("audit-record-b")
val a_dup = audit_sha256_hex("audit-record-a")
val b_dup = audit_sha256_hex("audit-record-b")
step("Verify the digests differ, and that both implementations agree on each")
expect(a_shared == b_shared).to_equal(false)
expect(a_dup == b_dup).to_equal(false)
expect(a_dup).to_equal(a_shared)
expect(b_dup).to_equal(b_shared)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
