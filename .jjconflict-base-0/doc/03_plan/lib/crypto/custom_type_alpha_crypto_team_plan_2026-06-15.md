# Plan — Custom-Type Alpha Crypto Team (TEMPLATE + shared foundation)

Created 2026-06-15. Companion research:
[`doc/01_research/lib/crypto/security_crypto_protocol_catalog_2026-06-15.md`](../../../01_research/lib/crypto/security_crypto_protocol_catalog_2026-06-15.md).

This is **one of three sibling multi-agent plans** and the **template**. It owns
the authoritative **shared custom-type foundation (Phase 0)** that the search and
compression plans depend on:
- [`../search/custom_type_alpha_search_team_plan_2026-06-15.md`](../search/custom_type_alpha_search_team_plan_2026-06-15.md)
- [`../compress/custom_type_alpha_compression_team_plan_2026-06-15.md`](../compress/custom_type_alpha_compression_team_plan_2026-06-15.md)

## Prime directive

**The #1 deliverable is improving the Simple language**, measured by the stream
of concrete bug/feature items this work produces. Crypto/search/compression are
the vehicle. Therefore:
1. **Extract primitives → build intensive custom types first** (Phase 0), before
   any algorithm work.
2. Custom types **carry behavior** — methods, trait/mixin conformance, generics
   (`<>`), `me`-self-mutation, operators. Inert newtypes are rejected at review.
3. Every time a safe/short custom-type form forces a primitive workaround, **file
   a language item** (CLAUDE.md rule) — never silently normalize the workaround.

## Mode: alpha (existing contract)

Reuse `src/os/crypto/dual_backend.spl`. **alpha** = run C oracle + pure-Simple,
compare, fail-closed on mismatch. Most catalog items are **already implemented**
on primitives (see research in-tree table); this plan **refactors them onto
custom types** and proves alpha parity, it does not rebuild from zero.

## C-implementation policy

Permissive license (BSD/MIT/Apache/ISC/0BSD/PD) ⇒ vendor/bind existing C as the
alpha oracle under `src/runtime/vendor/**`. Copyleft (GPL/LGPL/unRAR-restricted)
⇒ write our own minimal C oracle. License gate table is in the research doc.

---

## Phase 0 — Shared custom-type foundation (BARRIER; lands before all 3 teams)

> **Search and compression plans reference this section. Do not redefine these
> types elsewhere** — duplicating `ByteSpan` across teams recreates the exact
> tech debt the compression research already flags.

Target module: **`src/lib/common/bytes/`** (new): `span.spl`, `bits.spl`,
`ints.spl`, `window.spl`, `checksum.spl`, `__init__.spl`.

Extracted primitives → custom types:

| Primitive | Custom type | Required behavior (stresses compiler) |
|-----------|-------------|----------------------------------------|
| `[u8]` + offset/len | `ByteSpan` | bounds-checked `slice()`, `get(i)`, `len()`, iteration, `==`; **generic-free value type** |
| growable `[u8]` | `ByteBuffer` | `me push_u8()/push_span()`, `freeze() -> ByteSpan` (tests `me`-self-mutation) |
| bit-packed read | `BitReader` | `me read_bits(n) -> u64`, LSB/MSB order, cursor invariant |
| bit-packed write | `BitWriter` | `me put_bits(v, n)`, `me align()`, `finish() -> ByteBuffer` |
| `i64` casts | `U16le/U32le/U64le` + BE | typed endian load/store, operator forms, `from_span()/to_span()` |
| sliding history | `RingWindow` | `me push()`, `match_len()`, wraparound invariant (shared by LZ + search) |
| `i64` checksums | `Crc32`, `Adler32` | incremental `me update(span)`, `value() -> U32be` |

Foundation acceptance:
- Each type has a `*_spec.spl` proving invariants and round-trips.
- A `bytes_foundation_spec.spl` proves `ByteBuffer.freeze()` ↔ `ByteSpan` and
  `BitWriter`→`BitReader` round-trip bit-exactly.
- **Zero `[u8]` indexing escapes** in downstream code review except inside the
  foundation module.

### dual_backend seam decision (language probe — resolve in Phase 0)

`dual_backend_run_bytes` is primitive-typed. Two options:
- **A (default):** custom types convert at the seam via `to_span()/from_span()`;
  keep `dual_backend` primitive. Lowest risk.
- **B (probe):** make `dual_backend_run<T: ByteEq>` generic over a custom type
  with trait-based equality. This directly tests generics + traits + custom
  equality. **Attempt B first**; if it forces a workaround, file a top-tier
  language item and fall back to A. Record the outcome in this section.

---

## Phase 1 — Crypto refactor onto custom types (per-team disjoint scope)

Fan out **after** Phase 0 barrier. Each sub-team owns **disjoint files** (memory:
same-dir agents clobber). C oracle via alpha for each.

| Sub-team | Scope (files) | Custom types | C oracle (permissive) |
|----------|---------------|--------------|------------------------|
| T1 hashes/MAC | `crypto/sha256.spl`, `sha512.spl`, `hmac.spl`, `hkdf.spl` | `Digest<N>`, `MacTag` | libsodium/BearSSL |
| T2 AEAD | `os/crypto/aes256_gcm.spl`, ChaCha20-Poly1305 | `Nonce<N>`, `AuthTag`, `Plaintext/Ciphertext` | libsodium |
| T3 sign/KX | `ecdsa_p256.spl`, Ed25519/X25519 | `SecretKey`, `PublicKey`, `Scalar`, `FieldElem` | libsodium/Monocypher |
| T4 seam+vectors | `dual_backend.spl` seam, typed NIST/RFC fixtures | (consumes all) | n/a |

In-scope staged subset (rest deferred): SHA-256/512, HMAC, HKDF, AES-256-GCM,
ChaCha20-Poly1305, Ed25519, X25519, ECDSA-P256. PQ/advanced/protocols deferred.

## Phase 2 — Hardening & parity

- Constant-time `AuthTag`/`Digest` comparison only; ban raw `==` on secret bytes.
- Alpha byte-for-byte parity across the rv64 live SSH lane + host.
- Fix the tracked ChaCha20-Poly1305 tag bug under the new typed path.

---

## Multi-agent team structure

- **Orchestrator (Opus):** owns Phase 0 barrier, seam decision, merges, and the
  language-item triage. Verifies + commits on sub-agents' behalf (memory: agents
  drop deliverables uncommitted).
- **Foundation agent:** Phase 0 only, then dissolves into review.
- **4 domain sub-agents (Sonnet), disjoint file scope**, spawned in parallel in a
  single message after the barrier. Each told in-prompt it has `advisor()` access.
- Commit per sub-batch immediately after lint-clean (jj reconcile clobbers
  uncommitted edits).

## Language-improvement capture loop (first-class output)

For each friction point: `bin/simple bug-add --id=<slug>` → `doc/08_tracking/bug/`,
or a feature request in `doc/02_requirements/feature/`. Expected hot spots from
memory (pre-seed the team): `me`-method self-mutation (E1052), struct-literal
`Type { field: value }` lexer rules, `array.get(n≥1)` corruption, Option-`Some`
forwarding at non-Optional boundaries, JIT string-method-on-var folding, generics
`<>` edge cases, named-arg/`me`-receiver callsite strictness. **A plan run that
produces no language items is a red flag, not a success.**

## Gates
`bin/simple test`, `bin/simple build lint`, foundation + crypto specs green,
alpha parity green host + rv64 lane, `verify` → `STATUS: PASS`.
