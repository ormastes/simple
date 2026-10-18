# BLAKE3-256 / XXH3-128 / gzip hardening (pure Simple) — 2026-10-18

Branch: `release_phase3` (PR from `work/crypto-compress-harden-20261018`).

## Roles

| Algorithm | Role | Module |
|---|---|---|
| BLAKE3-256 | immutable artifacts, distributed cache objects, content verification | `src/lib/common/crypto/blake3.spl` |
| XXH3-128 (+XXH3-64) | fast local fingerprints, AST/TLDR cache indexing | `src/lib/common/crypto/xxh3.spl` |
| gzip / DEFLATE | RFC 1952 container + RFC 1951 stream, hardened decoder | `src/lib/nogc_sync_mut/compression/gzip/` |

BLAKE3 is the cryptographic choice; XXH3 is not collision-resistant and must
never be used where an adversary controls the input and a collision matters.

## Spec sources (transformed into SSpec scenarios)

- BLAKE3: `BLAKE3-team/BLAKE3-specs/blake3.pdf` + official `test_vectors/test_vectors.json`.
- XXH3: `Cyan4973/xxHash` `xxhash.h` (reference) + `doc/xxhash_spec.md` +
  `tests/sanity_test_vectors.h`. Sanity input buffer:
  `g = 2654435761; buf[i] = g >> 56; g *= 0x9E3779B185EBCA8D` (verified against
  the XXH32/XXH64 rows with the existing in-tree implementation).
- gzip: RFC 1951 (DEFLATE) and RFC 1952 (gzip), PDF + text from rfc-editor.org.

Vectors are copied verbatim from those files; no value is computed by the
implementation under test (see `fabricated_blake2s_65_byte_kat_2026-08-04.md`).

## Acceptance

1. Every official vector row selected at a code-path boundary passes.
2. Coverage on the touched modules: every function called, every decision
   seen both true and false (interpreter decision coverage,
   `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<p> simple run <spec>`).
3. gzip decoder rejects every malformed-input class in RFC 1951 §3.2 /
   RFC 1952 §2.3 without crashing or over-reading.
4. Perf/RSS measured before and after on the same binary; no regression.

## Evidence limits

Runs use the Rust-seed interpreter (`run` lane, `SPEC FILE VERDICT` line);
no pure-Simple self-hosted CLI is deployed on this aarch64 host.
