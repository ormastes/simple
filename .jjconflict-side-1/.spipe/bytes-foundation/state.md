# Feature: bytes-foundation

## Raw Request
Implement the search/pattern-matching plan fully with intensive custom types via
the SPipe dev workflow and agents. Per the plan
(`doc/03_plan/lib/crypto/custom_type_alpha_crypto_team_plan_2026-06-15.md`
§Phase-0), the shared custom-type foundation is a barrier that must land before
search/security/compression fan out. This feature is that barrier.

## Task Type
feature

## Refined Goal
Create `src/lib/common/bytes/` providing behavior-carrying custom types
(`ByteSpan`, `ByteBuffer`, `BitReader`, `BitWriter`, little/big-endian fixed-width
integer views, `RingWindow`, `Crc32`, `Adler32`) that replace ad-hoc `[u8]`/`i64`
primitive usage, consolidating existing `common/net/byte_cursor.spl` and the
brotli/zstd `bit_reader.spl` patterns, with full SSpec coverage and zero
behavior regressions.

## Acceptance Criteria
- AC-1: `src/lib/common/bytes/` exists with `span.spl`, `bits.spl`, `ints.spl`,
  `window.spl`, `checksum.spl`, `__init__.spl`; each type carries behavior
  (methods, `me`-self-mutation, operators where natural), not inert newtypes.
- AC-2: `ByteSpan` supports bounds-checked `slice`, `get`, `len`, iteration, and
  value equality; out-of-bounds access fails closed (no corruption).
- AC-3: `ByteBuffer` supports `me push_u8`/`me push_span` and `freeze() -> ByteSpan`;
  round-trip `ByteBuffer.freeze()` ↔ `ByteSpan` is byte-exact.
- AC-4: `BitWriter` → `BitReader` round-trips bit-exactly for both LSB-first and
  MSB-first orderings across non-byte-aligned widths (1..64 bits).
- AC-5: `U16le/U32le/U64le` + big-endian variants load/store round-trip against
  known fixtures; endianness is correct against hand-computed values.
- AC-6: `RingWindow` `push`/`match_len`/`copy_match` preserve the sliding-window
  distance invariant (shared primitive for LZ + search).
- AC-7: `Crc32` and `Adler32` incremental `update`/`value` match known test
  vectors (e.g. CRC32 of "123456789" = 0xCBF43926; relocate `src/os/crypto/adler32.spl`).
- AC-8: A `bytes_foundation_spec.spl` proves the cross-type round-trips (AC-3,
  AC-4) with absolute-oracle assertions (known values), not self-comparison.
- AC-9: `bin/simple test test/01_unit/lib/common/bytes/` is green in interpreter
  mode; `bin/simple build lint` clean for the new files.
- AC-10: Every language friction point (compiler bug, forced primitive
  workaround, perf cliff) is filed via `bin/simple bug-add` / a feature request
  under `doc/02_requirements/feature/` — the improvement stream is a deliverable.

## Scope Exclusions
- No search/crypto/compression algorithm work (separate downstream features).
- No SIMD specialization yet (scalar oracle first; SIMD lands in domain phases).
- No dual_backend generic-seam change here (that probe is in the crypto feature).

## Phase
dev-done

## Log
- dev: Created state file with 10 acceptance criteria (type: feature)
- dev-done: Implemented src/lib/common/bytes/ (span, bits, ints, window,
  checksum, __init__). 52 it-blocks green in interpreter mode (seed driver),
  lint clean. AC-1..AC-9 met with absolute oracles (CRC32=0xCBF43926,
  Adler32=0x091E01DE, hand-computed endian/bit patterns, 1..64-bit round-trips,
  ByteBuffer.freeze() <-> ByteSpan). `==` and facade import verified working;
  `for-in` over custom struct found broken. AC-10 items filed:
  bug for_in_custom_struct_no_iterator_protocol_2026-06-15,
  bug build_lint_subcommand_triggers_full_driver_rebuild_2026-06-15,
  feature custom_type_iterator_protocol.md. Adler-relocate deviation: kept
  src/os/crypto/adler32.spl + src/lib/common/hash/adler32.spl (live callers /
  spec) and implemented fresh Adler32 type instead of moving the file.
