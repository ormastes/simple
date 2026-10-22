# `workaround_bug_snapshot` verified the `#sdn-crc32` header in the `text` domain, not over the file's bytes
## Open 2026-10-22 — fixed same day in `src/app/bug/workaround_store.spl`

Date: 2026-10-22. Lane: compiler tooling (workaround-crc). Every compiler
build (native-build parent) refreshes known workarounds through
`refresh_workarounds` → `workaround_bug_snapshot`, which verifies the
`#sdn-crc32:` header of `doc/08_tracking/bug/bug_db.sdn` before use.

## Symptom

Pure-Simple-hosted compiler builds printed, on every build with indexed
workaround links:

```
workarounds: refresh failed: canonical bug database CRC mismatch
```

while the sealed header was correct: the stored CRC equaled
`zlib.crc32` of the exact on-disk bytes after the first line
(`#sdn-crc32:2090315492`, body 1,176,788 bytes, 551 non-ASCII bytes,
longest line 811 chars — measured 2026-10-22 on the release_phase3
checkout `4d058f7c73e`).

## Root cause

The check was `crc32_text(content.substring(newline + 1))` — the digest was
computed over a **`text` value**, not over the file's bytes. `text` passes
through a runtime string layer whose byte handling is a runtime convention:

- The seed-hosted runtime **rejects invalid UTF-8 at read birth**
  (`rt_file_read_regular_no_follow_bounded` → "content is not valid utf-8"),
  so `text` physically cannot represent some byte sequences a file-integrity
  header covers. Reproduced on this host: reading 80 bytes containing
  `0xff 0xfe` fails closed at the reader, before any CRC.
- On the pure-Simple-hosted build (the production compiler per AGENTS.md) the
  mismatch above was measured on content that seals correctly under
  `zlib.crc32` — the text layer's byte handling is the only stage that can
  diverge between read bytes and hashed bytes. (No pure-Simple binary exists
  on the 2026-10-22 host to bisect that stage further; the Rust seed binary
  hashes the file correctly in interpreter, smf, and native modes.)

The durable contract, already implemented by the sealing tool
(`scripts/check/reseal-sdn-crc32.shs`: `tail -n +2 | crc32`), is: **header
CRC == CRC-32/ISO-HDLC over the file's raw bytes after the first LF (0x0A)**.

## Fix (same change, `src/app/bug/workaround_store.spl`)

- The header is now verified in the byte domain:
  `crc32_bytes_from(content.bytes(), first_lf + 1)`, where `first_lf` is
  located by scanning the byte array for 0x0A. The bounded reader's string
  birth is a raw buffer copy on every deployed runtime (memcpy at
  `runtime_native.c:3284` and the seed's `rt_string_new`; verified
  byte-identical on the real 1.1 MB database), so `content.bytes()` IS the
  file's byte content.
- New byte-domain entry points in
  `src/lib/nogc_sync_mut/compression/gzip/crc.spl`: `crc32_bytes([u8])` and
  `crc32_bytes_from([u8], start)` (in-place table walk; the per-byte `push`
  rebuild is O(n^2), ~1185x measured, same defect class the `crc32_text`
  [u8] rebuild hit).
- No weakening: the check is still fail-closed and still discriminates single
  bytes. Compatibility: the byte domain IS the sealing tool's domain, so every
  existing correctly sealed file verifies unchanged (the repo's
  `bug_db.sdn` header `2090315492` still verifies; no reseal needed, no row
  content touched). A CRLF working copy still fails closed (its bytes were
  sealed over LF in git — refresh the file from the index; do NOT reseal).

## Companion bug found while pinning the repro: committed checkpoint-only WAL

`doc/08_tracking/bug/bug_db.sdn.wal` is **committed at HEAD** (checkpoint-only:
`#wal-version:2` + one `Checkpoint` row, zero pending entries — residue of
`SdnDatabase.save()`'s checkpoint step, swept in by
`bb3f6ab8ab2 rebase(main): transplant current tree`). The snapshot gate refused
on ANY non-empty WAL, so on a clean checkout of this release the refresh
failed 100% of the time with "checkpoint the canonical bug database WAL
before workaround refresh" — before the CRC gate was even reached. The gate
now refuses on WAL **content** (`wal_has_pending_content`): any row that is
not blank, a `#` header, or a `Checkpoint` row refuses (fail-closed on
unclassifiable bytes too); a checkpoint-only WAL cannot block every refresh.

## Evidence

- `test/01_unit/lib/nogc_sync_mut/compression/crc32_bytes_domain_spec.spl` —
  byte-domain KAT, Korean multibyte, invalid-UTF-8 byte coverage
  (`crc32_bytes == zlib.crc32 == 3153239212` on bytes no `text` can hold),
  821-byte long line, single-byte corruption discrimination.
- `test/01_unit/app/bug/bug_snapshot_crc_spec.spl` — the repository's real
  `bug_db.sdn` snapshot now succeeds; byte-sealed non-ASCII and CRLF-sealed
  fixtures verify; tampered body, seal-domain skew (LF header vs CRLF bytes),
  pending-entry WAL, and invalid-UTF-8 inputs all fail closed.
- Regressions: `crc32_text_crosslang_spec.spl` 6/6, `gzip_validate_crc_isize_spec.spl` 6/6.

## Pre-existing failure NOT addressed here (out of lane)

`test/02_integration/app/bug_workaround_store_spec.spl` fails on this Windows
host at `expect(workaround_host_remove(...)).to_equal(true)` — the seed
runtime's `rt_file_remove` returns false for the fixture file (reproduces on
the base commit without this change; the last expect before it,
`refresh ... is_err()` on a garbage WAL, passes with the new gate).
Owner: `src/lib/nogc_sync_mut/io/file_ops.spl` / seed runtime, not
`src/app/bug`.
