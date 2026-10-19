# Seed SMF header is repr(C)-padded; pure-Simple reader expects packed

**Date:** 2026-10-19
**Status:** open
**Area:** SMF format, seed (`src/compiler_rust`) vs pure-Simple (`src/compiler`, `src/os/smf`)

## Symptom

`dynsmf_artifact_witnesses_exports` (`src/os/smf/dynsmf_session.spl:319`)
returns false for every SMF the Rust seed writes. `smf_dynlib_validate`
fails with `invalid symbol count` on the seed-built crypto and compress
bundles, even though both carry all manifest exports as global symbols.

## Cause

The seed writes `SmfHeader` (`src/compiler_rust/common/src/smf/header.rs:9`,
`#[repr(C)]`) as raw struct bytes. repr(C) inserts 4 padding bytes after
`section_count` (offset 20), so `section_table_offset` is at 24,
`symbol_table_offset` at 32, `symbol_count` at 40, `exported_count` at 44.
The seed writer comments on this padding (`compiler/src/smf_writer.rs:172`).

The pure-Simple writer (`src/compiler/70.backend/linker/smf_header.spl:381`
`to_bytes`) and both pure-Simple readers
(`smf_header.spl:508`, `_SmfReaderMemory/header_parser.spl:508`,
`src/os/smf/smf_dynlib.spl:386`) use a packed layout: `section_table_offset`
at 20, `symbol_table_offset` at 28, `symbol_count` at 36.

So an SMF from one toolchain is misread by the other.

## Evidence

Seed (sha256 e357ff7f…) `compile --format=smf src/lib/common/crypto/dynsmf_entry.spl`:
header bytes 32..48 = `b83f1000 00000000 19080000 d7030000`, which is
symtab 0x103fb8, 2073 symbols, 983 exported. The pure-Simple validator
reads offset 36 and gets 0. A seed-layout parser finds all 34 crypto and all
16 compress manifest exports as global symbols.

## Impact

Bootstrap Stage 4c compiles bundles with the pure-Simple full CLI, which
writes packed headers, so that lane is not affected. Any seed-built SMF
checked by the pure-Simple loader or witness is rejected.

## Related, not investigated

On this aarch64 host, `simple run x.smf` dumps core even for a two-function
hello world built by the same seed. `compile --native` of the same source
runs correctly.
