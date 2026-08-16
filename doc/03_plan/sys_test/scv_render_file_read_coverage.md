# SCV and rendering file-read coverage system-test plan

Status: Modern SSpec source and authored mirror complete; execution is blocked —
no qualified pure-Simple runtime exists in the workspace (Rust seed is not
admissible evidence; the on-disk bootstrap stages segfault on a two-line
program, see
`doc/08_tracking/bug/origin_main_seed_unbuildable_duplicate_heap_counter_symbols_2026-08-16.md`).
No pass is claimed.

## Scope

Covers the byte-level contract of the two canonical file-read entry points in
`src/lib/nogc_sync_mut/io/file_ops.spl` after the 2026-08-16 signature
unification: `file_read_bytes -> [u8]` and `file_read_bytes_i64 -> [i64]`.

In scope: length preservation, element range, agreement between the two shapes,
lossless round-trip of every byte value including above 0x7F, and preservation
of the sfnt version bytes when reading a real font asset through the byte API
(the rendering read path).

Excluded: SCV pack, delta, merge, and integrity semantics; whether the several
same-named `file_read_bytes` definitions across the tree agree with one another
(a static definition-count concern, tracked separately); any claim about which
execution engine lowers these calls.

Executable:
`test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl`.

Authored mirror:
`doc/06_spec/03_system/stdlib/io/scv_render_file_read_contract_spec.md`.

## Why this coverage exists

The 2026-08-16 change altered `file_read_bytes` from `[i64]` to `[u8]` and
introduced `file_read_bytes_i64` for the raw shape, migrating ten `src/lib/scv/`
modules and `cache_validator.spl`. Review at `f6cadcc36af` confirmed the
migration is internally consistent and that the font/rendering path binds a
different, already-`[u8]` definition and is unaffected. Nothing, however,
asserted the byte fidelity itself at runtime — a future reshaping of either
entry point would again be caught only by inspection.

## Frozen primary flow

1. `Create the scratch directory and write bytes 0..255`
2. `Read the fixture through the canonical byte entry point`
3. `Read the fixture through the raw i64 entry point`
4. `Read the same fixture through both entry points`
5. `Read the font asset as bytes`

## Requirements

| ID | Requirement |
|---|---|
| REQ-IOREAD-001 | `file_read_bytes` returns a `[u8]` whose length equals the bytes written |
| REQ-IOREAD-002 | `file_read_bytes` reports each byte at its written index across the full 0..255 range |
| REQ-IOREAD-003 | `file_read_bytes_i64` returns a `[i64]` of the same length with no element sign-extended below zero |
| REQ-IOREAD-004 | Both entry points report the same byte at every index for the same file |
| REQ-IOREAD-005 | Reading a real TrueType asset through the byte API preserves the leading sfnt version bytes `00 01 00 00` |
| REQ-IOREAD-006 | The text and byte read families agree on length and content for an ASCII payload |

## Traceability matrix

| Requirement | Scenario | Assertion |
|---|---|---|
| REQ-IOREAD-001 | should return unsigned bytes from the canonical read | `bytes.len() == 256` |
| REQ-IOREAD-002 | should return unsigned bytes from the canonical read | `mismatches == 0` over indices 0..255 |
| REQ-IOREAD-003 | should return the same bytes from the raw i64 read | `raw.len() == 256`, `negatives == 0` |
| REQ-IOREAD-004 | should agree between the unsigned and raw read shapes | `disagreements == 0` |
| REQ-IOREAD-005 | should preserve the sfnt version bytes of a real font | leading bytes equal `0,1,0,0` |
| REQ-IOREAD-006 | should report the same ASCII content through both read families | `as_text == "SCV"`, `as_bytes[0] == 83` |

## Fail-closed design

Every precondition is asserted, never assumed: a scratch write that fails and a
missing font asset both call `fail(...)`. No scenario calls `skip(...)`, and no
oracle is stubbed to pass. An environment that cannot satisfy the contract
therefore cannot report green — the specification either runs and asserts, or it
fails. This is deliberate: a skip-on-missing-runtime design would have let this
lane look covered while proving nothing.

## Fixtures

- Scratch: `build/test/stdlib_io_read_contract/` (created by the spec).
- Font: `assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf`, a static
  TrueType face whose first four bytes were verified to be `00 01 00 00`.

## Execution readiness

The specification is complete and designed to run unchanged. Execution requires
a qualified pure-Simple runtime, which requires a working bootstrap, which is
currently blocked by duplicate `rt_heap_live_bytes` / `rt_heap_peak_bytes`
symbols at link time. When that is resolved, run the spec and record the result
here; until then this plan states blocked, not passing.
