# Entry-import scanner loses ALL imports after any multi-byte UTF-8 line (seed char-offset substring)

- **Date:** 2026-11-11
- **Status:** FIXED (pure-Simple scanner side, lane p3-compiler4); seed-side primitive defect ROUTED to seed-fix lane
- **Routed from:** boot6 lane, PR #8199 (row 0 of the 2026-11-11 p3-compiler4 batch)
- **Severity:** HIGH for seed runs over non-ASCII sources — every import after the first
  multi-byte line is silently dropped from the entry closure, producing bogus
  `unresolved name` / `unresolved type` cascades in innocent importing modules.

## Symptom

On the refreshed Rust seed (`bin/simple.exe`, 2026-11-11 build, build-commit
`0791c2b7f4a7`, 37577216 bytes):

```
_driver_entry_import_module_paths("é\nuse std.a\nuse std.b\n") == []
```

expected `["std.a", "std.b"]`. Any source whose first multi-byte code point
appears before its import block loses the whole block.

## Root cause (verified by probes on this seed, 2026-11-11)

The scanner navigates in BYTE space: `_driver_line_end` is a `byte_at` scan and
returns byte offsets; loop guards use `byte_len()`. Line extraction then fed
those byte offsets into `content.substring(start, end)` / `content[a:b]`.

The Simple language contract (src/lib/common/string_core.spl:15 — "the
language's own `s.substring(a, b)` byte-offset method"; seed std
`src/compiler_rust/lib/std/src/core/string_ops.spl:37-67` — `impl Len for text:
fn len() = byte length`) is BYTE offsets. The seed runtime instead implements
`substring` / `text[a:b]` / `text.len()` with CHARACTER offsets, while
`byte_at` / `byte_len` stay byte-based. Measured on the seed with
`"é\nuse std.a\nuse std.b\n"` (23 bytes, 21 chars):

- `content.byte_len()` = 23 (byte-based)
- `content.len()` = 22 (lead-byte count — char-based)
- `content.substring(3, 12)` / `content[3:12]` = `"se std.a"` (char-based slice
  of byte offsets — desynced)

So `_driver_line_end` returns byte offset 12 for line 2, the char-based
substring slices characters 3..12 (`"se std.a\n"`), the `use ` prefix match
fails, and the import is skipped. Same desync for the `"""` docstring cursor,
which mixed `index_of` (char offsets) with byte-space line bounds, and for the
sibling scanner, which also guarded its loop with `content.len()`.

## Fix (this lane, pure-Simple scanner side)

`src/compiler/80.driver/driver_entry_closure_core.spl` (2026-11-11 block,
`_driver_substring_is_byte_based_v1` and helpers):

1. Probe the runtime's substring policy ONCE with a byte-built `"é"`
   (`rt_bytes_to_text([0xC3, 0xA9])`): byte-offset substring(0,1) equals the
   single byte 0xC3; char-offset substring(0,1) equals the two-byte character.
2. On byte-based runtimes (self-hosted, per the language contract) slice
   directly — zero behavioural change.
3. On char-based runtimes (the seed), convert line byte offsets to char
   offsets by counting UTF-8 lead bytes. Scanner line boundaries are ASCII
   newlines, which never split a multi-byte sequence, so the conversion is
   exact. The conversion cursor is threaded through each scan loop
   (`conv_byte`/`conv_char`), so each line costs O(line bytes), not O(file).
4. The `"""` docstring cursor now uses a byte-space scan
   (`_driver_triple_quote_byte_index_v1`), removing the `index_of`
   char-offset mixing entirely.
5. The sibling scanner's loop guard changed from `content.len()` to
   `content.byte_len()` (byte cursor consistency) and slices through the same
   defensive helper.

## Seed-side routing (seed-fix lane scope)

The primitive defect itself — the seed implements `text.substring`,
`text[a:b]`, and `text.len()` with character offsets, violating the byte-offset
language contract — is in `src/compiler_rust` (Rust seed). This lane does not
touch the seed. Seed-fix lane: make the seed's `substring`/slice/`len`
byte-offset to match the contract and the self-hosted runtime; until then the
defensive scanner probe above keeps pure-Simple code correct on both.

## Verification (seed-smoke, worktree seed 2026-11-11)

- NEW pin spec `test/01_unit/compiler/bootstrap/entry_closure_utf8_then_imports_spec.spl`
  (the routed repro + 2/3/4-byte widths + mid-file multi-byte line + docstring
  toggle + siblings + ASCII control): 6/6 PASS.
- `test/01_unit/compiler/bootstrap/entry_closure_non_ascii_import_scan_spec.spl`
  (previously 4/5 FAIL on this seed): 5/5 PASS.
- `test/01_unit/compiler/bootstrap/entry_closure_from_import_spec.spl`: 5/5 PASS.
- `native_entry_closure_gate_source_spec.spl`: 3/6 (baseline 2/6 — one case
  improved; remaining 3 failures pre-date this change).
- `entry_closure_physical_source_dedup_spec.spl`: 13/14, the 1 failure
  pre-dates this change (identical on the unmodified tree).
- `driver_entry_import_scan_cost_spec.spl`: not re-run to completion; documented
  internal budget > 930 s (`native_build_per_file_driver_overhead_2026-08-21.md:204`),
  SIGTERMed at ~897.5 s on this host pre-change. The scanner-path specs above
  pass in seconds.

All runs: `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe test
<spec> --mode=interpreter --no-cache`, labelled seed-smoke.
