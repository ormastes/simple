# Parallel Agent Plan — Debug Format Verification & Interpreter Bug Fixes

**Created:** 2026-05-08
**Context:** Phases 1-4 of pure-Simple debug info parsing are COMPLETE (16 new files, 22 interpreter-mode tests pass). Two interpreter bugs block deep verification. This plan defines 7 parallel agents to fix bugs + add comprehensive tests.

## Dependency Graph

```
Wave 1 (parallel, no deps):
  Agent A: Fix bytes_to_u* interpreter externs
  Agent B: Fix ! (bang) unwrap parser in interpreter

Wave 2 (parallel, after Agent A completes):
  Agent C: Round-trip tests (Mach-O write→parse→verify)
  Agent D: DWARF line program + parser tests
  Agent E: PDB/CodeView end-to-end tests
  Agent F: Golden-file tests (compile .spl with -g, parse debug info)

Wave 3 (sequential, after Wave 2):
  Agent G: Phase 5 — [u8] migration of elf_inspect/elf_parser
```

## Blocking Bug References

| Bug ID | File | Blocks |
|--------|------|--------|
| `interpreter_missing_bytes_to_u32_extern_2026-05-08` | `doc/08_tracking/bug/interpreter_missing_bytes_to_u32_extern_2026-05-08.md` | Agents C, D, E, F |
| `interpreter_bang_unwrap_member_access_2026-05-08` | `doc/08_tracking/bug/interpreter_bang_unwrap_member_access_2026-05-08.md` | Revert workarounds after fix |

---

## Agent A: Fix `bytes_to_u*` Interpreter Externs

**Wave:** 1 (day-1, parallel with B)
**Estimated effort:** ~200 lines Rust

### File Scope (write)
- `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs` — add 6 new extern functions
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — register new externs in dispatch table
- `src/compiler_rust/compiler/src/interpreter_call/mod.rs` — wire extern dispatch (if needed)

### File Scope (read-only)
- `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` — reference C stub implementations for correct semantics (lines 259-310)
- `src/lib/nogc_sync_mut/binary_io.spl` — understand call signatures (`bytes_to_u32_le(bytes)` at ~line 196)
- `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs` — existing `rt_bytes_to_text_fn` as pattern (line 115-116)
- `doc/08_tracking/bug/interpreter_missing_bytes_to_u32_extern_2026-05-08.md` — bug spec

### Acceptance Criteria
1. Register these 6 externs in the interpreter extern dispatch:
   - `bytes_to_u16_le(b0: u8, b1: u8) -> u16`
   - `bytes_to_u16_be(b0: u8, b1: u8) -> u16`
   - `bytes_to_u32_le(b0: u8, b1: u8, b2: u8, b3: u8) -> u32`
   - `bytes_to_u32_be(b0: u8, b1: u8, b2: u8, b3: u8) -> u32`
   - `bytes_to_u64_le(b0..b7: u8) -> u64`
   - `bytes_to_u64_be(b0..b7: u8) -> u64`
2. `bin/simple test src/lib/nogc_sync_mut/debug/formats/test/msf_parser_spec.spl` passes (currently works with workaround; after fix, can import real `msf_parse`)
3. `BinaryReader.read_u32(ByteOrder.LittleEndian)` works in interpreter mode — verify with a minimal test:
   ```spl
   use std.binary_io.{BinaryReader, ByteOrder}
   val reader = BinaryReader([0x01, 0x00, 0x00, 0x00])
   val v = reader.read_u32(ByteOrder.LittleEndian)
   expect(v).to_equal(1)
   ```
4. `cargo test` in `src/compiler_rust/compiler/` passes
5. Full `bin/simple test` passes (22+ tests)
6. Run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` to rebuild self-hosted binary with new externs

### Commit
Single commit: `fix: register bytes_to_u{16,32,64}_{le,be} externs in interpreter`

### On Completion
Update bug doc `interpreter_missing_bytes_to_u32_extern_2026-05-08.md`: add "**Fixed:** 2026-05-XX" header, move to resolved section.

### Agent Prompt (copy-paste)
```
You are fixing a bug in the Simple language interpreter. The interpreter
does not register the `bytes_to_u32_le`, `bytes_to_u32_be`, and similar
byte-conversion extern functions, so any code calling BinaryReader.read_u16/
u32/u64 fails with "unknown extern function: bytes_to_u32_le".

Bug doc: doc/08_tracking/bug/interpreter_missing_bytes_to_u32_extern_2026-05-08.md

The native-compile path implements these as C stubs in:
  src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs (lines 259-310)
  — look at bytes_to_u32_le: takes 4 u8 args, returns u32 via bit-shift.

The interpreter extern dispatch is in:
  src/compiler_rust/compiler/src/interpreter_extern/mod.rs
  src/compiler_rust/compiler/src/interpreter_extern/conversion.rs
  src/compiler_rust/compiler/src/interpreter_call/mod.rs
  src/compiler_rust/compiler/src/interpreter_eval.rs

Follow the pattern of existing externs (e.g., rt_bytes_to_text_fn in
conversion.rs line 115). Add 6 functions: bytes_to_u{16,32,64}_{le,be}.
Each takes N u8 args and returns the assembled integer.

After implementing, verify:
  1. cargo test in src/compiler_rust/compiler/
  2. bin/simple test (all 22+ tests pass)
  3. scripts/bootstrap/bootstrap-from-scratch.sh --deploy

You have advisor() access — call it before writing code and before declaring done.
Commit message: "fix: register bytes_to_u{16,32,64}_{le,be} externs in interpreter"

IMPORTANT: Use jj for VCS. Never create branches. Work on main.
```

---

## Agent B: Fix `!` (Bang) Unwrap Parser in Interpreter

**Wave:** 1 (day-1, parallel with A)
**Estimated effort:** ~100-200 lines Rust

### File Scope (write)
- `src/compiler_rust/compiler/src/interpreter_eval.rs` — postfix expression evaluation (likely main fix location)
- `src/compiler_rust/compiler/src/interpreter/mod.rs` — expression parsing / evaluation
- `src/compiler_rust/compiler/src/interpreter_macro_invocation.rs` — if bang handling touches macro paths

### File Scope (read-only)
- `doc/08_tracking/bug/interpreter_bang_unwrap_member_access_2026-05-08.md` — bug spec with 3 failing cases
- `src/compiler_rust/compiler/src/predicate.rs` — may have unwrap/bang logic
- `src/compiler_rust/compiler/src/build_mode.rs` — bang references

### Acceptance Criteria
1. All three failing patterns now work in interpreter mode:
   - **Case A:** `val y = x!` (bare variable unwrap)
   - **Case B:** `val y = best!.address` (unwrap + member access chain)
   - **Case C:** `expect(result.err()!)` and `Err(x.err()!)` (unwrap inside function args)
2. Existing working pattern still works: `val v = result.ok()!` at statement end
3. Write a minimal test spec to verify all 3 cases:
   ```spl
   # test/interpreter_bang_unwrap_spec.spl
   describe "Bang Unwrap":
       it "unwraps bare variable":
           val x: i64? = 42
           val y = x!
           expect(y).to_equal(42)
       it "unwraps with member access":
           # use struct or tuple that has a field
       it "unwraps inside function args":
           val x: i64? = 42
           expect(x!).to_equal(42)
   ```
4. `bin/simple test` passes (22+ tests)
5. `cargo test` in `src/compiler_rust/compiler/` passes

### Commit
Single commit: `fix: allow ! unwrap on bare variables and in non-terminal positions`

### On Completion
1. Update bug doc `interpreter_bang_unwrap_member_access_2026-05-08.md`: add "**Fixed:** 2026-05-XX"
2. Revert workarounds in these files (restore original `!` syntax):
   - `src/lib/nogc_sync_mut/debug/formats/test/dwarf_abbrev_spec.spl` (lines 75-79)
   - `src/lib/nogc_sync_mut/debug/formats/dwarf_parser.spl` (lines ~285-292)
   - `src/lib/nogc_sync_mut/debug/formats/pdb_parser.spl` (lines ~152, 162, 285-292)
   - `src/compiler/70.backend/linker/macho_inspect.spl` (line 144)
   - `src/compiler/70.backend/linker/macho_parser.spl` (line 312)
   - `src/compiler/70.backend/linker/pe_inspect.spl` (line 247)
   - `src/compiler/70.backend/linker/pe_parser.spl` (line 266)
   - NOTE: `msf_parser.spl` and `msf_parser_spec.spl` are NOT in scope — their
     workaround (inline magic-check) is an extern issue, handled by Agent E.

### Agent Prompt (copy-paste)
```
You are fixing a bug in the Simple language interpreter's expression parser.
The interpreter rejects the `!` (unwrap) postfix operator in most positions,
only allowing it after method calls at statement end (e.g., `result.ok()!`).

Bug doc: doc/08_tracking/bug/interpreter_bang_unwrap_member_access_2026-05-08.md

Three cases fail:
  Case A: `val y = x!`  → "expected '(', '{', or '[', found Newline"
  Case B: `val y = best!.address` → parse error
  Case C: `expect(result.err()!)` → "expected Comma, found Bang"

The lint pass (bin/simple build lint) accepts ALL forms — only the interpreter
rejects them. The interpreter expression parser is in:
  src/compiler_rust/compiler/src/interpreter_eval.rs
  src/compiler_rust/compiler/src/interpreter/mod.rs

Search for where `!` / Bang / postfix operators are parsed in the expression
evaluator. The fix should allow `!` after any expression, and allow the result
to be followed by `.` (member access), `)` (closing paren), `,` (arg separator),
or newline.

After fixing, verify:
  1. cargo test in src/compiler_rust/compiler/
  2. bin/simple test (all 22+ tests pass)
  3. Revert workarounds in .spl files listed in the bug doc "Affected Files" table

You have advisor() access — call it before writing code and before declaring done.
Commit as two commits:
  1. "fix: allow ! unwrap on bare variables and in non-terminal positions"
  2. "refactor: revert ! unwrap workarounds in debug format + linker files"

IMPORTANT: Use jj for VCS. Never create branches. Work on main.
IMPORTANT: The workaround revert (commit 2) touches files outside your primary
scope — only change the specific workaround lines listed in the bug doc table.
```

---

## Agent C: Round-Trip Tests (Mach-O Write → Parse → Verify)

**Wave:** 2 (after Agent A completes)
**Depends on:** Agent A (needs `BinaryReader.read_u32` working)

### File Scope (write)
- `src/lib/nogc_sync_mut/debug/formats/test/macho_roundtrip_spec.spl` — NEW test file
- `src/compiler/70.backend/linker/test/macho_roundtrip_spec.spl` — NEW (if linker test dir exists)

### File Scope (read-only)
- `src/compiler/70.backend/backend/native/macho_writer.spl` — MachOWriter, MachOSection, MachOSymbol
- `src/compiler/70.backend/linker/macho_inspect.spl` — MachOInspector, macho_inspect()
- `src/compiler/70.backend/linker/macho_parser.spl` — MachOObject, macho_parse_object()
- `src/lib/nogc_sync_mut/binary_io.spl` — BinaryReader, BinaryWriter

### Acceptance Criteria
1. Write Mach-O via `MachOWriter` → parse back with `macho_parse_object()` → assert:
   - Section count matches
   - Section names match
   - Symbol count matches
   - Symbol names match
   - Entry point matches
2. Similarly for `macho_inspect()` → verify header fields round-trip
3. All new tests pass in interpreter mode
4. `bin/simple test` passes (25+ tests)

### Commit
`test: add Mach-O round-trip tests for macho_writer → macho_parser`

### Agent Prompt (copy-paste)
```
You are writing round-trip tests for the Mach-O format parser. The Simple
language project has a MachOWriter (write-only) and a MachOParser (read-only).
You need to verify they agree.

Writer: src/compiler/70.backend/backend/native/macho_writer.spl
  — MachOWriter, MachOSection, MachOSymbol, ByteBuffer
Parser: src/compiler/70.backend/linker/macho_parser.spl
  — MachOObject, macho_parse_object()
Inspector: src/compiler/70.backend/linker/macho_inspect.spl
  — MachOInspector, macho_inspect()

Create test file at:
  src/lib/nogc_sync_mut/debug/formats/test/macho_roundtrip_spec.spl

Test plan:
1. Construct a minimal Mach-O binary in memory using MachOWriter
2. Parse the result with macho_parse_object()
3. Assert section count, names, symbol count, names, entry point all match
4. Also test macho_inspect() on the same binary

Use BinaryReader/BinaryWriter from std.binary_io for any byte manipulation.
The test file uses SSpec: describe/it blocks with expect().to_equal().
See existing tests at src/lib/nogc_sync_mut/debug/formats/test/ for the pattern.

PREREQUISITE: Agent A must have fixed bytes_to_u* externs first. If
BinaryReader.read_u32 fails with "unknown extern", this agent cannot proceed.

You have advisor() access — call it before writing tests and before declaring done.
Commit: "test: add Mach-O round-trip tests for macho_writer → macho_parser"

IMPORTANT: Use jj for VCS. Never create branches. Work on main.
```

---

## Agent D: DWARF Line Program + Parser Tests

**Wave:** 2 (after Agent A completes)
**Depends on:** Agent A (needs `BinaryReader.read_u16/u32` working)

### File Scope (write)
- `src/lib/nogc_sync_mut/debug/formats/test/dwarf_line_spec.spl` — NEW test file
- `src/lib/nogc_sync_mut/debug/formats/test/dwarf_parser_spec.spl` — NEW test file

### File Scope (read-only)
- `src/lib/nogc_sync_mut/debug/formats/dwarf_line_program.spl` — DwarfLineHeader, dwarf_decode_line_program()
- `src/lib/nogc_sync_mut/debug/formats/dwarf_parser.spl` — DwarfParser, from_elf(), addr_to_source()
- `src/lib/nogc_sync_mut/debug/formats/dwarf_constants.spl` — DW_TAG_*, DW_AT_*, DW_LNS_*
- `src/lib/nogc_sync_mut/debug/formats/dwarf_abbrev.spl` — already tested
- `src/lib/nogc_sync_mut/debug/formats/debug_types.spl` — SourceLocation, DebugLineEntry

### Acceptance Criteria
1. `dwarf_line_spec.spl` tests:
   - Parse a minimal DWARF line program header from hand-crafted bytes
   - Verify `minimum_instruction_length`, `default_is_stmt`, `line_base`, `line_range`
   - Decode a trivial line program (DW_LNS_advance_pc + DW_LNS_advance_line + special opcodes)
   - Verify resulting `[DebugLineEntry]` has correct address/line pairs
2. `dwarf_parser_spec.spl` tests:
   - Construct minimal `.debug_info` + `.debug_abbrev` + `.debug_line` sections in `[u8]`
   - Parse with `DwarfParser` constructor
   - Verify `addr_to_source()` returns correct SourceLocation
   - Verify `function_at()` finds the right function
   - Verify `compilation_units()` returns expected CU names
3. All tests pass in interpreter mode
4. `bin/simple test` passes (27+ tests)

### Commit
`test: add DWARF line program and parser specification tests`

### Agent Prompt (copy-paste)
```
You are writing specification tests for the DWARF debug format parser in the
Simple language project. Two test files are needed.

Library files (read-only):
  src/lib/nogc_sync_mut/debug/formats/dwarf_line_program.spl
    — DwarfLineHeader, dwarf_decode_line_program()
  src/lib/nogc_sync_mut/debug/formats/dwarf_parser.spl
    — DwarfParser class, from_elf(), addr_to_source(), function_at()
  src/lib/nogc_sync_mut/debug/formats/dwarf_constants.spl
    — DW_TAG_*, DW_AT_*, DW_LNS_* constants
  src/lib/nogc_sync_mut/debug/formats/dwarf_abbrev.spl
    — already tested (read for context)
  src/lib/nogc_sync_mut/debug/formats/debug_types.spl
    — SourceLocation, DebugLineEntry, DebugFunction

Create two test files:
1. src/lib/nogc_sync_mut/debug/formats/test/dwarf_line_spec.spl
   — Test DwarfLineHeader parsing from hand-crafted bytes
   — Test dwarf_decode_line_program with a minimal program
   — Verify address/line pairs in output DebugLineEntry list

2. src/lib/nogc_sync_mut/debug/formats/test/dwarf_parser_spec.spl
   — Construct minimal .debug_info + .debug_abbrev + .debug_line in [u8]
   — Test DwarfParser construction and query methods
   — Verify addr_to_source(), function_at(), compilation_units()

See existing test pattern at:
  src/lib/nogc_sync_mut/debug/formats/test/dwarf_abbrev_spec.spl

PREREQUISITE: Agent A must have fixed bytes_to_u* externs.

You have advisor() access — call it before writing tests and before declaring done.
Commit: "test: add DWARF line program and parser specification tests"

IMPORTANT: Use jj for VCS. Never create branches. Work on main.
```

---

## Agent E: PDB/CodeView End-to-End Tests

**Wave:** 2 (after Agent A completes)
**Depends on:** Agent A (needs `BinaryReader.read_u32` working)

### File Scope (write)
- `src/lib/nogc_sync_mut/debug/formats/test/pdb_parser_spec.spl` — NEW test file
- `src/lib/nogc_sync_mut/debug/formats/test/codeview_records_spec.spl` — NEW test file

### File Scope (read-only)
- `src/lib/nogc_sync_mut/debug/formats/pdb_parser.spl` — PdbParser class
- `src/lib/nogc_sync_mut/debug/formats/msf_parser.spl` — MsfFile, msf_parse()
- `src/lib/nogc_sync_mut/debug/formats/codeview_records.spl` — CvSymRecord, cv_parse_*()
- `src/lib/nogc_sync_mut/debug/formats/pdb_constants.spl` — PDB stream indices, symbol kinds
- `src/lib/nogc_sync_mut/debug/formats/test/msf_parser_spec.spl` — existing MSF tests (reference)

### Acceptance Criteria
1. `codeview_records_spec.spl` tests:
   - Parse a hand-crafted CodeView symbol record (S_GPROC32)
   - Verify `cv_decode_proc_symbol()` extracts name, offset, code_size
   - Parse a line subsection, verify file_index and line pairs
   - Parse a file checksum record, verify name_offset
2. `pdb_parser_spec.spl` tests:
   - Construct minimal MSF container + DBI stream + module stream in `[u8]`
   - Parse with `PdbParser.parse()`
   - Verify `functions` list has expected entries
   - Verify `addr_to_source()` returns correct location
   - Verify `compilation_units()` count
3. Update `msf_parser_spec.spl` to use real `msf_parse()` now that `bytes_to_u32_le` works
4. All tests pass in interpreter mode
5. `bin/simple test` passes (29+ tests)

### Commit
Two commits:
1. `test: add CodeView records and PDB parser specification tests`
2. `refactor: update msf_parser_spec to use real msf_parse after extern fix`

### Agent Prompt (copy-paste)
```
You are writing specification tests for the PDB/CodeView debug format parser
in the Simple language project. Two new test files plus one update.

Library files (read-only):
  src/lib/nogc_sync_mut/debug/formats/pdb_parser.spl — PdbParser class
  src/lib/nogc_sync_mut/debug/formats/msf_parser.spl — MsfFile, msf_parse()
  src/lib/nogc_sync_mut/debug/formats/codeview_records.spl — CvSymRecord, cv_parse_*()
  src/lib/nogc_sync_mut/debug/formats/pdb_constants.spl — constants

Existing test (reference pattern):
  src/lib/nogc_sync_mut/debug/formats/test/msf_parser_spec.spl

Create:
1. src/lib/nogc_sync_mut/debug/formats/test/codeview_records_spec.spl
   — Test cv_decode_proc_symbol() with S_GPROC32 bytes
   — Test cv_parse_line_subsections() with minimal line data
   — Test cv_parse_file_checksums()

2. src/lib/nogc_sync_mut/debug/formats/test/pdb_parser_spec.spl
   — Build minimal MSF+DBI+module bytes (this is complex — build bottom-up)
   — Test PdbParser.parse(), verify functions, addr_to_source, units

3. Update src/lib/nogc_sync_mut/debug/formats/test/msf_parser_spec.spl
   — Now that bytes_to_u32_le extern works, add tests that call real msf_parse()
   — Keep existing check_msf_magic tests, ADD new tests using msf_parse

PREREQUISITE: Agent A must have fixed bytes_to_u* externs.

You have advisor() access — call it before writing tests and before declaring done.
Commits:
  1. "test: add CodeView records and PDB parser specification tests"
  2. "refactor: update msf_parser_spec to use real msf_parse after extern fix"

IMPORTANT: Use jj for VCS. Never create branches. Work on main.
```

---

## Agent F: Golden-File Tests (Compile .spl → Parse Debug Info)

**Wave:** 2 (after Agent A completes)
**Depends on:** Agent A (needs `BinaryReader` working), ideally also Agent B for clean syntax

### File Scope (write)
- `src/lib/nogc_sync_mut/debug/formats/test/golden_elf_dwarf_spec.spl` — NEW
- `test/fixtures/debug/` — small compiled fixture binaries (if needed)

### File Scope (read-only)
- `src/lib/nogc_sync_mut/debug/formats/dwarf_parser.spl` — DwarfParser.from_elf()
- `src/lib/nogc_sync_mut/debug/formats/debug_provider.spl` — DebugInfoProvider trait
- `src/lib/nogc_sync_mut/debug/remote/dwarf.spl` — FFI-based DWARF consumer (parity target)
- `src/compiler/70.backend/linker/elf_parser.spl` — ELF parsing

### Acceptance Criteria
1. Compile a minimal `.spl` file with debug info (`-g` flag)
2. Read the resulting ELF binary as `[u8]`
3. Parse with `DwarfParser.from_elf()`
4. Assert:
   - `compilation_units()` contains the source file name
   - `line_entries_all()` is non-empty
   - `addr_to_source(some_known_addr)` returns a SourceLocation with correct file
   - `function_at(addr)` returns the expected function name
5. **FFI parity:** Compare `DwarfParser.addr_to_source()` output against FFI `rt_dwarf_addr_to_line()` on the same binary — results must be identical
6. All tests pass
7. `bin/simple test` passes (30+ tests)

### Commit
`test: add golden-file ELF+DWARF integration tests with FFI parity check`

### Agent Prompt (copy-paste)
```
You are writing golden-file integration tests for the DWARF debug info parser.
The goal is to compile a Simple program with debug info, parse the resulting
ELF binary with the pure-Simple DwarfParser, and verify the debug info matches
what the FFI-based DWARF consumer returns.

Key files:
  src/lib/nogc_sync_mut/debug/formats/dwarf_parser.spl — DwarfParser.from_elf()
  src/lib/nogc_sync_mut/debug/remote/dwarf.spl — FFI rt_dwarf_addr_to_line()
  src/compiler/70.backend/linker/elf_parser.spl — ELF section reading

Create: src/lib/nogc_sync_mut/debug/formats/test/golden_elf_dwarf_spec.spl

Test plan:
1. Use bin/simple to compile a known .spl file with -g (debug info)
2. Read the ELF output into [u8]
3. Parse with DwarfParser.from_elf()
4. Assert compilation_units, line_entries, addr_to_source, function_at
5. Compare against FFI rt_dwarf_addr_to_line for parity

If the FFI comparison is impractical (different calling conventions), at minimum
verify the pure-Simple parser returns sensible results independently.

PREREQUISITE: Agent A must have fixed bytes_to_u* externs.

You have advisor() access — call it before writing tests and before declaring done.
Commit: "test: add golden-file ELF+DWARF integration tests with FFI parity check"

IMPORTANT: Use jj for VCS. Never create branches. Work on main.
```

---

## Agent G: Phase 5 — `[u8]` Migration of ELF Inspect/Parser

**Wave:** 3 (after Wave 2 complete)
**Depends on:** All Wave 2 agents (round-trip tests validate the migration)

### File Scope (write)
- `src/compiler/70.backend/linker/elf_inspect.spl` — migrate from `[i64]` to `[u8]` + BinaryReader
- `src/compiler/70.backend/linker/elf_parser.spl` — migrate from `[i64]` to `[u8]` + BinaryReader
- `src/compiler/70.backend/linker/mold.spl` — remove `[u8] → [i64]` conversion in `mold_post_link_check`

### File Scope (read-only)
- `src/lib/nogc_sync_mut/binary_io.spl` — BinaryReader API
- `src/compiler/70.backend/linker/macho_inspect.spl` — reference `[u8]` pattern (already uses BinaryReader)
- `src/compiler/70.backend/linker/pe_inspect.spl` — reference `[u8]` pattern

### Acceptance Criteria
1. `elf_inspect.spl` uses `BinaryReader` instead of `elf_read_u*_le` helpers on `[i64]`
2. `elf_parser.spl` uses `BinaryReader` instead of raw `[i64]` byte arrays
3. `mold_post_link_check` no longer needs `[u8] → [i64]` conversion
4. All existing ELF-related tests still pass
5. Mach-O round-trip tests (Agent C) still pass
6. `bin/simple build` succeeds
7. `bin/simple test` passes (all tests)
8. `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` succeeds

### Commit
Two commits:
1. `refactor: migrate elf_inspect + elf_parser from [i64] to [u8] + BinaryReader`
2. `refactor: remove [u8]→[i64] conversion in mold_post_link_check`

### Agent Prompt (copy-paste)
```
You are migrating the ELF inspect and parser modules from [i64]-based byte
arrays to [u8] + BinaryReader, matching the pattern already used by the
Mach-O and PE parsers.

Files to modify:
  src/compiler/70.backend/linker/elf_inspect.spl — currently uses [i64], elf_read_u*_le
  src/compiler/70.backend/linker/elf_parser.spl — currently uses [i64], elf_read_u*_le
  src/compiler/70.backend/linker/mold.spl — has [u8]→[i64] conversion in mold_post_link_check

Reference patterns (already using [u8] + BinaryReader):
  src/compiler/70.backend/linker/macho_inspect.spl
  src/compiler/70.backend/linker/pe_inspect.spl
  src/lib/nogc_sync_mut/binary_io.spl — BinaryReader API

Migration strategy:
1. Replace elf_read_u16_le/u32_le/u64_le with BinaryReader calls
2. Change function signatures from [i64] to [u8]
3. Update all callers (grep for imports from elf_inspect/elf_parser)
4. Remove the [u8]→[i64] conversion in mold.spl's mold_post_link_check

This is a refactor — behavior must be identical. Run the full test suite and
bootstrap to verify nothing breaks.

After implementing:
  1. bin/simple build lint
  2. bin/simple test (all tests pass)
  3. scripts/bootstrap/bootstrap-from-scratch.sh --deploy

You have advisor() access — call it before writing code and before declaring done.
Commits:
  1. "refactor: migrate elf_inspect + elf_parser from [i64] to [u8] + BinaryReader"
  2. "refactor: remove [u8]→[i64] conversion in mold_post_link_check"

IMPORTANT: Use jj for VCS. Never create branches. Work on main.
IMPORTANT: This is a LARGE refactor touching core linker code. Test thoroughly.
```

---

## Orchestration Notes

### Parallel Execution Rules
- **Wave 1:** Launch Agents A and B simultaneously. They have **zero file overlap**.
- **Wave 2:** Launch Agents C, D, E, F simultaneously ONLY after Agent A confirms "bytes_to_u* externs registered and tests pass" **AND** has run `bootstrap-from-scratch.sh --deploy` (hard gate — without deploy, the running binary still lacks the externs). They have disjoint test file scopes.
- **Wave 3:** Launch Agent G ONLY after all Wave 2 agents complete and their tests pass.

### File Collision Matrix
| | A | B | C | D | E | F | G |
|---|---|---|---|---|---|---|---|
| **A** | — | safe | — | — | — | — | — |
| **B** | safe | — | — | — | — | — | — |
| **C** | — | — | — | safe | safe | safe | — |
| **D** | — | — | safe | — | safe | safe | — |
| **E** | — | safe | safe | safe | — | safe | — |
| **F** | — | — | safe | safe | safe | — | — |
| **G** | — | — | — | — | — | — | — |

### Commit Cadence
Each agent makes **at most 2 commits**. Orchestrator verifies `bin/simple test` after each wave before launching the next.

### Sub-Agent Memory
All agents should be reminded:
- They have `advisor()` access
- Use `jj commit -m "msg"` not `git commit`
- Never create branches
- Read bug docs before implementing fixes
- Run `bin/simple test` before declaring done (interpreter mode only — `--mode=native`/`--mode=smf` give false greens due to stub-generation no-ops)
- After adding new externs, run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (not `bin/simple build bootstrap`)
