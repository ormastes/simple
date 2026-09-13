# Unit specs that never parse — a whole file's examples vanish with one line of output

- Status: PARTIALLY FIXED (2026-09-13, continuation) — 43 spec files repaired, 1 still OPEN
- Binary: `/home/yoon/dev/cargo-fulltest/release/simple`, sha256 `4dfdf671742007d30210`
- Base: `origin/main` `f4cd1c306dd`

## Continuation update (2026-09-13, later session)

Two of the three previously-OPEN files bisected and fixed, same method
(`head -N` bisect, no line number in the lexer error):

- `test/01_unit/common/structural/transfer_object_handle_capability_registry_spec.spl`
  — NOT a parser bug. Line 15 read
  `target: ParallelExecutionDomain): TransferEnvelopeV1:` — a colon-style
  return type (`): Type:`), which is not, and per
  `doc/07_guide/quick_reference/syntax_quick_reference.md:42,658` never was,
  valid Simple syntax (the arrow form `-> Type:` is canonical). Minimal repro
  confirms even the single-line form `fn foo(a: i64, b: i64): i64:` fails
  identically — reproducible independent of the multi-line parameter list.
  Fixed to `-> TransferEnvelopeV1:`. The file now parses and fails cleanly on
  its real, more specific defect: `Module
  "std.common.structural.transfer" does not export
  'object_handle_capability_registry'` — that module does not exist anywhere
  in `src/lib/common/structural/transfer/` (only `transfer_codec.spl`,
  `transfer_contracts.spl`). Same "target module never existed" class as
  `module_surfaces_from_owners` in the sibling hir receipt — in-flight feature
  work for another lane, not reconstructed here.
- `test/01_unit/gpu/backend_acceleration_spec.spl` — the file's first three
  `it` blocks (lines 5-29) sat at 4-space indent with no enclosing `describe`,
  so the parser hit the dedent to `describe "Additional behavior oracles":`
  at column 0 as `Unexpected token: expected expression, found Indent`.
  `git log -p --follow` on the file shows a `describe "Executed behavior
  oracles":` header immediately preceding these exact `it` lines in an earlier
  revision; a later rewrite dropped the header but kept its body. Restored
  verbatim. RED: 0 examples, could not compile. GREEN: `3 examples, 0
  failures` (5 declared/executed counting the nested `Additional behavior
  oracles` and `Module Suite` groups too) — full pass, not merely parseable.

`test/01_unit/hardware/rv32i/rv32_sv32_walker_spec.spl` stays OPEN — its cause
is the separately-filed
`doc/08_tracking/bug/allow_reserved_as_hard_keyword_2026-09-13.md` (`allow` is
a hard keyword contrary to the lexer's own comment), not a spec typo, and that
fix was assessed as too invasive for this lane (`TokenKind::Allow` has 11
parser consumers, not a `≤ 40 line` change).

## Why this class matters more than its failure count suggests

A spec that fails to LEX produces no verdict for any of its examples. The
sweep prints one `FAIL ... Error: error: compile failed: parse: ...` line and
moves on, so a file holding 26 examples costs exactly as much visible red as a
file holding one. Every SHA-2 and SHA-3 known-answer-test file in
`test/01_unit/lib/common/crypto/` was in this state and nothing in the tree
said so.

Detector, authoritative and already available: the sweep's own
`compile failed: parse:` line. Confirm one file with
`bin/simple compile <spec> -o /tmp/x.smf`.

A static parity scan over `"""` was tried as a cheaper detector and is NOT
reliable — 53 candidates counting occurrences, 120 counting them with comment
lines skipped, and it both misses real cases (`ast_types_spec.spl` has an even
count and does not parse) and flags healthy ones (`tag_parsing_spec.spl`
mentions `"""` inside a `#` comment). Do not gate on it.

The lexer error text carries **no line number**, so locating the offending
line means compiling prefixes of the file (`head -N`) and bisecting.

## Shapes found, and the fix for each

1. **Truncated generated `step` title** — 85 sites in 33 files, plus 34 with a
   stray extra quote in 4 more. `step("hashes \")` where the `it` title was
   `it "hashes \"abc\" to the FIPS 180-4 section B.1 digest":` — the title was
   cut at its first escaped quote, so `\"` escapes the closing quote and the
   string runs to end of line: `Error("Unterminated f-string")`.
   Fixed by restoring each title verbatim from the `it` line above it.
2. **Markdown block with no docstring delimiters** — the `## Operator workflow`
   section sitting at module level as bare prose. The backtick in
   ``Run `bin/simple test ...` `` then opens an atom literal:
   `Error("Unclosed backtick atom literal")`. Fixed by wrapping in `"""`.
3. **Docstring whose OPENING `"""` was lost** — the remaining closer opens a
   string that swallows the rest of the file. Fixed by restoring the opener.
4. **A `fn` header overwritten by a `describe` line** —
   `lazy_outline_equivalence_spec.spl` lost
   `fn scan_outline(source: text) -> [text]:`, leaving a `describe` whose body
   is a function body. Restored. Two helpers that edit also deleted,
   `extract_decl_name` and `sort_names`, are NOT reconstructed here: writing
   them means authoring the oracle the spec tests against, which is the owning
   lane's call. The file now declares its 16 examples and fails all 16 on
   `function extract_decl_name not found` — visible, which it was not before.
5. **Stale import path** — `use test.unit.tool.kernel_plugin_schema.generated.*`
   for modules that live beside the spec. Fixed to the relative
   `use .generated.<module>` form.
6. **Non-export import** — `use std.io.file.read_text`; `std.io.file` exports
   only `FileHandle, File`. Fixed to `std.io_runtime.{file_read}`.

## Still OPEN — one file

The first two rows of the original three-file table above were fixed in the
continuation update; both were spec-side defects (a never-valid colon return
type, a dropped `describe` header), not parser bugs.

| spec | parse error |
|---|---|
| `test/01_unit/hardware/rv32i/rv32_sv32_walker_spec.spl` | `Unexpected token: expected pattern, found Allow` |

This one IS a language defect, not a spec typo: `Allow` reads like an enum
variant the parser is treating as a keyword in pattern position. Tracked
separately: `doc/08_tracking/bug/allow_reserved_as_hard_keyword_2026-09-13.md`.

## Coverage of this record

Only `test/01_unit` directories that were actually swept on 2026-09-13 are
covered — `lib/`, `compiler/`, `app/`, `os/` and `std/` were not run to
completion (10,706 spec files at 5-10 s each), so more instances of every shape
above almost certainly remain. The same two typo families were also observed
outside `test/01_unit`; they were counted, not touched.
