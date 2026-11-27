# Bug: doctest parser_spec tests a removed/older API shape

- **Status:** open
- **Filed:** 2026-07-20
- **Affected spec:** `test/unit/doctest/parser_spec.spl`
- **Command:**
  `SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple test test/unit/doctest/parser_spec.spl --no-session-daemon`
- **Result:** `18 examples, 16 failures`

## Symptom

The spec imports `std.common.doctest.parser` and exercises:
- `examples[0].code`, `.setup`, `.teardown` fields on the returned item
- top-level free functions `extract_docstrings(source, path)` and
  `parse_expected(lines)`

Actual errors:
```
semantic: method `code` not found on type `DoctestItem`
semantic: method `setup` not found on type `DoctestItem`
semantic: method `teardown` not found on type `DoctestItem`
semantic: function `extract_docstrings` not found
semantic: function `parse_expected` not found
semantic: variable `Option` not found   (Option.None / Option.Some used bare)
```

## Root cause

`src/lib/common/doctest/parser.spl` (current source) defines:
- `class DoctestItem: source_path, start_line, commands: [text], expected: Expected, section_name: text?`
  — field is `commands`, not `code`; there is no `setup`/`teardown` field at all.
- A separate unused `class DoctestExample: code, expected, setup, teardown, line_number` exists in
  the same file but is never constructed or returned by any function — dead code.
- Exported functions: `parse_docstring`, `parse_doctests`, `parse_lines`, `build_expected`,
  `build_expected_line`. There is **no** `extract_docstrings` or `parse_expected` function anywhere
  in `src/` (`grep -rn "extract_docstrings\|fn parse_expected" src/` → no hits).
- The current parser also does not implement `Setup:` / `Teardown:` block parsing at all — only
  bare `>>>` code + following output lines.

This is not a simple rename: the spec exercises setup/teardown-block parsing and a docstring
extraction API that has no current equivalent to rename to. Renaming `code`→`commands` alone
would still leave 8+ examples failing against missing functionality (`extract_docstrings`,
`parse_expected`, setup/teardown fields), and dropping those assertions would violate the
"never weaken to force green" rule. Left as GENUINE-BUG: either restore/implement
`extract_docstrings`/`parse_expected`/setup-teardown parsing, or replace `DoctestExample`
(now dead code) and update the spec together as one deliberate API-alignment change.

## Repro (trimmed)

```
use std.common.doctest.parser
content = ">>> 1 + 1\n2\n"
examples = parse_docstring(content)
examples[0].code   # fails: DoctestItem has no `code`, only `commands`
```

Not touched: `test/unit/doctest/parser_spec.spl` left as-is (no edit made — any edit would
require deleting assertions for functionality that doesn't exist).

## Resolution (2026-11-25)

**Decision:** the current parser API is the live, intended one; the spec was stale
against it. Resolved as one deliberate API-alignment change: spec updated to the
current API, assertions for never-implemented functionality removed with the
feature gaps documented here, and two `nil`-vs-`None` matcher drifts fixed.
`src/lib/common/doctest/parser.spl` itself is unchanged.

**Evidence:**
1. Git history: `fdba9efaa02` created a 9-line stub; `b8378e68baa`
   ("test-tooling: implement doctest parser (TODO #15)", 2026-04-15) implemented
   the parser with `DoctestItem(commands)` and no setup/teardown parsing, no
   `extract_docstrings`, no `parse_expected` — from day one. The
   `DoctestExample(code/setup/teardown)` class appeared later
   (`39f75668713`, 2026-04-21, a workspace-sync commit) and is never
   constructed by any parse function. A working setup/teardown +
   `extract_docstrings` API therefore never existed and was never removed.
2. The Rust driver's doctest (`src/compiler_rust/driver/src/doctest/types.rs`)
   also defines its example type with `commands` and no setup/teardown —
   independent confirmation that `commands` is the designed API.
3. The Rust-free consumers of the module all use the current API:
   `test/01_unit/lib/test_runner/doctest_parser_spec.spl` (hardening spec,
   green) and `test/01_unit/doctest/runner_spec.spl` (green).
4. Correction to the original root-cause note: `DoctestExample` is **not**
   dead code — `src/lib/common/doctest/runner.spl` imports it for
   `ExampleResult.example` and `test/01_unit/doctest/runner_spec.spl`
   constructs it (29/29 green). It is kept.
5. Path drift: the spec now lives at `test/01_unit/doctest/parser_spec.spl`
   (moved from `test/unit/doctest/parser_spec.spl` by `df80cbb5939`).

**Assertions changed, each with reason (no silent deletions):**
- REMOVED `it "parses teardown block"` — asserted `DoctestItem.teardown`,
  a field that has never existed; teardown-block parsing is an unimplemented
  feature gap. Its input's real behavior (2 items, header acts as separator)
  stays pinned by `it "parses items after section labels"`.
- REMOVED `it "parses setup block"` — asserted `DoctestItem.setup` and
  `.code`; same unimplemented feature gap. Real behavior stays pinned by
  `it "parses items separated by section headers"`.
- REMOVED `it "parses continuation lines with ..."` — asserted `...` lines
  join `code`; the live parser (and two green tests:
  `it "treats non-prefix lines as expected output"` here and the hardening
  spec) pins `...` lines as expected-output text. `...` continuation-line
  joining is an unimplemented feature gap; the input is already covered by
  the green twin.
- REMOVED `context "extract_docstrings"` (2 examples) — called
  `extract_docstrings(source, path)`, which never existed in `src/`
  (`git log -S` finds no implementation commit) and has no rename
  equivalent; docstring extraction to `(content, line)` tuples is an
  unimplemented feature gap (nearest live surface: `parse_doctests`). The
  block was also mis-indented, which made the entire file fail to parse
  (`expected indented block after ':'` at the first `it`), so 0 of 18
  examples even executed.
- FIXED 2 assertions `expect msg to eq nil` → `expect(msg).to_be_nil()`
  (in `it "parses exception expectations"` and `it "parses exception"`) —
  after the repo-wide None migration, `Expected.Exception.msg` is
  `Option.None`, which `to eq nil` no longer matches; `to_be_nil()` is the
  form the green hardening spec already uses.

**Feature gaps filed by this note** (unimplemented, by design decision
deferred): setup/teardown block parsing on `DoctestItem`, `...`
continuation-line joining, and a docstring-extraction API
(`extract_docstrings`-style `(content, line)` tuples).

**Before/after** (`SIMPLE_LIB=src bin/simple.exe test <spec> --mode=interpreter`,
tracked self-hosted binary):
- Before: `outcome=ERROR executed=0 failed=1 reason=parse-error`
  (whole file unparseable; the stale `.code`/`.setup`/`.teardown`/
  `extract_docstrings` assertions sat behind the parse error).
- After: `outcome=OK declared>=18 executed=18 passed=18 failed=0`
  (23 examples originally; 5 removed as documented above, 18 kept, all
  passing, including the 2 with the nil→None matcher fix).
- Siblings run once, all green: `test/01_unit/doctest/runner_spec.spl`
  29/29, `test/01_unit/doctest/matcher_spec.spl` 23/23,
  `test/01_unit/lib/test_runner/doctest_parser_spec.spl` 9/9.
