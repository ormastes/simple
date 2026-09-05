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
