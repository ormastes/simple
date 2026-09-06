# `bin/simple lint` cannot lint `test/01_unit/compiler/codegen/` specs: internal string-index error on one file, SIGSEGV on its neighbour (2026-09-06)

- **Status:** OPEN — filed rather than worked around; no lint verdict was obtainable for a new spec in this directory.
- **Severity:** medium — not a wrong-value defect, but the linter is the gate for `.spl` changes and it produces no usable verdict here, so lint coverage for this directory is silently zero.
- **Class:** tooling / linter internal error.
- **Host:** aarch64 Linux, `bin/simple` -> `bin/release/aarch64-unknown-linux-gnu/simple` (Rust bootstrap seed, `--version` prints the seed banner).

## What was observed

Two files in the SAME directory, both valid (`bin/simple test` runs both to a
green `Results:` line), fail the linter two different ways.

1. A newly added spec — `test/01_unit/compiler/codegen/pure_simple_cond_optional_presence_lowering_spec.spl`
   (13,125 bytes on disk):

```
$ sh scripts/check/lint-cached.shs test/01_unit/compiler/codegen/pure_simple_cond_optional_presence_lowering_spec.spl
error: semantic: string index out of bounds: index is 13083 but length is 13083 (preview="# Purpose and audience: executable specification evidence fo")
FAIL — 1 file(s) checked, 1 with findings
```

   The index equals the length, which is the classic off-by-one at end of
   input. It is NOT the file size (13,125), so the subject is some internal
   buffer, not the raw file. The `preview=` field shows the buffer is this
   file's own text. The file ends with a single `\n` and has no unusual bytes.

2. A pre-existing, untouched sibling —
   `test/01_unit/compiler/codegen/condition_tag_decode_spec.spl`:

```
$ sh scripts/check/lint-cached.shs test/01_unit/compiler/codegen/condition_tag_decode_spec.spl
Segmentation fault (core dumped)
FAIL — 1 file(s) checked, 1 with findings
```

## Why this is filed and not normalised

`CLAUDE.md`: "When a short, safe grammar or compact expression form fails,
compiles too slowly, or forces a workaround, fix it or record a concrete
bug/feature request instead of silently normalizing the workaround." The
tempting workaround — shuffle the new spec's text until the index error stops —
would hide a real end-of-input bug and would do nothing for the SIGSEGV on the
neighbouring file, which no edit of mine could cause.

Both files are accepted by the compiler proper: `bin/simple test` reports
`Results: 7 total, 7 passed, 0 failed` for the first. So this is a linter-only
failure, not invalid source.

## Note on the wrapper's verdict line

`lint-cached.shs` reported `FAIL — 1 file(s) checked, 1 with findings` for the
SIGSEGV case. A crash is not a finding; classifying it as one makes a dead
linter indistinguishable from a lint violation in any log that only reads the
verdict. Worth a separate three-way classification (findings / crash / clean),
mirroring the SKIP-vs-FAIL distinction `check-c-runtime-compiles-push.shs`
already makes for missing headers.

## Next steps

- Reproduce the off-by-one under a debug build and locate the `index == length`
  read (likely a lexer/one-char-lookahead at EOF).
- Get a backtrace for the SIGSEGV on `condition_tag_decode_spec.spl`; it may or
  may not be the same root cause.
- Until then, `.spl` additions under `test/01_unit/compiler/codegen/` cannot be
  lint-verified; say so rather than claiming a clean lint.
