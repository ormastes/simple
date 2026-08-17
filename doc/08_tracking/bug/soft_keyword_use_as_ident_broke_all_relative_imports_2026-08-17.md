# `use` added to the soft-keyword-as-identifier list broke EVERY relative import (200 sites), taking `bin/simple test` down at HEAD

- **Filed:** 2026-08-17
- **Severity:** HIGH — `bin/simple test` fails to load its module graph on ANY
  spec, including specs that touch nothing related. Not a wrong answer: a hard
  parse error at module load.
- **Status:** FIXED 2026-08-17 (same day it landed)
- **Component:** `src/compiler_rust/parser` (bootstrap seed)
- **Introduced by:** `3c4e6551b7a` *fix(parser): 11 soft keywords could not be
  used as identifiers*

## Symptom

Three lines are enough:

```simple
# m.spl
use .vhdl.b.{VhdlBuilder}
fn main():
    print("ok")
```

```
$ SIMPLE_RUST_SEED_WARNING=0 <seed built at HEAD> run m.spl
error: compile failed: parse: in "m.spl": Unexpected token: expected identifier, found LBrace
rc=1
```

The same file on the previously deployed seed (built 2026-08-16 22:59) prints
`ok`, rc=0. That before/after pair is the whole diagnosis.

## Why it looked like something else

The first visible symptom was not this file at all — it was **every**
`bin/simple test <spec>` run dying with:

```
error: compile failed: parse: in ".../src/compiler/70.backend/backend/vhdl_backend.spl":
Unexpected token: expected identifier, found LBrace
```

`vhdl_backend.spl` is in the test runner's transitive module graph and has 9
relative imports, so an untouched, unrelated spec
(`test/01_unit/lib/std/shell/path_spec.spl`) failed identically. That makes the
regression look like it belongs to whatever lane is currently editing — it does
not. Confirm by binary, not by file: run the 3-line repro above.

## Root cause

`src/compiler_rust/parser/src/parser_impl/core.rs`, the `soft_kw_stmt_as_ident`
predicate added by `3c4e6551b7a`:

```rust
let soft_kw_stmt_as_ident = matches!(
    &self.current.kind,
    TokenKind::Skip | TokenKind::Bind | TokenKind::On | TokenKind::With
        | TokenKind::Use | TokenKind::Export | TokenKind::Requires
        | TokenKind::Auto | TokenKind::Mod | TokenKind::Examples | TokenKind::AndThen
) && (self.peek_is(&TokenKind::Assign) || self.peek_is(&TokenKind::Dot));
```

Its stated rule — "`<kw> = …` / `<kw>.field` at statement level is a use of that
variable, never the statement form" — is true for the other ten keywords and
**false for `use`**. `use .mod.X` and `use ..parent.X` are Simple's relative
imports, so `Use` followed by `Dot` is precisely the statement form. The
predicate therefore rerouted every relative import into expression parsing,
which reached `expect_method_name()` and rejected the `{` of the import's brace
group.

Blast radius, measured: `grep -rn "^use \." --include=*.spl src/ | wc -l` -> **200**.

## Fix

Split `Use` out of the `.`-peek half; it qualifies as an identifier only on
`Assign`, so `use = x` still works while `use .x.{Y}` parses as an import
again. `export`/`mod` have zero `.`-leading occurrences in the tree and were
left as they were.

## Verification status

- **Parser crate, GREEN:** `cargo test --release -p simple-parser --test
  relative_import_not_soft_keyword_ident` ->
  `test result: ok. 7 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out`
  (`src/compiler_rust/parser/tests/relative_import_not_soft_keyword_ident.rs`).
  Covers both directions: the four relative-import shapes plus the absolute
  form, AND the concessions the introducing commit wanted (`var use = 3; use =
  use + 1`, `export.field`, `mod.field`).
- **Full-binary re-verification NOT completed.** The `cargo build --release
  --bin simple` re-run was starved out on this shared host (17 concurrent
  processes on the same target dir; no log progress for 90 minutes) and was
  left running. The RED half of the end-to-end evidence IS recorded above
  (3-line repro, stale binary rc=0 vs HEAD-built binary rc=1). What is missing
  is only the matching GREEN on a binary carrying this fix. Next session:
  rebuild and re-run the 3-line repro plus any `bin/simple test <spec>`.

## How this got through

The introducing commit's own message says it:

> Scope note: ... **No .spl-level or full-binary verification — `--bin simple`
> was not built.**

Its `cargo test -p simple-parser` fixtures all passed, because they exercise
the eleven keywords in variable position and none of them parses a relative
import. A `--bin simple` build plus any single `.spl` file containing
`use .x.y` would have caught it immediately.

Lesson worth keeping: a parser change that widens *which token starts an
expression* narrows *which token starts a statement*, and the fixtures for the
first half cannot see the second half. Pair such a change with at least one
end-to-end `.spl` parse.
