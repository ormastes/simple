# `compile` parse diagnostics carry a filename but no line/column, forcing bisection to locate a defect

**Date:** 2026-08-17
**Status:** **FIXED 2026-08-17**
**Severity:** MEDIUM — does not break a build, but makes every parse failure in
a large file expensive to localise, and makes automated sweeps unable to report
a site
**Found by:** `src/lib/**` parse sweep (7780 files), while triaging six root
parse failures
**Binary:** `/mnt/data/cgtw2/release/simple` (freshly built Rust seed)

## Symptom

Every parse diagnostic on the `compile` path names the file twice and gives no
position within it:

```
$ /mnt/data/cgtw2/release/simple compile --emit-ast=/dev/null loc.spl
error: compile failed (…/loc.spl): parse: in "…/loc.spl": Unexpected token: expected expression, found Plus
```

There is no `line:col`, no source excerpt, and no caret — only the token kind.
Observed identically for three unrelated parse errors encountered in the sweep:

- `Unexpected token: expected expression, found Plus`
- `Unexpected token: expected expression, found Else`
- `val binding: refutable pattern in a val binding requires an `else:` clause
  that diverges (return/break/continue); use `if val ... = e:` to bind
  conditionally instead`

The last one is the worst case: it names no token at all, so in a 606-line file
there is nothing to grep for beyond guessing the construct.

## Why this matters concretely

Locating the two parser defects filed today
(`parser_same_indent_leading_operator_continuation_2026-08-17.md`,
`parser_block_if_expr_trailing_inline_else_2026-08-17.md`) required
**bisecting by prefix truncation** — compiling `head -n N file.spl` for every N
and finding the smallest prefix that reproduced the message. That is ~600
compiler invocations per file to recover information the parser already had.

The four source defects fixed today were located by grepping for the `val
Some(` pattern, which only worked because the construct was greppable.

## Note on the warning path

Warnings on the same run DO carry full location and a caret:

```
warning: Avoid 'export use *' - exposes unnecessary interfaces
  --> …/src/lib/gc_sync_mut/web_framework/persistence.spl:3:1
   |
  3 | export use std.gc_async_mut.web_framework.persistence.*
   | ^
```

So the renderer exists and is wired for warnings; the parse-error path is not
routed through it.

## Relationship to existing records

`simple_check_diagnostics_contract_raw_parser_error_not_stable_format_2026-07-20.md`
covers a different thing: the `check` command emitting a raw
`[parser_error] line L:C: …` format instead of the stable `error[Exxxx]` format.
Note that that raw format **does** include `line L:C`. This row is about the
`compile` path having no position information at all, in any format. (The `check`
path could not be cross-checked on this binary — `check` on the repo fails first
with an unrelated `semantic: undefined field 'log_mode'`.)

## Expected

A parse diagnostic reports `path:line:col` and, ideally, the same excerpt+caret
rendering the warning path already uses.

## Fix 2026-08-17 — the renderer now emits `path:line:col` + excerpt + caret

The parser was never missing the information; only the message text dropped it.
`ParseError` already carried a `Span { start, end, line, column }` and a
`span()` accessor. Two changes:

1. `src/compiler_rust/parser/src/error.rs` — added `ParseError::line_col()`,
   which prefers the span's real source coordinates and falls back to the
   variants that carry `line`/`column` directly (`SyntaxError`,
   `InvalidIndentation`). Returns `None` only for errors that genuinely have no
   position, so the caller degrades to the old message rather than printing a
   fabricated `0:0`.
2. `src/compiler_rust/compiler/src/pipeline/module_loader.rs` — added
   `render_parse_error(path, source, err)` and routed all **three**
   `CompileError::Parse(format!("in {:?}: {e}", path))` sites (previously lines
   1970 / 2022 / 2214) through it. It renders the same excerpt+caret shape the
   warning path already used.

### Evidence (A/B, same tree, both arms verbatim)

Fixture `loc.spl`:

```
fn f() -> int:
    val a = 1
    val b = + a
    b
```

Before — deployed `bin/simple` = `bin/release/x86_64-unknown-linux-gnu/simple`,
59537240 bytes, 2026-08-17 12:58:51:

```
$ bin/simple compile loc.spl --emit-ast=/dev/null -o /dev/null
rc=1
error: compile failed (…/loc.spl): parse: in "…/loc.spl": Unexpected token: expected expression, found Plus
```

After — `/mnt/data/cargo-target-sweep/release/simple`, 59570248 bytes,
built from this change:

```
$ /mnt/data/cargo-target-sweep/release/simple compile loc.spl --emit-ast=/dev/null -o /dev/null
rc=1
error: compile failed (…/loc.spl): parse: in "…/loc.spl": Unexpected token: expected expression, found Plus
  --> …/loc.spl:3:13
  |
3 |     val b = + a
  |             ^
```

### It paid for itself in the same session

The record's own complaint was that locating a defect cost "~600 compiler
invocations per file" of prefix bisection. All **nine** parse defects fixed
under `unparseable_spl_files_on_origin_main_sweep_2026-08-17.md` were located
with **one** invocation each, straight from the caret — including the two the
old message made hardest, the position-free
`expected expression, found Dedent` cases in
`formal_delivery_gates.spl` and `replay_runner.spl`.

Status: FIXED.
