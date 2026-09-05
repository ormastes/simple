# Bug: single-line `while COND: STMT` not supported ("expected Newline, found Identifier")

**ID:** parser_web_renderer_expected_newline_found_identifier_2026-07-13
**Filed:** 2026-07-13
**Status:** Rust parser source fixed 2026-07-15; focused regression added,
execution pending
**Severity:** P2 — load-path parse failure blocking a showcase app
**Component:** compiler frontend / Rust seed parser. The pure-Simple parser was
already correct because its shared `parse_block()` accepts an inline statement
when no indent follows the colon.

## Symptom

Any module-load of
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
failed with:
```
error: compile failed: parse: in ".../simple_web_html_layout_renderer.spl": Unexpected token: expected Newline, found Identifier { name: "j", pattern: Immutable }
```
`bin/simple check <file>` does NOT reproduce this (the check lane tolerates
it); only the module-load path (`use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.*`)
triggers it.

## Root cause (bisected + minimal repro)

The Rust `parse_while_with_label` path unconditionally required `Newline` and
`Indent` after the colon, unlike the adjacent inline-capable `if` and `for`
paths. Minimal isolated repro (previously failed with the exact same error):
```simple
fn f() -> i64:
    var j = 0
    while j < 10: j = j + 1
    return j
```
```simple
fn f() -> i64:
    var j = 0
    while j < 10: break
    return j
```
The sibling form `if j < 10: j = j + 1` parses fine. So this is a distinct
gap from the cast/generic-misparse family documented in
`parser_sfnt_glyf_expected_comma_found_plus_2026-07-13.md` — no cast, no `<`
ambiguity, no `and`/`or` line continuation involved; the bare presence of a
single-line `while` body is the trigger.

## Source fix (2026-07-15)

The Rust while parser now preserves its existing newline/deferred-dedent/
invariant block path and uses the existing `parse_inline_or_block()` owner when
the token after `:` is not a newline. Inline bodies carry no loop invariants.
The focused AST regression parses `while x < 10: x = x + 1` and requires one
assignment in the resulting `WhileStmt` body.

## Workaround applied

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
`parse_font_shorthand_family` (the only occurrences in the file, all 6 within
this one function): rewrote each single-line `while COND: STMT` into
standard block form, e.g.:
```
-            while j < n and dec_val(s.char_at(j)) < 10: j = j + 1
+            while j < n and dec_val(s.char_at(j)) < 10:
+                j = j + 1
```
Semantics-preserving — same loop body, just indented onto its own line.
6 instances fixed (lines 1880, 1883, 1886, 1889, 1890, 1891 in the original
file).

The source workaround may remain: block form is explicit, equivalent, and
continues to exercise the unchanged block parser.

## Verification

The focused Rust parser regression and a standalone seed parse remain to be
run for this source change. No runtime PASS is claimed by this update.
