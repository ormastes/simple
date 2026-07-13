# Bug: single-line `while COND: STMT` not supported ("expected Newline, found Identifier")

**ID:** parser_web_renderer_expected_newline_found_identifier_2026-07-13
**Filed:** 2026-07-13
**Status:** WORKED AROUND (source rewritten to block form); parser gap NOT fixed
**Severity:** P2 — load-path parse failure blocking a showcase app
**Component:** compiler frontend / parser (both deployed self-hosted `bin/simple`
and the fresh seed reject the same input)

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

Unlike `if COND: STMT`, which the parser accepts as a single-line inline-body
form, `while COND: STMT` is NOT supported at all — regardless of what `STMT`
is (assignment, `break`, function call). Minimal isolated repro (fails to
parse with the exact same error):
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

## Fix applied

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

## Requested fix

Either support single-line `while COND: STMT` symmetrically with `if COND:
STMT`, or emit a targeted diagnostic ("single-line while bodies are not
supported; use an indented block") instead of the generic "expected Newline,
found Identifier" token error, which gives no hint about the actual
construct at fault.

## Verification

Harness (`use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.*`
then `print("ok")`) now loads and prints `ok` on both `bin/simple` and the
fresh seed `src/compiler_rust/target/bootstrap/simple`.
