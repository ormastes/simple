# `name =` with the RHS on the next line does not parse — took a whole example file down silently

- **ID:** assign_rhs_newline_continuation_parse_2026-07-25
- **Status:** OPEN — occurrences in `examples/06_io/ui/web_render_file_gui.spl` repaired;
  the underlying grammar/diagnostic gap is NOT fixed
- **Severity:** high — the failure is whole-file (nothing in the module loads) and the
  diagnostic names no line, so the cost to locate it is a manual bisect

## Symptom

```
error: compile failed: parse: in ".../examples/06_io/ui/web_render_file_gui.spl":
Unexpected token: expected expression, found Newline
```

No line, no column, no caret. The file is 548 lines; locating the offending token
required bisecting by prefix truncation (`head -n N` + parse) — 20+ compiler
invocations.

## Cause

An assignment whose right-hand side starts on the following line:

```
current_font_pixel_size =
    updated_result.vector_font_pixel_size
```

Simple only continues an expression across lines inside parentheses — the same file
does this correctly a few lines later (`if ((gpu_requested and` ...). A bare trailing
`=` is not a continuation, so the parser reaches a Newline where it wants an
expression and aborts the module.

There were **10** such splits, lines 471-491, all introduced together as
column-width wrapping.

## Impact observed

`examples/06_io/ui/web_standards_showcase_gui.spl:14` does
`use web_render_file_gui.{run_web_standards_showcase, ...}`, so the unparseable
module took the entire web-standards showcase child down with it. The `web × host-WM`
showcase-matrix cell could therefore never produce a frame — the child died at parse
before rendering anything. This was masked because the parent wrapper's own failure
surfaced only as a generic example-watchdog timeout.

## Why it was not caught

Nothing parses `examples/**` in CI. The file was committed in this state; `bin/simple
lint` on it exits non-zero but does not print the parse error, so lint gave no signal
either.

## Fix direction (pick deliberately — none of these are done)

1. **Point at the token.** The parse error must carry file:line:col + caret, like the
   other diagnostics do. This alone turns a multi-hour bisect into a 5-second read,
   and is the highest-value change here.
2. **Make `lint` report parse errors.** `bin/simple lint <file>` currently exits 1 on
   an unparseable file while printing only unrelated style info. A linter that cannot
   say "this does not parse" fails at its first job.
3. **Parse-gate `examples/**`** in CI so an unparseable example cannot land.
4. *Optional, separate decision:* support a trailing-`=` line continuation. This is a
   language change, not a bug fix — the parenthesised form already works and is used
   elsewhere in the same file. Recorded here only so the choice is explicit rather
   than assumed; items 1-3 are worth doing regardless.

## Related

Same day, same class of "silent wrong thing, no diagnostic":
`doc/08_tracking/bug/env_get_nil_coalesce_dead_fallback_2026-07-25.md` (`??` applied
to a non-optional is provably dead code and warns about nothing).
