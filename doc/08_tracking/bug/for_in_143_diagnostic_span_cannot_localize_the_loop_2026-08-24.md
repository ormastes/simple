# `#143` (and its neighbours) report spans that cannot localize the loop (2026-08-24)

- **Status:** OPEN — not fixed
- **Severity:** MEDIUM — no wrong answers, but it makes a blocking diagnostic
  unactionable and has cost two lanes a probe-and-rebuild cycle each
- **Area:** `50.mir/mir_lowering_stmts.spl` for-in lowering / HIR block spans
- **Found by:** localizing the 32 `#143` blockers on the MCP build

## What is wrong

`for-in over non-array iterables is not supported by native codegen yet (#143)`
is raised with `Some(body.span)`. Measured across all 32 occurrences in a
`native-build src/app/mcp/main.spl`:

- **22 of 32 carry an entirely empty span** — `file=` (empty string), `line=0`,
  `col=0`, `start=0`, `end=0`. The diagnostic names no file at all.
- **The other 10 name a file, but it is the RECEIVER's span, not the loop's.**
  For the `object_ops.spl` cluster every one reported `line: 14` while the actual
  `for-in` statements are at lines 88, 143, 200, 202, 223, 244, 265 and 287.

The driver prints these as `43:1`, `6:1` and similar, which read like source
line:column and are in fact MIR program points.

The net effect: the error cannot be localized from its own output. Both the
count (32) and the breakdown by iterable kind had to be recovered by patching a
`print` into the compiler and rebuilding — for information the diagnostic is
already trying to convey.

## Why it is worth fixing with `#143` rather than after

`#143` is a deliberate unimplemented-feature message, so every hit is something a
person must go and rewrite or wait for. A feature-gap diagnostic that cannot say
WHERE the gap was hit forces a compiler-instrumentation cycle per investigation.
Two lanes have now paid it.

A related trap: an earlier lane observed empty spans on this path and concluded
they were normal for it. They are normal in the sense of "reproducible", not in
the sense of "acceptable" — on the blocking sites they are the whole problem.

## NOT verified

- Where the span is lost was not investigated: it could be `HirBlock.span` never
  being populated for a for-body, or the for-in lowering choosing the wrong span
  to attach. Only the symptom was measured.
- Whether other diagnostics raised with a `body.span` in the same file have the
  same defect was not checked.
