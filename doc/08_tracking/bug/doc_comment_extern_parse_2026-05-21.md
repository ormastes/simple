## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: Resolved 2026-05-29

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Blank doc comment before extern parse failure

Date: 2026-05-21

Status: Resolved 2026-05-29

## Summary

`bin/simple check` reports `unexpected token` / `expected: expression` at EOF when a blank `///` doc-comment line appears in a doc-comment block immediately before an `extern fn`.

## Repro

```spl
/// a
///
/// b
extern fn f(len: i64) -> [f64]
```

Observed:

```text
error[E0002]: unexpected token
  expected: expression
  found:    Eof
```

## Impact

This blocked `bin/simple check src/lib/common/science_math/perf_sugar.spl` and contributed to the broader `bin/simple check src/lib` smoke failure.

## Workaround Applied

Removed the blank `///` line in `src/lib/common/science_math/perf_sugar.spl`. The file now checks cleanly.

## Follow-up

Resolved in the Rust seed lexer/parser by treating a bare `///` between adjacent
line-style doc comments as an empty doc-comment separator instead of the opener
for a `/// ... ///` block.

Verification:

- `cargo fmt -p simple-parser`
- `cargo test -p simple-parser --lib lexer::tests -- --nocapture`
- `cargo test -p simple-parser --test declaration_tests -- --nocapture`
