# RETRACTED — see jit_option_i64_value3_reads_as_none_2026-07-24.md

**Date:** 2026-07-24

This report's original conclusion — that `Type(field: self.field)` in a named
argument was a *parse regression* breaking specs — is **wrong**. The `self.field`
"self is implicit" message is a harmless **Info-level style hint** that neither
aborts parsing nor breaks the test runner (specs with 2, 20, and 50 `self.field`
uses all pass under `simple test`).

The real root cause is a **JIT tag-box encoding bug**: an `Option<i64>` holding
the value `3` reads as `None`. `index_of` returns the match offset as
`Option<i64>`, so a `"10 examples, 0 failures"` summary (where `"example"` is at
byte offset 3) becomes `None` → the test-runner cannot parse the count → false
FAIL for any spec with **10–99 examples**.

Full analysis, minimal repro, JIT-vs-interpreter proof, and fix direction:
**`jit_option_i64_value3_reads_as_none_2026-07-24.md`**.
