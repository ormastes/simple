# `[] of text` is not Simple grammar but fails with "function `of` not found"

**Filed:** 2026-08-31 · **Status:** OPEN (diagnostic quality)
**Severity:** low — but the diagnostic is useless and the form looks plausible.

`val xs = [] of text` (seen in `test/*/sffi/sffi_public_api_spec.spl`, now
fixed to `val xs: [text] = []`) is not a grammar form: `of` is not a keyword
(`parser/src/lexer/identifiers.rs`), so the parser treats `of text` as a call
to a function named `of`, and the user sees
`semantic: function `of` not found` — nothing points at the array literal.

Wanted: either support the form or emit a targeted parse-time diagnostic
("`of` is not a type ascription; write `val xs: [text] = []`").
