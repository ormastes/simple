# `lexer_next_token` hardcodes `span.start = 0` — every outline token span is degenerate

Filed 2026-08-23. Status: **open.** Independent of, but discovered during, the
outline parse spin (`outline_authority_parse_spin_treesitter_2026-08-23.md`).

## The defect

`src/compiler/10.frontend/core/lexer.spl:85-92`

```
fn lexer_next_token(self: Lexer) -> Token:
    # Advance the global lexer and build a Token record.
    val kind: i64 = lex_next()
    val text = lex_token_text()
    val line = lex_token_line()
    val col = lex_token_col()
    val span = lex_span_new(0, text.len(), line, col)   # <-- start is ALWAYS 0
    Token(kind: kind, span: span, text: text)
```

The first argument to `lex_span_new` is the span START OFFSET. It is the
literal `0` for every token the function ever produces. `end` is `text.len()`,
so a span is not merely mis-based — it is `0..len(text)` for every token,
i.e. every token claims to begin at byte 0 of the file.

`line` and `col` ARE real, which is what makes this hard to notice: any
diagnostic that renders line/col looks correct while the byte offsets underneath
are meaningless.

`lex_next_token_record()` (same file, ~:514) builds its span the same way and
has the same defect.

## Why it matters

1. **It silently defeats `frontend_strip_outline_authority_spans`**
   (`frontend.spl:79-91`), whose whole contract is byte-offset arithmetic:
   ```
   for span in authority_spans:
       if span.start < copied_until or span.start < 0 or
          span.end_pos < span.start or span.end_pos > source.len():
           continue
   ```
   With every `start` equal to 0, the `span.start < copied_until` test discards
   every span after the first. The stripping pass cannot work as written, and
   fails **silently** — it `continue`s rather than reporting anything.

2. **It is a landmine for the next investigator.** This cost real time in this
   very session. A probe was written against `self.current.span.start` to answer
   "is the parser's cursor advancing?" — the only question that mattered — and
   it reported `start=0` on every iteration. That reading is consistent with two
   completely different worlds:
   - the cursor is genuinely stuck (what it looked like), and
   - the cursor is advancing perfectly well and **spans are simply degenerate**.

   The probe cannot distinguish them, so it is worthless for the purpose, and a
   progress guard written against `span.start` is not just useless but
   **actively wrong** — it compares `0 == 0` every iteration and fires
   unconditionally, injecting a spurious extra `advance()` into a working
   parser. One such guard was written and reverted here. The sound probe was
   `self.current.kind` plus `span.line`, which immediately gave the answer
   (`kind=190` constant — see the companion record).

   This is the same shape as the `file_read` infinite-recursion landmine
   recorded on 2026-08-23: a primitive that looks authoritative, is trusted by
   instrumentation, and quietly invalidates the measurement rather than failing.

3. Any future diagnostic, span-based cache key, source-map, or IDE feature that
   trusts these offsets inherits the defect.

## Scope

`lexer_next_token`'s only callers are `outline_lexer.spl:127` and `:140` (both
inside `treesitter_advance`), so today the blast radius is the treesitter
outline parser. That is *why* it has survived: the main parser uses
`core_lexer_next_token(lexer) -> (CoreLexer, i64)` and threads its own state.
The narrow blast radius is not a reason to leave it — it is the reason it was
never noticed.

## Fix sketch (not applied)

`lex_next()` already maintains a real position (`SIMPLE_BOOTSTRAP_LEX_POS`,
see `current_core_lexer_reset_file`). Plumb the token's true start offset out
of the CoreLexer alongside `line`/`col` — there are already
`lex_token_line()` / `lex_token_col()` accessors, so a `lex_token_start()`
accessor is the symmetric addition — and pass it to `lex_span_new` instead of
`0`. Then re-check `frontend_strip_outline_authority_spans`, which has never
run against non-degenerate spans and is therefore **unverified**, not merely
unused.

Until then: **do not trust `Token.span.start` from this path, and do not build
instrumentation on it.**
