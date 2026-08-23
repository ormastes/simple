# Parse spin in the treesitter outline-authority path (phase 1 blocker)

Filed 2026-08-23. Status: **FIXED** (`treesitter_is_at_end`, `outline_lexer.spl`).

## Symptom

stage1 runs 21, 23 and 24 all hang in step 1/6 at `parse 144/688` (run23
`144/689`) on `src/compiler/10.frontend/treesitter_types.spl`. All 8 parse
shards burn 65-87% CPU each with **byte-identical RSS** across sampling
windows and **zero `rchar`+`wchar` delta** — a bounded-memory infinite loop,
not slow progress and not an I/O livelock. run24 froze at
`+439476ms dt=0ms`, log line count 5758 -> 5758 over 60 s.

## Root cause: an exit condition that can never be reached

`Token.kind` carries the **raw CoreLexer numeric kind**, not a `TokenKind`
ordinal. That numeric space is fixed by `core/lexer_types.spl`:

```
fn lex_token_eof(line: i64) -> Token:   return lex_token_new(190, "", line, 0)
fn lex_token_error(msg, line, col):     return lex_token_new(191, msg, line, col)
fn token_is_keyword(t: Token) -> bool:  return t.kind >= 20 and t.kind <= 59
```

So EOF is **190**. `lex_next()` also returns 190 when it fails closed on a dead
lexer.

`TokenKind`, by contrast, is a **bare positional enum** in
`10.frontend/lexer_types.spl` — 142 variants, no explicit discriminants (the
`=` characters in it are inside `# ==` comments), so its ordinals span only
`0..141` and `Eof` sits at **133**. The raw value 190 is therefore
**unreachable by any `TokenKind` ordinal**.

`treesitter_is_at_end` compared the two spaces directly:

```
fn treesitter_is_at_end(self: TreeSitter) -> bool:
    val kind = self.current.kind
    kind == TokenKind.Eof          # 190 == 133 -- never true
```

It could never return true. `outline.spl`'s top-level loop
(`while not self.treesitter_is_at_end():`) therefore had an exit condition
that could never be reached, and `treesitter_synchronize`'s inner
`while not self.treesitter_is_at_end():` had the same. Zero allocation, zero
I/O, pure CPU — exactly the measured signature.

**Direct evidence.** Instrumenting the loop with a SOUND probe
(`self.current.kind`, not `span.start` — see the landmine below) gave
`kind=190 line=1 col=0` on every one of 29 consecutive iterations: the parser
was sitting on EOF, correctly lexed, and simply not recognising it.

## The fix

`src/compiler/10.frontend/treesitter/outline_lexer.spl`, `treesitter_is_at_end`:

```
kind == 190 or kind == TokenKind.Eof
```

Testing the raw value is what makes the loop terminable. The `TokenKind`
comparison is kept alongside it so a Token that does carry an ordinal is still
recognised. The change is **strictly additive**: it can neither make a
previously-terminating parse spin, nor cause a token to be skipped — which is
the failure mode that would turn a hang into a silent wrong parse.

Post-fix the file parses to completion in **~3.8 s** with **0 parse errors**,
and the shard proceeds to the rest of its closure.

## Trigger: a substring, not the module count

`frontend.spl:76`
```
fn frontend_has_outline_authority(source: text) -> bool:
    source.contains("friend ") or source.contains("internal_export")
```
Any file containing either substring **anywhere** — including in a struct field
name or a comment — takes the outline-authority path (`treesitter_new(...)`
then `.parse_outline()`) before the real parser runs. That is why the bug is
reproducible on a **one-file** source set and needs no stage1 build.

Clean discriminator:

| file | occurrences | stalls |
|---|---|---|
| `treesitter_types.spl` | 1 (its own field `internal_exports:`) | yes |
| `outline.spl` | 9 | yes |
| `outline_members` / `_decls` / `_types` / `_lexer` | 0 | no |

`treesitter_types.spl` — the file that DEFINES the outline types — is caught by
the naive substring test for those very types.

### Recorded design concern (not fixed here; someone's call)

Routing the parser by **unanchored `contains()` over whole file text** is
fragile by construction. Even with the loop fixed, any file that merely
mentions `friend ` or `internal_export` in a comment, a string literal, or an
identifier silently takes a different parse path than its neighbours. This
should be a deliberate decision, not an accident of substring matching; an
anchored/token-aware test would make routing a property of declarations rather
than of arbitrary text.

## Landmine hit during investigation — filed separately

`lexer_next_token` (`core/lexer.spl:91`) **hardcodes `span.start = 0`** for
every token. A probe built on `self.current.span.start` therefore cannot
distinguish "cursor stuck" from "spans are degenerate", and a progress guard
written against it compares `0 == 0` and fires unconditionally. One such guard
was written here, produced a plausible-looking but meaningless reading, and was
reverted. Switching the probe to `kind` gave the answer immediately.
See `doc/08_tracking/bug/lexer_next_token_hardcodes_span_start_zero_2026-08-23.md`.

## Hypotheses ruled out with evidence

- **Stray `Dedent` / `treesitter_synchronize` recovery.** It is true that
  `synchronize` returns without consuming on `Dedent` while the member loops in
  `outline_decls`/`outline_members` are safe only because they `break` on
  Dedent themselves — but that is **not** this bug. Fixing it was tried first
  and **did not stop the hang**; the probe then showed the parser never reaches
  any Dedent because it never gets past EOF-recognition. (The `synchronize`
  asymmetry remains a latent sharp edge, but with `is_at_end` correct its inner
  loop now terminates.)
- **`d6fce96e530`** ("self.<stripped>() call sites", 563 rewrites across the
  outline family) is **exonerated**: it rewrote all five outline files roughly
  equally, yet only the two containing the trigger substring stall, and its
  diff touches no lexer or `next_token` line.
- **The shard work queue**: a claim does file I/O, and the measured
  `rchar`+`wchar` delta is 0. The spin is inside one `parse_full_frontend` call.
- **`parsed_entry_index` probe loops** (`driver_source_pipeline_parsing.spl`
  :619, :686): capacity is `2n+1`, so load factor never exceeds 0.5.
- **`lex_next()` dead-lexer death**: already fails closed, reporting
  `[lexer_fatal] dead lexer` and returning kind 190.

## Guard

`scripts/check/check-outline-parse-terminates.shs` — executes the real parse of
every outline-authority fixture under a clock and fails if a parse is entered
but never returns. Verdict convention `PASS`/`FAIL`/`ERROR-on-zero`, fatal
`--selftest` (5 fixtures over the classification logic). Wired **advisory** in
`config/check/must_check_gates.sdn`: it runs real compiles (~8 min), and a
blocking multi-minute gate on every push is one that gets routed around with
`--no-verify`, which protects nothing.

Neuter-verified both directions on the real seed:
- with the fix: `PASS — 2 fixture(s) parsed, outline-authority path terminated for all`
- fix reverted: `FAIL — 2 fixture(s) parsed, outline-authority path did not terminate for: treesitter_types.spl(rc=124) outline.spl(rc=124)`

No existing guard could have caught this: every other guard checks trees,
ranges, or source text, and the two that run a compiler run it over source or
check that a binary does not crash. A parser that spins forever is well-formed
as bytes, compiles cleanly, crashes nothing, and returns no wrong answer — it
simply never returns. Only executing the parse under a clock can see it.
