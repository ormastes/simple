# Parse spin in the treesitter outline-authority path (phase 1 blocker)

Filed 2026-08-23. Status: **root cause localized with a cheap reproducer; fix NOT landed.**

## Symptom

stage1 runs 21 and 23 hang forever in step 1/6 at `parse 144/688` on
`src/compiler/10.frontend/treesitter_types.spl`, on a fully repaired tree.
All 8 parse shards burn ~65-83% CPU each with **exactly flat RSS** and
**zero `rchar`/`wchar` delta** -- a bounded-memory infinite loop, not slow
progress and not an I/O livelock.

## Reproducer -- no stage1 needed

`sh scripts/check/repro-outline-parse-spin.shs <seed> [timeout_s]`

Reproduces on a **one-file source set** in ~2.5 s of parse time. Measured
pre-fix: reaches `[build] parse 0/28 ... treesitter_types.spl` at **+2464 ms**,
then produces no further output while burning 95+ s CPU (utime 1567 -> 3211
ticks over 30 s = ~55% of a core) with RSS flat/falling
(383640 kB -> 378604 kB) and `wchar` frozen at 19919.

## Trigger: a substring, not the module count

`frontend.spl:76`
```
fn frontend_has_outline_authority(source: text) -> bool:
    source.contains("friend ") or source.contains("internal_export")
```
Any file containing either substring **anywhere** -- including in a struct
field name or a comment -- takes the outline-authority path at
`frontend.spl:133-140` (`treesitter_new(...)` then `.parse_outline()`) before
the real parser runs.

This explains the whole affected file set, and it is a clean discriminator:

| file | occurrences | stalls |
|---|---|---|
| `treesitter_types.spl` | 1 (field `internal_exports:`) | yes |
| `outline.spl` | 9 | yes (reported by a second lane) |
| `outline_members.spl` | 0 | no |
| `outline_decls.spl` | 0 | no |
| `outline_types.spl` | 0 | no |
| `outline_lexer.spl` | 0 | no |

`treesitter_types.spl` matches on its own field name -- the file that DEFINES
the outline types is caught by the naive substring test for those types.

## Localization (positional, from the build's own receipts)

With `SIMPLE_COMPILER_TRACE=1` the last receipt is
`phase2:parse:file:start .../treesitter_types.spl chars=11201`, and
`[frontend] parse_and_build:start` (`frontend.spl:145`) **never appears**.
That marker sits immediately after the outline-authority block and immediately
before `frontend_parse_or_restore`, so the spin is inside
`authority_tree.parse_outline()` and nowhere else.

## Where it spins

`outline.spl`, `parse_outline()` top-level loop:
```
while not self.treesitter_is_at_end():
    self.treesitter_skip_newlines()
    if self.treesitter_is_at_end(): break
    val item = self.treesitter_parse_top_level_item()
    match item: ... case _: pass
    # no progress guard, no Dedent handling
```
The loop has **no progress guarantee**. Unrecognised tokens reach the
`case _:` arm of `treesitter_parse_top_level_item`, whose only recovery is
`treesitter_synchronize()` -- and synchronize (`outline_lexer.spl`) **returns
without consuming** when the current token is `Dedent`:
```
me treesitter_synchronize(self: TreeSitter):
    while not self.treesitter_is_at_end():
        if self.treesitter_check(TokenKind.Newline):
            self.treesitter_advance(); return
        if self.treesitter_check(TokenKind.Dedent):
            return          # consumes NOTHING
        self.treesitter_advance()
```
The member loops in `outline_decls` / `outline_members` are safe from this
because they `break` on `Dedent` themselves. The top-level loop has no such
check.

## What is NOT the cause (ruled out with evidence)

- **`d6fce96e530`** ("self.<stripped>() call sites", 563 rewrites across the
  outline family) is **exonerated**: it rewrote all five outline files roughly
  equally, but only the two containing the trigger substring stall. Its diff
  also touches no lexer/`next_token` line in `outline_lexer.spl`.
- **The shard work queue** is exonerated: a claim involves file I/O, and the
  measured `rchar+wchar` delta is zero. The spin is inside a single
  `parse_full_frontend` call, not the loop over files.
- **The open-addressed `parsed_entry_index` probe loops**
  (`driver_source_pipeline_parsing.spl:619,686`) are exonerated: capacity is
  `2n+1`, so load factor never exceeds 0.5 and the probe always finds a hole.
- **`lex_next()` dead-lexer death** is exonerated: it already fails closed,
  reporting `[lexer_fatal] dead lexer` and returning kind 190 (Eof).

## Open question blocking the fix

An instrumented run shows the loop re-dispatching with `self.current.span.start`
pinned at 0 and `text` empty for 400 consecutive iterations. **`span.start` is
not usable as a cursor probe**: `lexer_next_token` (`core/lexer.spl:85-92`)
hardcodes it --
```
val span = lex_span_new(0, text.len(), line, col)   # start is ALWAYS 0
```
-- so that measurement cannot distinguish "cursor stuck" from "spans are
degenerate", and a progress guard written against `span.start` is therefore
invalid. Two candidate fixes were tried and **neither resolved the hang**:
skipping stray `Indent`/`Dedent` at top level, and a `span.start`-based
progress guard (the latter is unsound for the reason just given).

Note also that `lexer_next_token` is the **only** non-threading token wrapper
in the tree, and `treesitter_advance` is its **only** caller. Every other
consumer uses `core_lexer_next_token(lexer) -> (CoreLexer, i64)` and threads
the returned lexer explicitly. That asymmetry is why only the outline parser
is affected and is the first place to look next.

## Next steps

1. Instrument with a real cursor (token index or `lex_token_line`/`col`), not
   `span.start`, to establish whether `treesitter_advance` advances at all.
2. Fix `lexer_next_token`'s hardcoded `span.start = 0` regardless -- it makes
   every outline span degenerate and defeats
   `frontend_strip_outline_authority_spans`, which orders spans by `.start`.
3. Add an unconditional progress guarantee to the `parse_outline` top-level
   loop once a sound cursor exists.
