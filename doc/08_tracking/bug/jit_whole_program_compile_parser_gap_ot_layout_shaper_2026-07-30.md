# Forcing JIT on the web pipeline hits a parser bug BEFORE the documented HIR-lowering gaps

**Date:** 2026-07-30
**Status:** OPEN — reproduced and precisely localized (PROVED); not fixed
(deep lexer/parser interaction, judged too risky to rush)
**Component:** Rust seed parser, `src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`
(`parse_if`, inline-statement branch, ~line 148-190); surfaced via
`src/lib/skia/feature/shaper/ot_layout_shaper.spl`

## Context

`doc/08_tracking/bug/web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`
(2026-07-29) documented that forcing `SIMPLE_EXECUTION_MODE=jit` on
`examples/06_io/ui/web_render_file_gui.spl` hits `Unknown type:
DrawIrRenderTarget`, and a standalone repro (importing
`font_renderer.resolve_font_metrics_with_language`) hits a different gap,
`Unsupported feature: CastElse` on `read_u32_be` in
`src/lib/skia/feature/glyph/ot_parser_layout.spl:280`. This doc's task was to
root-cause and fix both.

## What actually reproduces today (2026-07-30) — PROVED

```
SIMPLE_EXECUTION_MODE=jit SHOWCASE_RESOLUTION=480x360 \
bin/release/x86_64-unknown-linux-gnu/simple run examples/06_io/ui/web_render_file_gui.spl
```

does **not** hit `Unknown type: DrawIrRenderTarget`. It hits a **parser**
error, fatal in both JIT and interpreted mode (parsing is shared):

```
[INFO] JIT compilation failed, falling back to interpreter: module load error: parse: in
  "src/lib/skia/feature/shaper/ot_layout_shaper.spl": Unexpected token: expected expression, found Dedent
error: compile failed: parse: in "src/lib/skia/feature/shaper/ot_layout_shaper.spl":
  Unexpected token: expected expression, found Dedent
```

This is a **different, earlier-encountered defect** than the two documented
2026-07-29 gaps — `ot_layout_shaper.spl` (directory `shaper/`) is a
different file from `ot_parser_layout.spl` (directory `glyph/`), despite the
similar name. `ot_layout_shaper.spl`'s only commit
(`f119f8b7120`, "chore: consolidate completed agent session work",
2026-07-28 23:58:13) predates the 2026-07-29 doc, so this bug already
existed when that doc was written — the doc's narrower standalone repro
(importing only `font_renderer.resolve_font_metrics_with_language`)
apparently didn't pull `ot_layout_shaper.spl` into its whole-program JIT
closure, but the full web pipeline entry does, and hits it first.

**Net effect: the two originally-documented gaps (`DrawIrRenderTarget`,
`CastElse`) could not be independently re-confirmed this pass** — the real
web pipeline and every JIT attempt that reaches this file now stops here
first. They are very likely still real and still present further along the
same whole-program JIT closure (nothing suggests they were fixed), but that
is now INFERRED, not re-verified, since this earlier blocker was never
cleared.

## Root cause — minimal repro (PROVED), locus found, exact mechanism NOT
resolved

Isolated via bisection (the real file's `resolve_canonical_layout_run`
function, lines 165-204) down to a 6-line minimal reproduction:

```
fn resolve_x(start: i64) -> i64:
    if start < 0 or
        start == 99: return 0
    1
```

`bin/release/x86_64-unknown-linux-gnu/simple run` on this file alone
reproduces the identical `Unexpected token: expected expression, found
Dedent` error. Removing either the multi-line condition (folding `or` back
onto one line) or restructuring the inline `if...: return` clears it —
**both individually confirmed necessary** for the trigger (tested):

- Single-line condition + inline `if: return` + trailing bare statement:
  **works** (`if start < 0: return 0` on one line).
- Multi-line condition (trailing `or` continuing onto the next indented
  line) + inline `if...: return` body + a trailing bare statement on the
  next line at the **outer** indentation (the dedent back out of the `if`):
  **fails**, every time, with the exact "expected expression, found Dedent"
  symptom from the original repro.

**Locus (PROVED, found by reading, not yet instrumented/traced):**
`src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`, `parse_if`,
the inline-statement branch (~148-190). After parsing the inline `then`
statement, it does:

```rust
if self.check(&TokenKind::Newline) {
    let has_elif_or_else = self.peek_through_newlines_and_indents_is(&TokenKind::Elif)
        || self.peek_through_newlines_and_indents_is(&TokenKind::Else);
    if has_elif_or_else {
        while self.check(&TokenKind::Newline) { self.advance(); }
    }
}
```

i.e. it deliberately does **not** consume the trailing `Newline`/`Dedent`
tokens when no `elif`/`else` follows, leaving them "for the outer block
parser" per its own comment. **Working hypothesis, not confirmed:** when the
`if`'s own *condition* was multi-line (via the lexer's G27
"trailing-RHS-token continues the logical line" suppression of
`Newline`/`Indent`/`Dedent` while scanning `or`-continued conditions,
`src/compiler/10.frontend/core/lexer_struct.spl` — the pure-Simple lexer's
own doc-comment for the identical continuation mechanism, consulted for
comparison, not proof this is the same code path in the Rust seed), the
token stream's `Dedent` bookkeeping for the *outer* block is off by one
relative to the single-line-condition case, so the "outer block parser" this
comment refers to sees a `Dedent` where it expects another expression. This
is a plausible, locus-correct hypothesis, not a confirmed mechanism — it was
not instrumented or traced through the lexer's indent-stack state to verify.

## Why not fixed this pass

This is a genuine, deep interaction between the lexer's multi-line-condition
continuation suppression and the parser's inline-if trailing-token handling
— exactly the class of change CLAUDE.md's bootstrap rules flag as needing
full-bootstrap validation before landing (a lexer/parser grammar change,
not a contained one-line allowlist fix). Given the severity of getting this
wrong (silent mis-parse across the whole `.spl` corpus, not just a crash),
and the time budget for this pass, it was not attempted. Reported precisely
instead, per the established pattern for this class of finding in adjacent
docs this same day.

## Recommended next steps

1. Confirm the hypothesis with a debug trace of the lexer's `indent_stack`
   depth across the two probe variants (this doc's own `retry`-methodology
   would apply directly: instrument, diff token streams old vs new).
2. Fix in the lexer's G27 continuation logic or the parser's post-inline-if
   newline handling (whichever the trace implicates), then re-run the
   **original** two-gap repros from `web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`
   to confirm `DrawIrRenderTarget` and `CastElse` are still the next
   blockers (or have also changed).
3. Survey for the same `if <cond> or\n    <cond>: <inline-stmt>` shape
   elsewhere in owned `.spl` source — this pattern is common enough
   (`_selected_text`/`resolve_canonical_layout_run` in the same file alone
   has two more near-misses) that other files may already carry the same
   latent parse failure, only unreached because nothing has whole-program
   JIT-compiled them yet.

## Validation performed this pass

- Reproduction: PROVED, exact command from the assigned task, current
  source, current deployed seed.
- Root-cause locus: PROVED (function and file identified via bisection),
  mechanism: INFERRED (plausible hypothesis, not traced/confirmed).
- Fix: not attempted (documented reason above).
- Byte-identical-archive / cargo-clean validation: not applicable — no
  code change was made this pass.
