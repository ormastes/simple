# Multi-line trailing-`or` condition + inline `: return` body — known parser grammar limitation (re-encountered via a corrupt shared-WC edit, origin unaffected)

**Date:** 2026-07-30
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
this doc originally reported as a pipeline blocker was **not** present at
origin; it was a corrupt, uncommitted edit in the shared working copy from
another session. What remains valid and durable: a real parser grammar
limitation, already known and already worked around at origin
(`941c1daeacf`), with a minimal repro and a `parse_if` locus analysis for
the grammar-fix backlog.
**Component:** Rust seed parser, `src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`
(`parse_if`, inline-statement branch, ~line 148-190)

## Correction (2026-07-30, same day)

The original version of this doc reported `SIMPLE_EXECUTION_MODE=jit` on
`examples/06_io/ui/web_render_file_gui.spl` hitting a parse error in
`src/lib/skia/feature/shaper/ot_layout_shaper.spl`, and attributed it to a
pre-existing defect dating to commit `f119f8b7120` (2026-07-28), predating
`doc/08_tracking/bug/web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`.

**That attribution was wrong.** The coordinator identified and verified: the
exact parse-error class this doc hit was already fixed at origin the day
before this investigation, in `941c1daeacf` ("parenthesized all the
multi-line-if inline-body sites"). **Origin's copy of
`ot_layout_shaper.spl`, at this doc's own landed commit tip, already has the
parenthesized form at line 167 and compiles clean:**

```
    if (start < 0 or end_idx > codepoints.len() or start >= end_idx or
        not _selected_text(script, language, codepoints, start, end_idx)): return None
```

What this investigation actually measured was the **shared working copy**
at `/home/ormastes/dev/pub/simple`, which was carrying **another session's
uncommitted, corrupt edit**: the parens had been reverted, and an
if/else was truncated mid-argument-list. That corruption — not origin, not
`f119f8b7120`, not a re-encountered pipeline blocker — is what produced the
`Unexpected token: expected expression, found Dedent` error reproduced
below. The coordinator restored the file from origin per the stale-WC
protocol; it compiles clean in the working copy now. This is (per the
coordinator) the third lane this same shared WC has burned this way.

**Consequently:** the earlier framing of this doc ("a previously-undocumented
blocker predating and superseding the 2026-07-29 `DrawIrRenderTarget`/
`CastElse` gaps, currently stopping every JIT attempt on the real pipeline")
is **retracted**. The `DrawIrRenderTarget`/`CastElse` gaps from
`web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md` were never
superseded and remain the operative blockers for the original JIT
root-cause assignment — re-investigated separately from a pristine worktree,
see that assignment's own landing for the corrected result.

## What stays valid and durable from this pass

The multi-line-condition-plus-inline-return shape this pass stumbled onto
**is a real, known parser grammar limitation** — exactly the one
`941c1daeacf` worked around by parenthesizing affected call sites, and
documented at origin as a known runtime limitation ("multi-line booleans —
wrap in parentheses"). This pass's contribution is a clean **minimal
repro** and a **`parse_if` locus analysis**, useful for whoever eventually
closes the grammar gap itself (rather than continuing to route around it
with parentheses at each call site):

### Minimal repro (PROVED — reproduces the documented limitation directly, independent of the WC-corruption episode)

```
fn resolve_x(start: i64) -> i64:
    if start < 0 or
        start == 99: return 0
    1
```

`bin/release/x86_64-unknown-linux-gnu/simple run` on this 6-line file
reproduces `Unexpected token: expected expression, found Dedent`. Both
halves of the trigger were individually confirmed necessary:

- Single-line condition + inline `if: return` + trailing bare statement:
  **works** (e.g. `if start < 0: return 0` on one line).
- Multi-line condition (trailing `or` continuing onto the next indented
  line) + inline `if...: return` body + a trailing bare statement at the
  **outer** indentation (the dedent back out of the `if`): **fails**, every
  time, with this exact symptom.

Wrapping the multi-line condition in parentheses (the `941c1daeacf`
workaround) clears it, consistent with that fix's own description.

### `parse_if` locus (PROVED — found by reading; mechanism below is INFERRED, not traced)

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
parser" per its own comment. **Working hypothesis, not confirmed:** when
the `if`'s own *condition* was multi-line (via the lexer's G27
"trailing-RHS-token continues the logical line" suppression of
`Newline`/`Indent`/`Dedent` while scanning `or`-continued conditions —
consulted in `src/compiler/10.frontend/core/lexer_struct.spl`'s own
doc-comment for the identical continuation mechanism, in the pure-Simple
lexer, not proof this is the same code path in the Rust seed), the token
stream's `Dedent` bookkeeping for the *outer* block ends up off by one
relative to the single-line-condition case, so the "outer block parser"
this comment refers to sees a `Dedent` where it expects another expression.
This is a locus-correct, plausible hypothesis — not a confirmed mechanism.
It was not instrumented or traced through the lexer's indent-stack state to
verify, and is left for whoever picks up the grammar-fix backlog item.

## Recommended next steps (grammar-fix backlog, not urgent — the workaround is known and applied at known sites)

1. Confirm the hypothesis with a debug trace of the lexer's `indent_stack`
   depth across the two minimal-repro variants.
2. Fix in the lexer's G27 continuation logic or the parser's post-inline-if
   newline handling (whichever the trace implicates) so the parenthesization
   workaround is no longer required.
3. Survey owned `.spl` source for the same `if <cond> or\n    <cond>:
   <inline-stmt>` shape that has **not** yet been parenthesized — `941c1daeacf`
   covered known sites, but the shape may recur elsewhere and only surface
   when something eventually whole-program-JIT-compiles that file.

## Validation performed this pass

- WC-corruption correction: PROVED (origin diff-verified, coordinator's
  restoration confirmed).
- Minimal repro: PROVED, independent of the WC episode — reproduces the
  documented, already-known-and-worked-around grammar limitation directly.
- `parse_if` locus: PROVED (code read). Mechanism: INFERRED (hypothesis,
  not traced).
- No code change made this pass (grammar fix not attempted — backlog item,
  not urgent given the existing workaround).
