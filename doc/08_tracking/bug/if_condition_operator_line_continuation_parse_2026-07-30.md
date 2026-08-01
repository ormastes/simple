# Trailing-operator line continuation rejected for comparison/equality operators (seed parser only)

**Status:** FIXED for comparison and equality (2026-07-30). One sub-case
remains open: `elif` conditions — see "Remaining gap" below.
**Found:** while running
`scripts/check/check-linux-hosted-wm-live-window-evidence.shs`.

## Corrected diagnosis — the defect is OPERATOR-scoped, not `if`-scoped

The first report framed this as "continuation fails inside an `if`
condition but parses in a `val` binding". **That framing was wrong**, and
it was wrong because the original repro pair changed two variables at
once: it used `+` in the binding and `>` in the condition. Controlling for
that shows the context is irrelevant and the operator is everything —
comparison/equality continuation fails in a `val` binding just as it does
in an `if`:

| Form | Old seed |
|---|---|
| `val x = a +` ⏎ `b` | PARSES |
| `if a and` ⏎ `b:` | PARSES |
| `val x = a >` ⏎ `b` | **FAILS** |
| `val x = a ==` ⏎ `b` | **FAILS** |
| `if a >` ⏎ `b:` | **FAILS** |
| `while a >` ⏎ `b:` | **FAILS** |

## Root cause (PROVED)

`src/compiler_rust/parser/src/expressions/binary.rs` generates most binary
operator parsers with `parse_binary_single!` / `parse_binary_multi!`, and
those macros handle line continuation (both trailing-operator and
leading-operator forms) by calling
`skip_newlines_and_indents_for_method_chain()`.

Two parsers are **hand-written** and therefore never inherited it:

- `parse_comparison` — hand-written to support chaining (`a < b < c`);
- `parse_equality` — hand-written to support `not in`.

Both did `self.advance()` past the operator and immediately called the
next precedence level, so a newline after the operator hit the expression
parser directly: *"expected expression, found Newline"*.

## Engine scope: seed parser ONLY (PROVED)

- **Rust seed parser: BROKEN** (all comparison/equality forms above).
- **Pure-Simple parser (`src/compiler/10.frontend/core/parser_expr.spl`):
  NOT affected** — `build/redeploy_out/simple_stage2` parses every form
  above, including the exact real-world construct.

So there is a real engine divergence, and no pure-Simple change is needed.

This also explains how the offending source got committed: it parses fine
under the pure-Simple parser, and only the seed rejects it.

Note on how it surfaced: the host-WM gate ran with `SIMPLE_BIN=stage2`,
yet the parse error came from the seed — `native-build` spawns a worker
that uses the **deployed** `bin/simple` regardless of `SIMPLE_BIN`.

## Real-world impact

`src/lib/common/web/browser_renderer_protocol.spl:559`, introduced by
`ba0ce4e3c06` *"feat(web): add SBR2 command capability codec"*
(2026-07-30):

```simple
    if payload_bytes.len().to_i64() >
       BROWSER_RENDERER_MAX_PAYLOAD_BYTES - capability_bytes:
```

This blocked `check-linux-hosted-wm-live-window-evidence.shs` at
`reason=production-native-build-failed` (walls 1-7 otherwise passing), and
would block any lane compiling that file with the seed.

## Fix

Added the same trailing-operator continuation skip the macros use to both
hand-written parsers, immediately after the operator is consumed. The fix
is confined to those two functions; no statement-level or lexer change.

**The source file was deliberately NOT edited** — per CLAUDE.md, a short
safe grammar form that fails is a parser bug to fix, not something to
normalize away in the caller.

Tests: `comparison_continuation_tests` in the same file — comparison
(`<`, `>`, `<=`, `>=`) and equality (`==`, `!=`) continuations in both
binding and `if` position, `while` conditions, the exact real-world
construct, and a guard that the already-working arithmetic/logical forms
keep parsing. Full parser suite: 240/240 pass.

## Remaining gap: `elif` (open, deliberately not chased)

`elif a >` ⏎ `b:` still fails. After the expression-level fix its error
**moves** from `expected expression, found Newline` to
`found Indent` (continuation indented deeper) or `found Dedent`
(continuation aligned) — i.e. it is no longer an expression-parsing
problem at all, but `elif`'s own statement-level indent bookkeeping.

Fixing it means touching the statement/expression boundary, which carries
real regression risk for all indentation-sensitive parsing, so it is left
open rather than rushed. It was already broken before this fix, so nothing
regressed. The behaviour is pinned by
`elif_condition_continuation_is_still_unsupported`, which asserts the
current failure and tells whoever fixes it to flip the assertion.
