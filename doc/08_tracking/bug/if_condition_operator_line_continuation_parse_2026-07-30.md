# Trailing-operator line continuation rejected for comparison/equality operators (seed parser only)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
`elif` sub-case landed 2026-07-31 (`a7e5fbccf85` plus the shared
`parse_condition_block` drain in `parser_impl/core.rs`) and is re-verified
closed at origin `b9341804e5` on 2026-08-01 — see "Remaining gap" below,
which is now a closed record rather than an open item.
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

## Remaining gap: `elif` — CLOSED 2026-07-31, re-verified 2026-08-01

The section below is the original open-item write-up, kept for the
diagnosis. It is no longer open. `elif a >` ⏎ `b:` now parses, in both the
deep (continuation column > body column) and shallow shapes, together with
`else if`, `while`, and chained `elif`. The fix did land in the
statement/expression boundary, exactly where this section predicted:
`parse_elif_or_else_if_body` in `stmt_parsing/control_flow.rs` applies the
save-before/drain-after `deferred_dedent_count` dance at all four `elif` /
`else if` call sites, and `parse_condition_block` in `parser_impl/core.rs`
drains at BOTH candidate points so the deep and shallow shapes agree.
Coverage is `elif_condition_continuation_parses`,
`elif_condition_deep_continuation_indent_ambiguity_is_now_supported`, and
`condition_continuation_indent_shape_matrix` in
`src/compiler_rust/parser/src/expressions/binary.rs`, plus the
language-level `test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl`.

Re-verification on 2026-08-01 at origin `b9341804e5` (PROVED): a probe test
built against the tip `simple-parser` crate parses `elif a and` ⏎ `b:`,
`elif a ==` ⏎ `b:`, `elif a >` ⏎ `b:`, and the real-world
`browser_session_runtime.spl` dispatch condition, while a deliberate
syntax-error fixture in the same run still fails.

**Trap for the next reader:** the deployed `bin/simple_seed` in this
workspace is a 2026-07-25 binary, i.e. older than BOTH the assignment fix
(`6587c9e8875`) and this `elif` fix. Probing with it reproduces the exact
original error strings and looks like the gaps are still open. Probe the
tip source (`cargo test -p simple-parser`), not the deployed binary.

### Original write-up (historical)

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
