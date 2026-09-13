# Self-hosted parser rejects standard SSpec suite syntax

Date: 2026-08-08
Status: open / release-blocking for LLM Caret executable SSpec evidence

## Reproducer

Run the current macOS arm64 self-hosted binary against the isolated Caret
workspace with its source/delegation paths explicitly pinned:

```text
.../simple run test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl --mode=interpreter
```

The parser reports `unexpected token in expression: ':'` at every standard
SSpec suite/example header, beginning at:

```simple
describe "REQ-LLM-CARET-TUI-HARDEN-009: frame and input behavior":
    it "should clamp inner content height for undersized terminals":
```

The same grammar is used throughout the existing Caret test suite. The failure
happens before imports, fixtures, or assertions, so it is not caused by the
typed terminal lifecycle change.

## Expected

The self-hosted runtime accepts canonical `describe "...":` and
`it "...":` SSpec declarations and executes the current 19 examples.

## Actual impact

The focused self-hosted test command exits before executing any example. The
mirrored runtime manual cannot be regenerated from this runtime, and the typed
`CaretIo.begin_tui/end_tui` contract has no authoritative executable result.

## Scope and next owner

This is a compiler/SSpec parser compatibility defect. Do not rewrite Caret
specs into a noncanonical DSL variant merely to accommodate one deployed
runtime: that would diverge from repository SSpec convention and hide the
runtime regression. The owner must add a minimal parser regression around a
single `describe`/`it` pair, repair the parser, rebuild a provenance-qualified
self-hosted binary, then rerun the focused Caret spec and regenerate its manual.

## Triage 2026-09-13 (BUGFIX-12 shard 22)

Repro needs an actually-deployed self-hosted binary (bootstrap output), which
is out of scope for this shard (bootstrap is a separate sanctioned pipeline,
not a shard-triage action, and this worktree only has the Rust seed linked at
`bin/simple`). Source-level lead: `grep -rn '"describe"' src/compiler/` finds
no `describe`/`it` special-casing in `src/compiler/10.frontend/core/parser.spl`
or its `_Parser*` siblings — SSpec `describe "...":` / `it "...":` headers are
ordinary call-expressions followed by a colon+indented block, i.e. this needs
the *generic* "call-expression statement may open a colon block" grammar rule,
not a `describe`-specific one. `unexpected token in expression: ':'` firing at
that call means the self-hosted statement parser only allows a trailing `:`
block after specific keyword-led statements (`if`/`while`/`for`/`fn`/etc.),
not after an arbitrary primary/call expression — that's the gap to close in
the self-hosted parser's statement dispatch, most likely in
`_ParserDecls`/`_ParserPrimary` where `"unexpected token in expression"` is
raised (`src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`,
`_ParserPrimary/primary_expr.spl`). Needs a self-hosted-build verification
loop this shard cannot run. Leaving OPEN with this direction recorded.
