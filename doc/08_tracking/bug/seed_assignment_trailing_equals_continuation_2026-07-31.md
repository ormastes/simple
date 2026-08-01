# Rust-seed parser rejects trailing-`=` assignment continuation — FIXED

- **ID:** seed_assignment_trailing_equals_continuation_2026-07-31
- **Status:** FIXED (seed parser, `src/compiler_rust/parser/src/expressions/no_paren.rs`)
- **Severity:** high — blocked native-build discovery of the whole
  `hosted_browser_renderer_worker.spl` module, which in turn was the last wall
  in front of showcase cells #4-6 (host-WM)

## Symptom

```
Build failed: failed to parse .../src/os/hosted/hosted_browser_renderer_worker.spl
at 1066:41 during discovery: Unexpected token: expected expression, found Newline
```

```
            self.input_view_start_byte =
                frame.resolved_input_view_start_byte
```

## Root cause (PROVED)

`parse_expression_or_assignment` in
`src/compiler_rust/parser/src/expressions/no_paren.rs` consumed the assign-op
token (`=`, or a compound form `+=`/`-=`/`*=`/`/=`/`%=`/`~=`/...) and
immediately called a **fresh top-level** `parse_expression()` for the RHS. A
Newline right after the operator hit "expected expression, found Newline"
before any expression-level continuation handling ever ran — unlike the
binary operators in `expressions/binary.rs`, which continue mid-chain inside
an already-open `parse_expression_inner()` call and so inherit its
`binary_indent_count` save/reset/drain bookkeeping automatically.

## Fix

Right after consuming the assign-op token, call
`skip_newlines_and_indents_for_method_chain()` (same primitive
`expressions/binary.rs` uses for the comparison/equality fix, `023a60a05aa`)
and record how many INDENTs it consumed. After the RHS `parse_expression()`
call returns, drain the matching DEDENTs with
`consume_dedents_for_method_chain()` — the same save/skip/drain shape, just
applied around a top-level `parse_expression()` call instead of mid-chain.
Single fix site; both plain `=` and every compound-assign token share the
`if let Some(op) = assign_op { ... }` branch, so one change covers all of
them.

## Non-vacuity (PROVED)

`cargo test -p simple-parser --lib expressions::no_paren::` — new
`assignment_continuation_tests` module, 4 tests:

- Before fix (fix lines replaced with a `TEMP-REVERTED` marker, tests kept):
  `1 passed; 3 failed` — the 3 continuation cases panic with "expected
  expression, found Newline" / "found Dedent" shaped assertion failures; the
  same-line guard test still passes (no regression there).
- After fix restored: `4 passed; 0 failed`.

Full parser suite after the fix: `cargo test -p simple-parser` — 39 test
binaries, 909 passed, 0 failed. No regressions.

## Engine scope (PROVED) — seed-only, pure-Simple parser unaffected

Probed the exact construct plus a plain-local-var and compound-assign variant
against the pre-built pure-Simple self-hosted compiler
(`build/native_probe/stage3-explicit/simple compile --format=smf`, same
probe method as `a7e5fbccf85`): all three probes progress past
`parse_module_body` (the trace marker for a completed parse) and fail only
downstream, at HIR/MIR lowering, on causes unrelated to this construct
(`unresolved name: self` on the field-access repro — a separate,
already-known receiver-binding quirk; `unresolved method call: merge` on the
plain-function repro — unrelated stdlib gap). Parsing itself never errors.
This is a seed-only engine divergence, consistent with the sibling
comparison/equality (`023a60a05aa`) and elif-drain (`a7e5fbccf85`) fixes from
the same week.

## Distinct from two pre-existing, already-source-fixed bug docs

`doc/08_tracking/bug/assign_rhs_newline_continuation_parse_2026-07-25.md` and
`doc/08_tracking/bug/parser_bare_reassignment_multiline_continuation_2026-07-25.md`
describe the **identical surface symptom** (`x =\n expr` failing) but are
about the **pure-Simple self-hosted lexer/parser**
(`src/compiler/10.frontend/core/{lexer_scanners,lexer_struct,tokens}.spl`),
fixed there by `ab63c351d142` (2026-07-13, well before this defect's
introduction). `ab63c351d142` never touched `src/compiler_rust/**`; grepping
the current tree for its `token_requires_rhs` suppression mechanism outside
`src/compiler/` returns nothing. The Rust seed parser bug fixed here is a
separate defect in a separate parser implementation that happens to produce
the same error text. Cross-referenced from both older docs.

## Distinct from two neighbouring defects — do not conflate

- `023a60a05aa` fixed `parse_comparison`/`parse_equality` trailing-operator
  continuation (binary-operator mid-chain, not assignment-statement RHS).
- `seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md` is
  a DEDENT-then-INDENT ambiguity specific to a continuation line indented
  *deeper* than its own block body; distinct mechanism, still open.

## Continuation family enumeration

See `doc/08_tracking/bug/seed_line_continuation_family_enumeration_2026-07-31.md`
for the full per-construct probe table (`family_continuation_probe.rs`).

## Verified end-to-end with the real LLVM-featured seed binary (PROVED)

Built `cargo build --profile bootstrap -p simple-driver --features llvm`
(154 MB binary, confirms the LLVM feature is actually linked — a plain
`--release` build is ~57 MB with no LLVM). Ran
`simple compile src/os/hosted/hosted_browser_renderer_worker.spl` directly:
the original `1066:41 ... found Newline` error is gone. Discovery now
proceeds past that file and past its `use` graph, and fails later in a
**different file**
(`src/lib/gc_async_mut/web/browser_session_runtime.spl`) with a **different**
error shape (`Unexpected token: expected expression, found Indent`, no
line/col reported). A minimal repro of the nearby `elif (\n ...\n):`
parenthesized-condition shape at that file's line ~553 parses cleanly in
isolation, so the new wall is a distinct, not-yet-bisected defect —
**explicitly out of scope for this fix**, not chased further here. Whoever
picks up the next wall should start with
`simple compile src/lib/gc_async_mut/web/browser_session_runtime.spl` on the
LLVM-featured seed built from this fix.
