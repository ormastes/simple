# Parser rejects line continuation after a trailing binary comparison operator
## Resolved 2026-11-25 — fixed by 023a60a05aa, verified on the pinned seed (see end of file)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.
(Superseded by the 2026-11-25 resolution note at the end of this file.)

- **Date:** 2026-08-04
- **Area:** compiler/parser (both Rust seed and self-hosted stage binary agree)
- **Symptom:** `compile failed: parse: ... Unexpected token: expected expression, found Newline`

## Repro

```spl
fn f(a: i64, b: i64) -> bool:
    if a >
       b:
        return true
    false
```

An unparenthesized condition that breaks the line immediately after a binary
comparison operator (`>`, `<`, `>=`, ...) fails to parse. The same expression
wrapped in parentheses parses fine:

```spl
    if (a >
        b):
```

## Impact

`src/lib/common/web/browser_renderer_protocol.spl` was committed with three
such continuations (in `browser_renderer_capability_message_encode` and the
capability decoder's payload-length check). Since that module is in the import
chain of the hosted WM stack (`common.ui.gpu_web_capacity_manifest` ->
hosted compositor specs), every spec that pulls the hosted chain failed to
load in the test lane, e.g.:

```
FAIL test/01_unit/os/compositor/host_gui_event_router_spec.spl
  Error: error: compile failed: parse: in ".../browser_renderer_protocol.spl":
  Unexpected token: expected expression, found Newline
```

## Workaround applied (2026-08-04)

Parenthesized the three conditions in `browser_renderer_protocol.spl`
(lines ~575, ~583, ~780), matching the parenthesized multi-line style the rest
of that file already uses. This unblocks the hosted compositor spec chain.

## Ask

Either support line continuation after a trailing binary operator (the file
was committed in that style, so some earlier lane accepted or never parsed
it), or have lint/fmt flag bare trailing-operator continuations at commit
time so they cannot land unparsed.


## Resolved 2026-11-25 (p2w4-ad lane, release/1.0.0 @ ef6a94f8a03) — STALE, fix already landed

Fixed by `023a60a05aa` ("fix(parser): support trailing-operator line
continuation for comparison and equality operators", in tree at HEAD): the
hand-written `parse_comparison`/`parse_equality` in
`src/compiler_rust/parser/src/expressions/binary.rs` never inherited the
continuation handling the macro-generated binary parsers had; they do now.

Verified behaviorally on the pinned seed
(`SIMPLE_LIB=src bin/simple.exe run <probe> --mode=interpreter`) with the
doc's exact repro shape — `if a >\n   b:` unparenthesized — which now parses
and runs (`parse-cont ok`).

Known residual, deliberately out of scope of that fix and pinned by its own
test: `elif` conditions still reject the continuation (statement-level indent
bookkeeping, not expression parsing) — see
`elif_condition_continuation_is_still_unsupported` and
`doc/08_tracking/bug/comparison_operator_line_continuation_parse_2026-07-30.md`.

**Status: RESOLVED.**
