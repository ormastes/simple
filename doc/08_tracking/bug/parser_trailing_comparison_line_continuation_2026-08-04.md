# Parser rejects line continuation after a trailing binary comparison operator
**Status:** OPEN (2026-09-12, re-verified: bin/simple test test/01_unit/os/compositor/host_gui_event_router_spec.spl -> 3 passed, 2 failed, still reproduces)

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

## Triage 2026-09-12
Rule B: ran `bin/simple test test/01_unit/os/compositor/host_gui_event_router_spec.spl` on the deployed seed; 2 of 5 checks still fail, so this record still reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Triage 2026-09-13 (BUGFIX-6 lane)

Skipped from this row-order pass: primary file/fix surface is the Rust seed
(`src/compiler_rust/**`) or otherwise not exercisable/fixable from this
pure-Simple, non-Codex lane within the triage budget. Not reproduced or
re-diagnosed this pass; left OPEN as-is.
