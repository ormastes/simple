# Parser rejects line continuation after a trailing binary comparison operator
**Status:** CLOSED (2026-09-13) -- not reproducible; minimal repro now parses and runs correctly (the 2026-09-12 re-verification was a misattribution, see Re-check below)

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

## Re-check 2026-09-13 (BUGFIX-10 fanout) — the 2026-09-12 re-verification was a misattribution

The 2026-09-12 "Triage" entry's evidence (`host_gui_event_router_spec.spl`
"2 of 5 checks still fail") does NOT test this bug. Independently
investigated those same 2 failures earlier in this lane's pass (see
`int_to_u8_to_char_chained_call_nested_dispatch_2026-08-07.md`): both are
`method 'get_prop' not found on value of type enum in nested call context`
— a completely different defect (interpreter nested-call dispatcher on enum
receivers, `doc/08_tracking/bug/interp_enum_method_nested_call_dispatch_2026-06-29.md`),
with no trailing-comparison-operator parsing involved at all. That row's
own re-verification command was a stale copy-paste, not an actual test of
this bug's symptom.

Ran this doc's own minimal repro directly instead:

```
$ bin/simple run scratchpad/probe_trailing_op.spl
fn f(a: i64, b: i64) -> bool:
    if a >
       b:
        return true
    false
...
true
```

Parses and runs correctly — `f(3, 1)` returns `true`, no
`Unexpected token: expected expression, found Newline`. Also compiled
`src/lib/common/web/browser_renderer_protocol.spl` (the file the workaround
was applied to) directly: it fails for a completely unrelated reason
("cannot compile to standalone SMF: 28 function(s) contain constructs that
require the interpreter" — a native-AOT capability gap, not a parse error),
confirming no `Unexpected token`/parse failure there either.

- Status: CLOSED (2026-09-13) — not reproducible on `f26970e9d93`; the
  named parser defect is gone. The 2026-09-12 entry's "still reproduces"
  claim rested on an unrelated bug's failures and should be disregarded.
## Triage 2026-09-13 (BUGFIX-6 lane)

Skipped from this row-order pass: primary file/fix surface is the Rust seed
(`src/compiler_rust/**`) or otherwise not exercisable/fixable from this
pure-Simple, non-Codex lane within the triage budget. Not reproduced or
re-diagnosed this pass; left OPEN as-is.
