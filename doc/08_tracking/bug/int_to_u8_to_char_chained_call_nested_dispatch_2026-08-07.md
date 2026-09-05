# `(i64).to_u8().to_char()` chained call fails in nested-call dispatch context

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-07, U4.2 coverage-closure unit (WM/GUI/web system-test
coverage plan, `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`)
**Area:** interpreter / nested-call method dispatch (Rust seed)
**Binary provenance:** `readlink -f bin/simple` ->
`bin/release/x86_64-unknown-linux-gnu/simple`, seed banner confirmed present.

## Symptom

`src/os/compositor/host_gui_event_router.spl`'s `host_glfw_key_name(key: i64)`
(the GLFW-key-code-to-name mapper used by every real key-press routed through
`HostGuiEventRouter.route_scalar`) crashes for every letter and every
printable-ASCII key code — i.e. almost every real keystroke a hosted-WM user
ever sends:

```
error: semantic: method 'to_char' not found on value of type i64 in nested call context
```

Minimal repro (`bin/simple run`, no spec/test-runner involved):

```simple
val key: i64 = 65
val a = (key + 32).to_u8().to_char()   # chained call -> ERRORS
print(a)
```

versus the same computation split across an intermediate `val` (works):

```simple
val key: i64 = 65
val u = (key + 32).to_u8()
val a = u.to_char()                    # non-chained -> "a"
print(a)
```

Both variants were reproduced directly, isolating the trigger to the
**chained** two-method form `<expr>.to_u8().to_char()` specifically — the
receiver type after `.to_u8()` genuinely is `u8` (confirmed by the
intermediate-`val` variant succeeding), so this is not a type-inference bug in
the ordinary sense; it only manifests through the nested/chained-call
dispatch path.

## Why this is a distinct defect from the two related, already-closed bugs

- `doc/08_tracking/bug/i64_to_char_missing_outside_llvm_backend_2026-08-05.md`
  (FIXED 2026-08-05) added `to_char` to the **primary** interpreter dispatcher
  (`handle_int_methods` in `interpreter_method/primitives.rs`). That fix is
  what makes the intermediate-`val` variant above work — `u.to_char()` alone,
  as a single non-chained call, resolves through the primary dispatcher.
  `host_gui_event_router.spl` is explicitly listed as one of that bug's ~20
  affected call sites, but the chained form there was never independently
  retested after the primary-dispatcher fix landed — this report is that
  retest, and it shows the chained form is still broken.
- `doc/08_tracking/bug/interp_enum_method_nested_call_dispatch_2026-06-29.md`
  (FIXED, seed-side, pending redeploy per its own doc) added an
  `enum` receiver arm to the **separate nested/chained-call dispatcher**
  (`interpreter_helpers/method_dispatch.rs`). That fix only covers
  `Value::Enum` receivers; it does not touch primitive int/uint receivers.

This report's repro hits the **nested/chained-call dispatcher** (error text
says "in nested call context", matching that dispatcher's own error phrasing)
with a **primitive `u8` receiver**, which neither prior fix covers. The
nested dispatcher appears to fall back to treating the pre-`.to_u8()` value's
original type (`i64`) for method resolution on a chained call, rather than
re-deriving the type after the first method call in the chain — consistent
with the pattern already fixed once for `Value::Enum` in the 2026-06-29 doc,
just not yet mirrored for numeric-conversion methods (`to_u8`/`to_i32`/etc.
followed by another method call in the same chain).

## Impact

`host_glfw_key_name` is reached from `HostGuiEventRouter.route_scalar`'s
`WINDOW_EVENT_KEY` branch on every physical key press once a hosted window is
focused. Both of its non-trivial branches (`key >= 65 and key <= 90` and
`key >= 32 and key <= 126`) used the broken chained form before this unit's
fix, meaning **every uppercase letter and every printable-ASCII key code
crashed key routing** rather than dispatching a keypress. The `route_scalar`
KEY branch has no existing test coverage prior to this unit (see
`test/01_unit/os/compositor/host_gui_event_router_coverage_closure_spec.spl`,
U4.2), so this was live and undetected.

## Interim fix landed with this report

`src/os/compositor/host_gui_event_router.spl`'s `host_glfw_key_name` was
rewritten to use the documented repo workaround
(`.claude/rules/language.md` — "Chained methods on erased receivers... use
intermediate typed `val`") for both branches:

```simple
if key >= 65 and key <= 90:
    val lowered_byte: u8 = (key + 32).to_u8()
    return lowered_byte.to_char()
if key >= 32 and key <= 126:
    val printable_byte: u8 = key.to_u8()
    return printable_byte.to_char()
```

This is a call-site workaround, not a fix to the underlying nested-call
dispatcher — the chained form remains broken repo-wide for any other call
site that hits it. Real oracle regression test:
`host_gui_event_router_coverage_closure_spec.spl`, describe block
`"host_glfw_key_name (U4.2 closure)"`, all three `it`s (12 non-printable
codes, uppercase-range + printable-range lowering, and the empty-fallback
both-directions case).

## Unblock condition

Add a primitive-receiver arm (int/uint post-conversion, mirroring the
`Value::Enum` arm added 2026-06-29) to the nested/chained-call dispatcher in
`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`, or
confirm/rebuild+redeploy if such an arm already exists in seed source but is
undeployed (as was true for the enum fix at the time its doc was written).
Requires a seed rebuild + `bin/simple` redeploy to verify — out of scope for
this unit per this session's "no cargo/bootstrap" constraint.

## Re-investigated 2026-08-10 (correcting a prior blanket-claim mislabel)

A prior pass in this session had mass-relabeled this doc using the incorrect
claim "the interpreter is implemented entirely under `src/compiler_rust/**`,
off-limits" as a blanket rule — false in general, since the self-hosted
tree-walk interpreter is pure Simple at `src/compiler/95.interp/*.spl` and IS
editable. Re-checked specifically for THIS bug:

- Reproduced fresh: `bin/simple run` on
  `val a = (key + 32).to_u8().to_char()` reproduces the exact error text
  `error: semantic: method 'to_char' not found on value of type i64 in nested
  call context` on the currently deployed seed binary
  (`bin/release/x86_64-unknown-linux-gnu/simple`, seed banner confirmed).
- `/usr/bin/grep -n "nested call context"
  src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs` —
  hit at line 855 (`"method '{}' not found on value of type {} in nested call
  context"`), the exact source of the error string. This confirms the doc's
  cited file is real and current.
- `/usr/bin/grep -rln "nested call context" src/compiler/` — **zero hits**.
  The pure-Simple `src/compiler/95.interp/` interpreter does not implement a
  separate nested/chained-call dispatcher at all (no such error string
  exists there), so there is no editable `.spl` counterpart to add a
  primitive-receiver arm to — the only implementation reachable today is the
  seed's `method_dispatch.rs`.

Conclusion: legitimate architectural classification, correctly re-justified
by direct grep evidence (`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs:855`)
rather than a blanket assumption. The call-site workaround already landed in
`host_gui_event_router.spl` remains the correct interim mitigation. Status
unchanged: **OPEN — ARCHITECTURAL (Rust seed nested-call dispatcher, verified
2026-08-10, evidence: `method_dispatch.rs:855`)**.
