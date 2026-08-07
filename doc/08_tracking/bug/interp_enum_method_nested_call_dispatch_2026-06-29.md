# Interp: enum method not found in nested/chained call context

**Status:** FIXED in seed source; pending seed rebuild + deploy to default `bin/simple`
**Found:** 2026-06-29 (noise sweep — riscv64 target spec)
**Area:** interpreter / method dispatch (Rust seed)

## Symptom

Calling a method on an enum value that is itself the result of a nested call —
e.g. `t.arch().to_string()` where `arch()` returns an enum — fails in
chained-call position:

```
semantic: method 'to_string' not found on value of type enum in nested call context
```

The same chain works in a plain function body (`bin/simple run` main()); it only
fails when evaluated through the nested/chained-call dispatcher (observed in an
`it` block under `bin/simple test`). Repro:

```simple
enum Color:
    Red
    Green
    fn label() -> text:
        match self:
            Red: "red"
            Green: "green"
class Box:
    pass_dn
impl Box:
    static fn create() -> Box: Box()
    fn color() -> Color: Color.Green
# b.color().label() -> errored in nested position
```

Surfaced as `target_riscv64_spec.spl` "reports RiscV64 architecture"
(`t.arch().to_string()`).

## Root cause

`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs` (the
chained/nested-call dispatcher) handled `Value::Object` (class methods, impl,
trait, UFCS) but had no arm for `Value::Enum`, so enum receivers fell through to
the generic "method not found … in nested call context" error. The primary
method evaluator (`interpreter_method/mod.rs`) handles enum receivers; the
nested dispatcher did not mirror it.

## Fix

Added a `Value::Enum { enum_name, .. }` arm to the nested dispatcher that mirrors
the primary path: look up the method in the enum's impl blocks, then in the enum
body via the local `enums` map and `GLOBAL_ENUMS` (cross-module enums), and call
it with the enum value bound as `self`.

## Verification

Regression test `bdd_enum_method_in_nested_call_context` in
`src/compiler_rust/driver/tests/interpreter_bdd.rs`; end-to-end the
`target_riscv64_spec.spl` "reports RiscV64 architecture" example passes with the
rebuilt binary.

## Deploy gate

Seed-side fix; effective for `bin/simple` after seed rebuild + deploy. Combined
with the falsy-call matcher fix
(`sspec_matcher_falsy_call_result_false_red_2026-06-29.md`), the riscv64 target
spec goes from 2 failures to 0.

## Further occurrence confirming still-undeployed status (2026-08-07, U4.2)

`test/01_unit/os/compositor/host_gui_event_router_spec.spl` was independently
found RED on the currently-deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, seed banner confirmed) during
U4.2 coverage-closure work: `Results: 5 total, 2 passed, 3 failed`, all 3
failures with the exact symptom text this doc documents —
`semantic: method 'get_prop' not found on value of type enum in nested call
context` (chained `session.current_tree().find_widget("name").get_prop(...)`)
and one downstream `expected subject to be truthy, got 0` caused by the same
call failing inside a boolean expression. This confirms the fix described
above is still not deployed to `bin/simple` as of 2026-08-07 — same gate as
recorded above, now with a second, independent live repro. Not fixed or
worked around as part of U4.2 (out of scope: seed rebuild forbidden by that
unit's task constraints); U4.2's own coverage-closure spec
(`host_gui_event_router_coverage_closure_spec.spl`) avoids the pattern by
using an intermediate `val` for every multi-step chain, and its own line-%
"before" baseline for `host_gui_event_router.spl` is reported as `0%` for
this reason — see
`doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md`'s U4.2
addendum.
