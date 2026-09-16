---
id: enum_pattern_match_optional_value_silent_fallthrough_2026-07-20
status: OPEN
severity: medium
discovered: 2026-07-20
discovered_by: SPEC-REPAIR lane (test/01_unit/app/ui.browser/input_translation_spec.spl repair)
related: src/app/ui.browser/event_bridge.spl
related: test/01_unit/app/ui.browser/input_translation_spec.spl
related: doc/08_tracking/bug/interp_dict_get_option_match_never_matches_2026-07-05.md
---

# `match ev:` with enum-constructor field-binding arms silently never matches when `ev` is `T?` (Optional), not `T`

## Summary

When a function returns an Optional-wrapped enum (`UIEvent?`, i.e. `Option<UIEvent>`)
and the caller pattern-matches the raw Optional value directly against enum
constructor patterns that carry field bindings, the field-binding arms **never
match** — even when the underlying value genuinely is that variant with those
exact field values. Execution silently falls through to the wildcard `_` arm
every time, with no compile error, no runtime error, and no warning:

```simple
fn translate_mouse_event(x: i32, y: i32, button: i32, action: text) -> UIEvent?:
    ...
    return UIEvent.TouchPress(x: x, y: y)   # left press

# Caller — BUG: the TouchPress arm is NEVER taken, even for a real left press
val ev = translate_mouse_event(120, 240, 0, "press")   # ev: UIEvent?
match ev:
    UIEvent.TouchPress(x, y) =>
        use(x, y)                # unreachable
    _ =>
        handle_unexpected()      # ALWAYS taken instead
```

Only the literal `nil` pattern arm matches correctly against the Optional
value (e.g. `match ev: nil => ... _ => ...` correctly detects the nil case).
Any arm that both (a) names a specific enum variant and (b) binds that
variant's fields fails to narrow through the `T?` wrapper and falls through
to `_`.

## Minimal repro (proven via probe, not just observed)

Probed directly with `bin/simple run` against the real, independently-verified
`translate_mouse_event` (see Evidence below) — confirmed the *underlying
function* returns the exactly-expected `UIEvent` variant for every case;
matching that same value works correctly the moment it is unwrapped first:

```simple
val raw = translate_mouse_event(120, 240, 0, "press")   # raw: UIEvent?

# BUG SHAPE — never matches the TouchPress arm:
match raw:
    UIEvent.TouchPress(x, y) => print "matched"   # never printed
    _ => print "fell through"                     # always printed

# WORKING SHAPE — unwrap the Optional first, then match the bare T:
if val ev = raw.?:
    match ev:
        UIEvent.TouchPress(x, y) => print "matched"   # printed correctly
        _ => print "fell through"
else:
    print "raw was nil"
```

## Evidence

`test/01_unit/app/ui.browser/input_translation_spec.spl` (landed at
`09a71feb5c7` as part of the 2026-07-20 hardening campaign) asserted directly
on the `UIEvent?` return of `translate_mouse_event` with
`match ev: UIEvent.TouchPress(x, y) => ... _ => expect(false).to_be_true()`
style arms. 7 of 9 examples failed — every case that expected a specific
non-nil variant (left press/release, middle press/release, right
press/release, move) fell through to the `expect(false)` arm and failed; only
the 2 cases that expected `nil` (unknown button, unknown action) passed,
because those matched the literal `nil` arm correctly.

A standalone probe (`bin/simple run`) that unwraps `raw.?` first via
`if val ev = raw.?:` before matching, run against the identical
`translate_mouse_event` calls for all 9 cases, printed the exact expected
variant and field values for every non-nil case, and correctly took the
nil/else branch for both nil cases — proving `event_bridge.spl`'s translation
logic is correct and the defect is in Optional-wrapped enum pattern matching,
not in the production code under test. Probe output (all 9 cases correct):

```
== left press ==       -> MATCHED TouchPress(x=120, y=240)
== left release ==     -> MATCHED TouchRelease(x=120, y=240)
== middle press ==     -> MATCHED MouseEvent(x=50, y=60, button=middle, kind=down)
== middle release ==   -> MATCHED MouseEvent(x=50, y=60, button=middle, kind=up)
== right press ==      -> MATCHED MouseEvent(x=10, y=20, button=right, kind=down)
== right release ==    -> MATCHED MouseEvent(x=10, y=20, button=right, kind=up)
== move (button=0) ==  -> MATCHED TouchMove(x=5, y=6)
== unknown button (3) press ==  -> raw == nil (correctly no match)
== unknown action (drag) ==     -> raw == nil (correctly no match)
```

## Fix applied to the spec (workaround, not a compiler fix)

The spec was rewritten to unwrap the `UIEvent?` via `if val ev = raw.?:`
before matching field-binding arms against the now-bare `UIEvent`, with a
real failing assertion (`fail_test("expected ..., got ...")`) naming the
expected variant in both the unwrapped fallthrough arm and the `else`
(nil-when-not-expected) branch, replacing the `expect(false).to_be_true()`
anti-pattern. The two nil-returning cases now assert `raw == nil` directly
(equality comparison, not pattern-match narrowing, so it is unaffected by
this defect). All 9 examples pass after the rewrite; `event_bridge.spl` was
**not** changed — its translation logic was independently proven correct.

## Impact

Any code — spec or production — that pattern-matches a `T?`-typed value
directly against enum constructor patterns with field bindings silently
takes the wrong branch instead of erroring. This is a correctness footgun
of the same family as
`interp_dict_get_option_match_never_matches_2026-07-05.md` (Dict.get()
result matched as `Some(x)`) but for the general case of *any* Optional
enum value matched with field-binding constructor patterns — it made 7 of
9 spec examples in `input_translation_spec.spl` silently fail (they still
reported as failures, not false-positives, but for the wrong reason: a
match defect, not a translation defect) and would silently produce wrong
*runtime* behavior (never a compile/type error) in non-test code that relies
on this shape.

## Scope

Pattern-match semantics for enum constructor patterns (with field bindings)
against `Option<Enum>`-typed (`T?`) scrutinees; not specific to
`UIEvent`/`event_bridge.spl`. The correct, currently-required idiom is to
narrow the Optional first (`if val ev = raw.?:` / `if val ev = raw:`) and
match the bare value inside, exactly as documented for `if val` pattern
binding in `doc/07_guide/quick_reference/syntax_quick_reference.md`.

## Suggested follow-up

1. Either make `match` auto-narrow a `T?` scrutinee against enum-constructor
   patterns (treating `nil` as an implicit `_`-only match and non-nil as the
   unwrapped `T`), or make it a compile-time type error to match a `T?`
   value against bare `T` variant patterns — the current silent fallthrough
   is the worst of both options.
2. Grep `test/01_unit/**` and `src/**` for `match <expr>:` where `<expr>`'s
   static type is a `?`-suffixed enum and at least one arm is a variant
   constructor with field bindings — other call sites likely carry the same
   masked defect (same class as the `Dict.get()` bug's suggested follow-up).
3. Add a regression spec directly targeting this shape (Optional-enum matched
   with field-binding constructor arms) so a future compiler fix has a red
   test to turn green, and so this doesn't regress unnoticed again.
