# Interpreter: `return` inside if-block under or-pattern match arm is swallowed

**Date:** 2026-06-13
**Severity:** medium (silent wrong value, no error)
**Status:** open — workaround applied at the one known live site

## Symptom

A method whose `match` uses an or-pattern arm (`A | B:`) with a nested `if` +
`return` falls through to the post-match `return` even when the arm matched and
the `if` condition was true. No error; the function returns the wrong value.

## Repro (was live in src/lib/common/ui/profile.spl ProfileSet.resolve)

```simple
fn resolve(orientation: Orientation) -> WidgetNode:
    match orientation:
        Orientation.Landscape | Orientation.Square:
            if self.landscape_root != nil:
                return self.landscape_root      # swallowed — falls through
        Orientation.Portrait:
            if self.portrait_root != nil:
                return self.portrait_root       # swallowed — falls through
    return self.default_root                    # always taken
```

Observed via `test/01_unit/app/ui/profile_spec.spl` ("resolves landscape
profile when set" / "resolves portrait profile when set" / "resolves Square as
Landscape" — failed with "expected default to equal landscape" for months;
pre-existing before the 2026-06 mobile-gui-platform work).

## Workaround applied

Rewrote `ProfileSet.resolve` as plain `if`/`return` chains (profile.spl) —
spec went 51/54 → 54/54. `ProfileSet.has_profile` uses the same or-pattern
shape but returns the match arm value as an expression (no early `return`
inside `if`), which appears unaffected — not rewritten.

## Suspected root cause

Match-arm lowering for or-patterns discards the early-`return` control flow of
statements nested under the arm (related family: doc/08_tracking/bug/interp_*
receiver/nested-push 2026-05-30 codegen gotchas).

## Next step

Minimal standalone repro spec + fix in interpreter match lowering; then revert
the profile.spl workaround to the match form.
