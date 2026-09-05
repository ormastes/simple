# Interpreter: `me` method called through a `Trait?`-typed module slot re-boxes the receiver per call, losing field mutations

**Date:** 2026-07-07
**Severity:** medium — silently drops state mutations on any object stored
behind a `Trait?`-typed module-level `var` and invoked via a trait-typed
call; found while wiring `_wm_background_image_provider:
BackgroundImageProvider?` in `src/lib/common/ui/window_scene.spl`.
**Status:** OPEN — workaround is the established module-level-`var`-state
convention (matches the existing `_*_compositor_override_*` pattern), not a
fix.

## Symptom

A `me` (mutating) trait method invoked through a module-level slot typed
`SomeTrait?` gets a **freshly re-boxed copy of the receiver on every call**
when the slot is *re-read* between calls, so field mutations made inside the
method body do not persist to the next call.

**Repro nuance — this is not simple bind-once-call-twice:**

- Binding the trait value into a local once and calling the mutating method
  twice on that SAME local binding works fine — mutations persist call to
  call.
- The bug only reproduces when each call independently **re-reads the
  module-level slot** (`_wm_background_image_provider.resolve(...)` where
  the global `var` is read fresh each time), e.g. three sequential calls each
  doing `if provider is Some(p): p.mutate(); a = p.field` yield `a=1 b=1 c=1`
  instead of the expected accumulating `a=1 b=2 c=3` — every call sees the
  object in its initial state, as if a fresh copy were unboxed from the
  `Some(...)` each time the slot is read.

## Why it matters

Any provider/strategy object registered once into a `Trait?`-typed module
slot and expected to accumulate state across calls (caches, counters,
content-hash memoization) will silently lose that state if the call site
re-reads the slot per invocation — which is the natural way to write such
code (`_provider.resolve(...)` inline, not `let p = _provider; p.resolve()`
held across calls). Same interpreter-representation family as the Dict-value-
copy-on-read class of bugs already tracked elsewhere (boxed/optional values
get copied rather than referenced on each unwrap).

## Workaround applied (established convention, reused here)

`background_image_provider.spl`'s content-hash cache and stale-serve state
live in **module-level `var`s** (mirroring the pre-existing
`_*_compositor_override_*` pattern already used elsewhere in the compositor
code for exactly this reason), not as fields on the provider object reached
through the `Trait?` slot. State mutated via module-level `var` assignment
persists correctly across calls; state mutated via `me` methods on the
trait-slot-held object does not.

## Next step

Find where a `Some(x)`-wrapped trait object is unwrapped at each `Optional`
slot read in the interpreter (likely the same Optional/Result value-copy
path implicated in
`interp_fs_class_statics_return_result_despite_optional_types_2026-07-07.md`)
and confirm whether the unwrap clones the boxed value instead of returning a
shared reference/handle. A minimal regression repro: module-level
`var slot: SomeTrait? = nil`; register an object with a mutable counter
field; call a `me`-mutating method through `slot` (re-reading the module var
each time, not a locally-held binding) 3× in sequence; assert the counter
accumulates rather than resetting.
