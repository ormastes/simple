# Bug: `me`-impl → `me`-free-function delegator drops field reassignments

**Date:** 2026-04-28
**Severity:** medium — blocks legitimate dedup refactors
**Discovered by:** Phase-5 cluster A1 of `/dev do semantic duplication remove` pipeline
**Detail:** see `.sstack/semantic-dup-removal/A1_blocker.md`

## Symptom

When an `impl me` block delegates to a `me` free function and the free function reassigns fields on `self`:

```spl
class Loader:
  modules: Dict<text, Module>
  global_symbols: Dict<text, Symbol>

impl me Loader:
  fn unload(self, path: text):
    moduleloader_unload(self, path)   # one-line delegator

me fn moduleloader_unload(self: Loader, path: text):
  self.modules = self.modules.without(path)        # <-- DROPS in caller
  self.global_symbols = self.global_symbols.without_owner(path)  # DROPS
```

The reassignments inside `moduleloader_unload` do **not** propagate back to the caller's `self` after the impl-method returns. Tests that observe `self.modules.contains(path)` post-delegate find the entry still present.

## Why "load" works but "unload" doesn't

`moduleloader_load` only uses **in-place** mutation: `self.modules.set(path, mod)`. The dict object itself is shared by reference, so the mutation is visible.

`moduleloader_unload` uses **field reassignment**: `self.modules = self.modules.without(path)`. The new dict is bound to the local `self` inside the free function but never written back to the caller.

## Reproduction

`src/compiler/99.loader/module_loader.spl` already has both shapes:

- `moduleloader_load` — in-place style, delegation works
- `moduleloader_unload` — reassignment style, delegation breaks

A1 attempted both `moduleloader_unload(self, path)` and `self.moduleloader_unload(path)` — same failure.

## Test evidence

```
Original me unload body (38-line dup):  22/22 pass, 101ms
me unload → moduleloader_unload(self,path):  16/22 pass (6 field-reassign asserts fail)
me unload → self.moduleloader_unload(path):  16/22 pass (same 6 asserts fail)
```

Spec: `test/unit/compiler/loader/module_loader_spec.spl` (the 9 it-blocks added in Phase 4).

## Fix options

1. **Compiler: pass `self` by mutable reference in `me` free functions** — make field reassignment write through. Likely the right answer; matches how `me`-impl methods already work.
2. **Compiler: forbid field reassignment inside `me` free functions** — diagnostic at parse/HIR. Avoids silent drop, forces explicit return-and-rebind.
3. **Workaround at call site:** `me unload` returns the new state and the impl caller rebinds — not a one-line delegator anymore, partially defeats the dedup.

Option 1 is the only one that actually unblocks A1.

## Impact on dedup pipeline

A1 marked **deferred**, not abandoned. Pipeline proceeds with B1, D1, C1+C2 (none of which depend on this semantics).
