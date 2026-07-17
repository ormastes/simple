# `arr[i].field = value` rejected as invalid assignment target

Date: 2026-07-11
Status: RESOLVED (triage-confirmed 2026-07-17: selector lane reproduced fix in current source via bootstrap-seed run + git log -S; call-site workarounds can be unwound)
Severity: P3 — language ergonomics gap, not a functional blocker

## Reproducer

```text
src/os/compositor/host_compositor_entry.spl:707 (pre-fix)
self.windows[j].focused = self.windows[j].id == window_id

error: semantic: invalid assignment: field assignment requires identifier
or simple nested field access as object
```

Assigning to a field of an array/list element reached via index —
`some_array[i].field = value` — is not accepted by the assignment-target
check. Only "identifier or simple nested field access" objects are allowed
on the left of a field assignment, and an index expression (`arr[i]`) does
not qualify even though a plain field chain (`a.b.c`) does.

## Workaround (used at every call site so far)

Copy the indexed element into a local `var`, mutate the local's field(s),
then write the local back to the array slot:

```text
var w = self.windows[j]
w.focused = w.id == window_id
self.windows[j] = w
```

This is the existing idiom already used elsewhere in
`host_compositor_entry.spl` (e.g. `maximize_window`/`restore_window`,
lines ~692-704 and ~714-723 before this fix) — the fix at line 707 and in
`apply_wm_action` (lines ~734-739) just extended the same idiom to the two
remaining raw `self.windows[idx].field = ...` occurrences, which were the
compile-error root cause blocking
`test/03_system/app/ui/feature/shared_wm_renderer_unification_spec.spl` and
`test/03_system/check/wm_multiapp_taskbar_spec.spl`.

## Impact

Every array-of-struct mutation site in the codebase needs the 3-line
copy/mutate/store-back workaround instead of the natural one-liner. This is
a recurring paper-cut (this file alone had 2 occurrences across 6 lines)
and increases the chance of forgetting the store-back line, which would
silently no-op the mutation.

## Follow-Up

Consider extending the assignment-target check to accept
`<expr>[<index>].<field> = value` by desugaring it internally to the
same copy/mutate/store-back sequence at compile time (get element by
index → mutate field on the temporary → index-assign back), matching how
`<identifier>.<field> = value` already works. Fix in the pure-Simple
compiler (semantic assignment-target validation / lowering), not the Rust
seed.
