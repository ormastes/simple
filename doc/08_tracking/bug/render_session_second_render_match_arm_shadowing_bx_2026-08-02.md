# Second full-layout render on one SimpleWebRenderSession dies: "WebLayoutManager has no field bx"
## Closed 2026-09-16 — ... one session (documented in-spec). ## Fix directions Either rename the arm binding (cheap,

## Re-verification 2026-11-25 (p2w4-ac lane, release/1.0.0)

The cheap fix direction ("rename the arm binding") is landed in current
source. `src/lib/gc_async_mut/gpu/browser_engine/simple_web_render_session.spl:355`
now binds the match arm as `Some(retained_manager):` — no longer the
same-named `retained` — and carries an explicit NOTE (:348-350) citing this
exact bug ("the arm binding is deliberately NOT named `retained`"). The outer
`retained` local (:335) is untouched by the arm. Verified by code inspection;
a live two-render repro under the interpreter is blocked on this host by the
known seed rejection of `@representation_boundary` at release/1.0.0 HEAD, so
no new `Results:` line was obtained. The family-level interpreter match-arm
scope leak remains a separate, known issue. Status unchanged: CLOSED (local
fix landed).

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Date:** 2026-08-02 · **Severity:** medium · **Area:** browser_engine render session / interpreter match-arm binding

## Symptom

Rendering twice through the SAME `SimpleWebRenderSession` (first render OK,
then mutate the snapshot and render again) fails under the tree-walk
interpreter with `WebLayoutManager has no field bx`.

## Root cause (isolated during showcase spec work, 2026-08-02)

In `src/lib/gc_async_mut/gpu/browser_engine/simple_web_render_session.spl`, a
`case Some(retained):` match arm binds `retained` and the binding LEAKS over
the same-named outer variable after the arm (the known interpreter match-arm
binding leak family — see
`doc/08_tracking/bug/` interp match-arm notes / memory
`interp_match_arm_binding_leaks_into_same_named_param`). On the second render
the leaked binding holds a `WebLayoutManager` where later code expects the
retained layout box struct (field `bx`), so field access explodes.

## Workaround in tree

`test/03_system/gui/web_showcase_full_gpu_offload_spec.spl` verifies
mutation-sensitivity across two independent sessions instead of two renders
on one session (documented in-spec).

## Fix directions

Either rename the arm binding (cheap, local, unblocks multi-render sessions
now) or fix the interpreter's arm-binding scope leak (family fix; several
prior instances). Renaming in `simple_web_render_session.spl` should be done
regardless — same-named arm bindings over live outers are a known trap.

