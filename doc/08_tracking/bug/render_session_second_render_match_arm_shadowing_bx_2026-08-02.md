# Second full-layout render on one SimpleWebRenderSession dies: "WebLayoutManager has no field bx"

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
