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

## Verdict 2026-08-17: ALREADY FIXED in tree (closed on content, not on SHA)

The cheap local fix named below has already landed in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_render_session.spl`. The arm
binding is now `retained_manager`, not `retained`, and carries an in-source note
naming this exact defect:

```
348	            # NOTE: the arm binding is deliberately NOT named `retained` —
350	            # same-named live outer (here the retained boxes above), which made
355	                Some(retained_manager):
356	                    if retained_manager.generation == snapshot.document_generation:
357	                        retained_manager
```

The live outer `retained` (line 335) is still read unshadowed afterwards at lines
378, 391, 395 and 401, and `result.hit_index.boxes.bx` at line 476 is the
intended field access, not the symptom.

Scope note: this closes the *render-session* row only. The underlying
**interpreter match-arm binding leak** family fix is NOT claimed here — it was
avoided, not repaired, and remains a live trap for any other same-named arm
binding over a live outer.

## Fix directions

Either rename the arm binding (cheap, local, unblocks multi-render sessions
now) or fix the interpreter's arm-binding scope leak (family fix; several
prior instances). Renaming in `simple_web_render_session.spl` should be done
regardless — same-named arm bindings over live outers are a known trap.

## Triage 2026-08-17 (lane m7c_lib_async) — LIVE, root cause outside src/lib

`.boxes.bx` is still read at `simple_web_render_session.spl:476`
(`self.counters.retained_box_count = result.hit_index.boxes.bx.len().to_i64()`),
exactly as this doc describes, and no guard or restructure has been added.
The defect is the interpreter's match-arm binding leaking over a same-named
outer variable — a `src/compiler_rust/**` fix, out of this lane's file scope.
Confirmed LIVE by content; not patched here.
