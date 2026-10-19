# Stage 3 closure promote walks the full `_bootstrap_fn_*` registry per module (2026-10-20)

**Symptom.** After #3919 (closure modules lowered in a transient scope) memory per
module dropped 36 MB -> 2.6 MB, but the closure step slowed from ~700 to ~70-150
modules/min (s3diag15: ~0.7-0.8 s/module, mildly growing over ~760 modules).

**Cause.** `bootstrap_fn_registries_promote` promoted each `_bootstrap_fn_*` Dict
wholesale. `rt_transient_heap_promote` walks every entry of a persistent dict
(persistence cannot stop a walk without a write barrier), so each module re-walked
the whole accumulated registry: O(modules x registry).

**Fix.** Dict handles predate the scope and bucket storage is plain calloc, so an
in-scope write adds only transient keys/values. Every write path in
`mir_data.spl` journals them; promotion adopts the journal plus any registry whose
handle a rebuild/reset replaced in scope. A one-time wholesale adoption runs on
the first promotion per process. Spec:
`test/01_unit/compiler/mir/bootstrap_fn_registry_delta_promote_spec.spl` (equivalence,
per-module root count bounded, static journal coverage; red on the old code).

**Open.** The owner promote (`promote_transient_owner`) also walks roots that grow
across modules (composite/struct layout dicts, ambient global maps). That is not
measured yet. Run Stage 2 with `SIMPLE_MIR_SECTION_PROFILE_FILE=<path>`. The new
`s4_promote_mir_registries` / `s4_promote_fn_registries` marks split the old
`s4_promote_registries` section so each cost shows up on its own.
