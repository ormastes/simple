# Stage 2 HIR worker SIGSEGV in layer_eq_registry_reset_module (2026-10-23)

## Symptom
`native-build ... src/compiler/bootstrap_admission/p2_add.spl` with the pure-Simple Stage 2
compiler: HIR shard worker SIGSEGV (rc -139), first load of `for key in layer_eq_registry_views`
in `layer_eq_registry_reset_module` <- `parser_init_with_path` <- `parse_and_build_module_with_scope_owner`
<- `frontend_parse_or_restore` <- `CompilerDriver.lower_and_check_retained_owner_impl`.
Not restore-specific: SIMPLE_FRONTEND_CACHE=0 moves the crash to the MIR shard worker; a fresh
cache (miss path) crashes/aggregate-fails too.

## Evidence (gdb, aarch64 Stage 2 binary)
1. First parse (cache restore) `reset_module` replaces the static `[]` globals with fresh scope-owned
   arrays (`views` 0x23ba5c1 -> heap).
2. Driver pauses the scope and calls `layer_eq_registry_promote_transient_owner`; all three
   `rt_transient_heap_promote` calls return 1 and `views` is the exact promoted pointer.
3. Array header is byte-identical before and after promote, and `driver_end_transient_parse_scope`
   then frees it (freelist words, later 0xfff..f8 poison).
4. Second parse calls `reset_module` and iterates the freed array: SIGSEGV.

## Root cause
`rt_transient_heap_promote` (src/compiler_rust/runtime/src/value/collections.rs) returned true for ANY
root present in the heap registry ("registered heap object = already persistent"). Scope-owned arrays
and dicts are registered too, so a root array/dict is never removed from `scope.objects` and is freed
at scope end. Struct roots work (children are walked), which hid it: only direct array/dict roots such
as module-global registries (layer_eq/effect/aspect/rt_criticality/resource) are affected.
The C twin classifies by scope ownership first and is not affected.

## Fix
No-op success only when the paused scope does not own the root; otherwise fall through to the walk.

## Status
UNVERIFIED: no rebuild possible in this lane (no cargo/bootstrap). Needs Stage 2 redeploy with the
seed runtime change, then re-run p2_add. Env workaround: none honest; SIMPLE_FRONTEND_CACHE=0 only moves the crash.
