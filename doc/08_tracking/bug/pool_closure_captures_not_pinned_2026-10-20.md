# Pool-retained closure: captured transient heap objects are not pinned

- **Date:** 2026-10-20
- **Status:** open
- **Found by:** Opus review of the pool closure-retention fix (bug doc
  `native_imported_fn_value_null_call_2026-10-20.md` section 3a)

`rt_closure_retain` pins the closure object itself. Scope end then defers its free, and
the last `rt_closure_release` frees it. The closure's captures are not pinned. A
capture that is a heap object (string, array, dict, enum, boxed float/int) allocated in
the same transient scope is still freed when that scope ends. The pool task then reads
a dangling tagged handle through `rt_closure_get_capture`.

Most reads go through the registry check and degrade to nil, which gives a wrong value.
After the address is reused, the read is a real use-after-free.

Affected: `runtime_native.c` (`rt_core_reclaim_transient_immortal`) and
`src/compiler_rust/runtime/src/value/collections.rs` (`rt_transient_array_scope_end`).

Safe today: inline (int/bool) captures, and captures created outside any transient
scope (immortal).

Fix options:
1. Fail closed at submit. `rt_closure_retain` refuses (returns 0, so submit returns -3)
   when any capture is a heap object owned by the submitter's live transient scope.
2. Pin the reachable capture graph, as `rt_transient_heap_promote` walks it, and defer
   those frees with the closure.
