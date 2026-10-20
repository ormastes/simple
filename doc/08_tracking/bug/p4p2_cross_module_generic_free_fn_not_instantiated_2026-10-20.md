# Phase-2 producer leaves cross-module generic free-fn calls on the unspecialized symbol

- **Date:** 2026-10-20
- **Status:** open. A tagged source workaround is active. No root fix yet; the compiler owner needs to triage it.
- **Found by:** p4-phase2 lane, test-runner tool (`src/app/test_runner_new/main.spl`) on the llvm backend.
- **Producer:** `producer7-20261020/strict/simple-producer7-strict.exe` (release_phase3 `87b9c74ff39`).
- **Source:** origin/release_phase3 `97aa8eb9e1f` plus the lane workaround commits.

## Failure

Every object compiled. The link then failed:

```
lld-link: error: undefined symbol: lib.nogc_sync_mut.concurrent.mutex.mutex_new      (x4)
lld-link: error: undefined symbol: lib.nogc_sync_mut.concurrent.mutex.mutex_unlock   (x5)
>>> referenced by aot-....o:(lib.nogc_sync_mut.rt_hal.boundary...)
>>> referenced by aot-....o:(lib.nogc_sync_mut.mcdc.dynamic_probe...)
```

## Evidence

`llvm-nm` on the mutex module's object (`cache-llvm/s610c007.../aot-573f3d3c....o`)
shows only the non-generic functions:

```
T lib.nogc_sync_mut.concurrent.mutex.mutex_lock_gate
U rt_mutex_lock
```

`mutex_new<T>` and `mutex_unlock<T>` are generic free functions. The defining
module emits no symbol for them. The callers (`mutex_new(0)`,
`mutex_unlock(m, 0)`) were not instantiated locally; they reference the bare,
unspecialized name.

This is the same family as
`mutex_lock_return_only_generic_needs_call_type_2026-10-10`, which already added
`mutex_lock_gate`. Here the generic T IS inferable from the argument, but
specialization still did not happen.

## Workaround

Tagged `@workaround bug=p4p2_cross_module_generic_free_fn_not_instantiated_2026-10-20`.

- `src/lib/nogc_sync_mut/concurrent/mutex.spl`: adds `mutex_new_gate(i64)` and
  `mutex_unlock_gate(Mutex, i64)`. They have the same runtime contract as
  `mutex_new<i64>` and `mutex_unlock<i64>`.
- `src/lib/nogc_sync_mut/mcdc/dynamic_probe.spl` and
  `src/lib/nogc_sync_mut/rt_hal/boundary.spl` now use the gates. Both pass only
  the integer 0.

Original forms are at
`97aa8eb9e1f:src/lib/nogc_sync_mut/{mcdc/dynamic_probe.spl,rt_hal/boundary.spl}`.

Other `mutex_new(...)` callers, about 24, pass struct states. They will fail the
same way if they enter a native closure. The fix there is the compiler fix, not
more gates.

## Root fix needed

Generic free functions called from another module must be monomorphized at the
call site. Failing that, the defining module must emit the erased instance
under the referenced name. Find where cross-module generic call targets are
resolved during MIR/codegen, and why `mutex_new(0)` keeps the base name.
