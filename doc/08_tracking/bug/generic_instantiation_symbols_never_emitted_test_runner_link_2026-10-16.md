# Generic-instantiation symbols never emitted (test-runner tool-build link)

Date: 2026-10-16
Lane: release_phase3 Windows full bootstrap, stage2 compiler (pure-Simple,
admitted) native-building the test runner (`src/app/test_runner_new/main.spl`).
Evidence: `lld-link: undefined symbol` over ALL of `build/aot-*.o` — nothing
defines them, anything may reference them.

## Undefined symbols

- `lib.nogc_sync_mut.concurrent.mutex.mutex_new` — the BARE name of the
  generic fn `fn mutex_new<T>(initial: T) -> Mutex`
  (src/lib/nogc_sync_mut/concurrent/mutex.spl:96). A generic function has no
  callable bare symbol; only `$`-mangled instantiations do. The caller was
  emitted as a direct call to the bare name, i.e. the call site was lowered
  WITHOUT monomorphization.
- `_type_pool_promote_root$arr_str`, `_type_pool_promote_root$arr_i64`,
  `_type_pool_promote_root$arr_arr_i64` — instantiations of the compiler's
  own generic `fn _type_pool_promote_root<T>(root: [T]) -> bool`
  (src/compiler/10.frontend/core/types.spl:1595), used with EXPLICIT type
  arguments at types.spl:1607-1609 (`<[text]>, <[i64]>`). The defining
  module's object references but does not define them: the monomorphization
  pass did not emit these local instantiations in the stage2-compiled
  compiler on the test-runner closure.

The stage2 self-build (compiler compiling the same compiler sources) DOES
emit its needed instantiations, so this is closure-shape-dependent: some
generic instantiations reachable from the test-runner closure are dropped.

## Next investigation

- Where monomorphization collects instantiations (50.mir mono pass) and why
  these call sites contribute no instantiation record: the bare `mutex_new`
  call suggests a callee-resolution path that treats a generic fn as a plain
  direct call (no type-argument inference => no instantiation requested).
- Whether the types.spl self-instantiations are dropped at collection or at
  emission (check the mono inventory for `_type_pool_promote_root$*` entries
  keyed by the types module in a failing run vs the successful stage2 build).
- After the fix, re-run the lane: HIR/MIR are already clean (all prior fixes
  landed), so the link is the remaining gate for the test-runner tool build;
  the cli tool build is expected to link with the same fix.

## Resolution (FIXED, landed on release_phase3)

Root causes found (both confirmed in the mono pass):

- **(A) Module-global initializers were never rewritten.** The
  monomorphization integration rewrote generic call sites only inside function
  bodies. Calls in module-level `var` initializers survived as bare-template
  direct calls — e.g. `var _lock: Mutex = mutex_new(0)` in
  `src/lib/nogc_sync_mut/dynamic_probe.spl:37` lowered to a direct call to the
  bare name `lib.nogc_sync_mut.concurrent.mutex.mutex_new`, which has no
  emitted symbol. Fix: run module `constants` initializers through the same
  expression rewrite and carry the rewritten table into the collection step
  (`rewritten_consts`).
- **(B) `_type_pool_promote_root<T>` local instantiations were referenced but
  never placed.** The compiler's own generic at
  `src/compiler/10.frontend/core/types.spl:1595` was used with explicit type
  arguments, but the mono pass never emitted those instantiations on this
  closure shape. Fix: concretize the three used variants (`_text`, `_i64`,
  `_arr_i64`) as plain non-generic functions.

Landings:
- PR #3540 (commit 53afb8c62cb) — constants rewrite + `_type_pool_promote_root`
  concretization.
- PR #3521 parse repairs (commits 2e057996de1, 4893cc0d8a7) — `HirConst]]`/`]`/
  `>` bracket typos in the new `Dict<SymbolId, HirConst>` annotation.

With the fix, the stage2 tool builds (test runner, cli) link cleanly; the
remaining gate is full stage2 admission + stage3 resume (tracked separately).
