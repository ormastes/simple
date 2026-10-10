# `mutex_lock` return-only generic requires an explicit call type

## Evidence

The Phase 3 native-build receipt at
`/dev/shm/simple-phase3-1000-object-attempt-20261010/execution-receipt.json`
records E-MONO-032 and E-MONO-033 for rows 2 and 3, compiling
`src/app/build/targets/action_identity.spl` and
`src/app/build/targets/artifact_receipt.spl`. Both fail at
`src/lib/nogc_sync_mut/rt_hal/boundary.spl:138:16` because the call has no
explicit type argument and its argument types do not determine the generic
result type.

The declaration in `src/lib/nogc_sync_mut/concurrent/mutex.spl` is
`fn mutex_lock<T>(mutex: Mutex) -> T?`. `Mutex` is not parameterized by its
stored value type, so `mutex_lock`'s only input cannot determine `T`. The
boundary lock is initialized by `mutex_new(0)` and all unlock paths restore
`0`; the supported protected value here is therefore `i64`.

## Minimal reproduction and prevention

```simple
val lock: Mutex = mutex_new(0)
val held = mutex_lock(lock)       # E-MONO-032: T appears only in the result
val held_i64 = mutex_lock<i64>(lock)  # explicit, contract-matched type
```

Keep the generic API for callers protecting arbitrary values, but provide a
type argument (or a typed result context where supported) when the protected
value cannot be inferred from an argument. The boundary call now states
`mutex_lock<i64>(owner_install_lock)` and carries an `@workaround` tag linking
this source-level finding. Standalone positive, negative, and non-sentinel text
controls are recorded in
`test/fixtures/compiler/mutex_lock_typeargs/manifest.json`; all remain
unexecuted. No compiler behavior change or native PASS is claimed by this
report.
