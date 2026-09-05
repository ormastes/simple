# Bootstrap atomic SFFI ABI and semantics mismatch

**Date:** 2026-08-26

**Status:** Source fix implemented; not dynamically or cryptographically verified

**Owner:** bootstrap standard library / atomic runtime boundary

## Impact

`src/compiler_rust/lib/std/src/infra/atomic.spl` cannot be promoted by merely
adding `unsafe(ffi)` annotations. Its source declarations disagree with the
compiler registry and Rust provider, and several supposedly observational
operations mutate state. Calling these shapes through native code is an ABI
mis-call risk; interpreting the results can fabricate success/current values.

## Static evidence

The bootstrap declaration passes an ordering argument to load, store, swap,
fetch, flag-test, and flag-clear operations. The exact `RuntimeFuncSpec` and
`src/compiler_rust/runtime/src/value/sffi/atomic.rs` provider accept no ordering
argument and always use `SeqCst`.

`rt_atomic_int_compare_exchange` is declared with five arguments and an `i64`
result. The registry/provider accept three arguments and return `bool`. The
wrapper then decodes a nonexistent success bit and masks away the sign bit,
which cannot preserve arbitrary `i64` values.

The boolean declarations transport values/results as `i64`; the registry and
provider use the boolean/I8 ABI. `AtomicBool.compare_and_swap` is implemented
with unconditional swap, so a mismatched expected value still mutates state.

`AtomicFlag.is_set`, `is_clear`, and `summary` call test-and-set and therefore
change a clear flag to set while claiming to inspect it.

The Rust provider stores every atomic behind a global `Mutex<HashMap<...>>`.
Operations are thread-safe but are not lock-free, contrary to the module docs.
Invalid/stale handles fabricate `0` or `false`, and free is not typed or
exactly-once.

`rt_spin_loop_hint` has a Rust runtime provider but no exact native-codegen or
interpreter registration in the inspected tree.

## Required fix

1. Select the existing two-argument, provider-owned SeqCst ABI as the bootstrap
   compatibility contract; do not pass advisory ordering across SFFI.
2. Change integer compare-exchange to a semantic `bool`. Update callers to
   consume the boolean directly; do not invent a current value or add a second
   load on the contention path.
3. Use boolean ABI types for all boolean operations and add the existing
   provider compare-exchange identity to the exact registry where missing.
4. Add a non-mutating flag-load provider/registry/interpreter identity, or
   remove the observational flag APIs. Do not implement inspection with
   test-and-set.
5. Validate allocation handles once at construction. Keep ordinary operations
   one direct provider call; mark manual free and raw-handle exposure unsafe.
6. Either replace the map-backed provider with typed stable storage or describe
   it honestly as mutex-backed. Do not claim lock-free behavior without
   measurement and implementation evidence.
7. Add the spin-loop identity to exact native/interpreter registries before the
   spinlock facade can be admitted.

## Implemented source resolution

- The bootstrap raw declarations now exactly match the provider-owned SeqCst
  ABI; ordering remains a source compatibility parameter and is no longer
  transported to providers that do not accept it.
- Integer and boolean compare-exchange return real booleans. The impossible
  packed-current decoder and unconditional boolean swap workaround are gone.
- Semaphore consumers use the boolean directly, so contention still performs
  one compare-exchange and no reconstructing load.
- Flag observation uses a new `rt_atomic_flag_load` identity across C, Rust,
  interpreter, and native registry and no longer changes the flag.
- `rt_spin_loop_hint` now has exact interpreter/native registry closure and a C
  provider in addition to the Rust provider.
- C and Rust allocation handles are rejected once at construction when
  non-positive. Manual release and raw-object `AtomicRef` operations are
  explicitly unsafe.
- Module documentation now distinguishes direct C11 atomics from the Rust
  compatibility provider's mutex-protected handle maps.

The runtime provider remains unsigned and unadmitted, Rust handle operations
remain mutex/map-backed, and invalid raw handles still collapse to zero/false.
Those limitations prevent a verified-safe claim even though the source ABI and
boolean semantics are repaired.

## Performance and memory gate

The corrected success path must remain one provider call per load/store/RMW.
No per-operation hash/signature check, name lookup, wrapper allocation, retry,
or extra load is allowed. Compare-exchange contention must not acquire a second
map lock merely to reconstruct a value the ABI did not return. Measure the same
single-thread and contended operation baseline before/after once verification
is authorized; report latency, throughput, and peak allocation/RSS.

## Admission status

Unsafe and unverified. No exact artifact evidence or trusted signature is bound
to this family. Until the ABI and semantic defects above are fixed, even an
artifact signature would authenticate broken behavior rather than make it safe.
