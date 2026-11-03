# nogc_async_mut specs pin lib functions that do not exist (or have no rt_ backing)

Date: 2026-09-16
Status: OPEN

## 2026-11-03 partial repair: non-inline multicore submission

The missing `multicore_green_try_spawn` facade is implemented using the existing
runtime pool submission boundary. It submits once, never calls the closure on
rejection, and returns a rejected handle with no native task and no inline
completion. `ran_inline_fallback()` now requires an actual inline completion;
joining a rejected handle fails explicitly instead of inventing a zero result.
Ordinary `multicore_green_spawn` keeps its existing inline fallback behavior.

The focused contract spec covers rejected and inline handle states and actual
runtime submission. A typed submitter boundary shared by production and tests
allows zero/negative rejection and positive acceptance to be injected. A
side-effecting task and submit-call counts detect forbidden inline execution
and repeated submission. A separate rejected-join process fixture must reach
its entry marker, fail with the intended panic, and never print its post-join
marker; `check-multicore-green-try-spawn.shs` collects both results.
Execution is **TEST_BLOCKED**: the canonical
`bin/release/<triple>/simple` self-hosted runtime is absent; `bin/simple.exe` is
the Rust seed and is not an authorized verification substitute. Authored tests
are not a PASS. Provider rejection and accepted task execution still require
self-hosted runtime evidence. The other missing modules/functions and ArcBox
provider obligations below remain open; this umbrella bug is not resolved.

## Observed

Worklist specs fail on symbols with no implementation anywhere in `src/lib`
(or with externs lacking runtime backing):

- `concurrent/multicore_green_try_spawn_contract_spec.spl` — `semantic: function 'multicore_green_try_spawn' not found`.
- `http_server/tls_record_capability_spec.spl` — `tls_record_path_admits_min_version` missing.
- `io/driver_write_completion_spec.spl` — `io_write_completion_has_progress_v1` missing.
- `quic/quic_udp_initial_spec.spl` — `build_unprotected_initial_shape` missing.
- `sosix/posix_spec.spl` — `unknown extern function rt_fd_pread` (declared, no runtime backing).

## Impact

The five specs cannot execute; the contracts they pin (green-thread try-spawn
semantics, TLS record floor admission, io_uring write-completion progress,
QUIC initial-packet shape, positional pread) have no runnable implementation
to verify against.

## Expectation

Each named function exists in `src/lib` with the semantics its spec documents,
and `rt_fd_pread` has a real runtime implementation.

## Unblock condition

Implement the four missing lib functions and back `rt_fd_pread` in the runtime
(or retire the specs with owner sign-off). Not spec-side fixable.

## 2026-10-21 follow-up: ArcBox atomic weak acquisition

The noGC sync and async `rc.spl` modules still depend on interpreter-owned
`arc_box_*` operations. Their concrete provider is
`src/compiler_rust/compiler/src/interpreter_extern/rc.rs`, registered in
`interpreter_extern/mod.rs`. No matching native C or Simple-core ArcBox
provider was found. This is distinct from the `rt_shared_*` object ABI.

The provider layout is `AtomicUsize strong` at offset zero, `AtomicUsize weak`
at `sizeof(AtomicUsize)`, and interpreter `Value` at twice that size. Its
load plus increment operations cannot implement atomic weak acquisition:
final strong release may occur between them and the increment resurrects a
dead payload. Existing native `rt_par_atomic_cmpxchg_i64` accepts a raw aligned
64-bit cell and returns its previous value; it has no matching interpreter
handler and is not a portable substitute for this target-sized ArcBox layout.
The registered-handle `rt_atomic_int_compare_exchange` ABI is also incompatible.

Required provider contract before implementing `Weak.upgrade_arc() -> Arc?`:

- An ArcBox-owned `try_inc_strong` operation must compare-exchange a nonzero
  count to count + 1, rejecting zero and the chosen maximum count before
  addition. Successful acquisition needs acquire ordering; contention must
  retry against the observed count without resurrecting zero.
- Return exactly one releasable Arc owner on success. A compatibility copied
  i64 operation must acquire, copy, then release that temporary owner rather
  than leak its count or read after destruction.
- Keep one implicit weak reference while strong ownership exists. Final
  strong release destroys the payload before releasing that implicit weak;
  only the final weak decrement frees the control block. This prevents the
  current independent final-strong/final-weak free checks from racing into a
  double free. Public weak counts exclude the implicit reference while live.
- Supply actual native and interpreter providers with their own verified
  layout/allocator contracts; the interpreter `Value` payload must not be
  reinterpreted as a native machine word.

The existing typed single-threaded `upgrade_rc()` repair does not qualify Arc.
No new Arc API, fabricated extern, hardcoded failure, Rust/C implementation,
build, or test execution was introduced in this follow-up. This lane is frozen
pending the provider implementation; authored Rc tests remain unexecuted.
