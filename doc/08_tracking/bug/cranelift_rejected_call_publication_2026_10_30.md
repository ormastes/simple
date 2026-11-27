# Cranelift rejected calls must prevent publication

Status: implemented; isolated provider tests pass; full compiler/native producer
integration has not been rerun for this change.

The panic ABI diagnostic compiled and linked despite a rejected declaration,
missing import and zero function reference. Its explicit panic worked, but its
cast path trapped without the required panic message. Native build exit0 was
therefore insufficient evidence of clean code generation. Original log SHA256:
`548f3564d0a8351dc5c4b9e9f43424c137b17a14369d4095346b12a18e112234`, at
`/work/native-hello-diagnostic-20261030/panic-abi-probe/attempt-executable-copy/`.
The separate panic ABI correction addresses the triggering invalid signature.
This change addresses the provider's lost error state.

## Correction and ownership

The Rust Cranelift SFFI records the first declaration/import refusal or invalid
direct-call function/value handle against its live owning module. An invalid
unowned handle does not allocate failure state. No C ABI signature or return
convention changes: zero remains both the existing error sentinel and the
legitimate result of a void call. The separate module state disambiguates them. The first reason is retained for
ownership evidence; it is printed at refusal and is not replayed at finalization.

A failed module cannot finish a function, define previously finished functions,
finalize, return a JIT function pointer or emit an object. Rejected emission
leaves any pre-existing output untouched. Failed function completion drops its
borrowing builder before its backing allocation, without finalizing incomplete
IR. Free and registry reset remove failure state; independent modules retain
independent state. Existing same-module construction/publication lifecycle is
caller-serialized; the change does not add a concurrent same-module transaction
API. Failure locks are released before acquiring any other registry lock.

This is a bounded direct-call/declaration/import fix, not a claim that all other
provider refusals now propagate. Existing diagnostic helper functions still
return detailed Result errors; the public SFFI boundaries own the sticky state.

## Executed validation

Host-only owner harness `/private/tmp/astra-cranelift-latch-harness` imports the
actual repository `cranelift_sffi.rs` and its tests by path, with existing
`compiler_backfill` cfg excluding RuntimeValue wrappers. Its only local shim is
host SystemV call convention; actual Cranelift modules, builders, imports and
object emission are used. This is not a full compiler crate or Simple SSpec run.
Command:

```sh
RUSTFLAGS='--cfg compiler_backfill' CARGO_BUILD_JOBS=1 cargo test   --manifest-path /private/tmp/astra-cranelift-latch-harness/Cargo.toml   --lib -- --test-threads=1
```

Initial red: 3 tests executed, 3 failed because finalization/function completion
incorrectly succeeded. Log `/private/tmp/astra-cranelift-latch-red.log`, SHA256
`7ef33b32340c35c5099e8f08d0d47103fbc7f24aaa8c13b69809b94cc119b663`.
During positive-control development the fixture used return(value0) rather than
the dedicated void return, leaving an unfilled block; that setup error was
corrected and its intermediate abort log retained separately.

Final focused default-parallel run: 7 passed, 0 failed, 1 ignored helper,
8 unrelated tests filtered, exit0. The ignored registry-reset helper is executed
alone in a child test process by the ordinary parent test, which checks its exit
and one-test execution count. Normal tests never clear unrelated registries.
Log `/private/tmp/astra-cranelift-latch-parallel-green.log`, SHA256
`e2588f5b7d466933634dca07257c8f9238ae727596fd41ceb8230eafbc7e0ba2`.

All owner cases serially: 15 passed, 0 failed, 1 ignored helper, exit0, including
existing abort, diagnostics and owned-handle cases. Serial execution is required
by existing registry-wide abort tests, not imposed on the new normal tests.
Log `/private/tmp/astra-cranelift-latch-owner-final-v2.log`, SHA256
`6c1d07ddf57f101bba22686b9aaf87490fcc37be21e0732ac4862796041a0815`.
The new tests cover conflict/no publication, missing import/cleanup, valid void
zero and independent module success, concurrent separate-module ownership,
isolated reset, rejection of a function completed before a later module failure,
and missing direct-call argument value handles.

Full repository follow-up command (not executed here):
`cargo test -p simple-compiler --lib error_latch_tests -- --test-threads=1` from
`src/compiler_rust`, with canonical pinned toolchain/runtime prerequisites.
Native integration remains pending a source-matched producer rebuild.
