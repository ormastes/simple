# fn-typed extern parameters: 32-bit ABI unproven (`ptr` vs 64-bit integer)

Status: open. Follows the change that lowers fn-typed parameters as
`HirTypeKind.Function -> MirTypeKind.FuncPtr -> LLVM ptr / CL_TYPE_PTR`
instead of `Any -> i64`.

## What is proven

- x86_64 (cranelift and LLVM): a generic walker with a fn-typed parameter
  native-builds and runs, with a named function and a capturing lambda.
- riscv32 LLVM IR, Simple-to-Simple only: the callback parameter is `ptr`
  under a `p:32:32` datalayout, the caller passes `ptr @mod.fn`, and the body
  calls through it (`generic_walker_fn_param_abi_spec.spl`, third case). The
  closure check widens with `ptrtoint ptr to i64`, which is well defined.

## What is not proven

Extern declarations whose native side takes the callback as a 64-bit
integer:

- `extern fn native_spawn_worker(worker_fn: fn() -> i64)`
  (`src/compiler_rust/lib/std/src/host/common/io/fs_sffi.spl:59`); the Rust
  side is `pub extern "C" fn native_spawn_worker(worker_fn: u64)`
  (`src/compiler_rust/runtime/src/value/file_io/process.rs:27`).
- `extern fn par_map(items: [Value], f: fn(Value) -> Value)`
  (`src/compiler/90.tools/sffi_gen/specs/lib_wrappers.spl:97`,
  `src/app/ffi_gen.specs/lib_wrappers.spl:97`).

On 64-bit targets `ptr` and `u64`/`int64_t` use the same register, so this is
harmless. On riscv32 / arm32 / x86 a 64-bit integer argument takes a
register pair (or stack slot), while a `ptr` takes one 32-bit register. The
callee would read a garbage high word, and every later argument would be
misaligned.

## Fix direction

Either lower a FuncPtr argument to an extern as `ptrtoint ... to i64` when
the extern's declared native type is a 64-bit integer, or change the native
prototypes to take a pointer-width type (`usize` / `uintptr_t`). Then add a
32-bit IR spec for an extern call site and a 32-bit native run.
