# A foreign `extern fn` of the same name blocks an imported function value (seed, LLVM)

- **Status:** verification-pending
- **Found:** 2026-11-20, riscv64 kernel native-build (`src/os/kernel/abi/syscall_shim.spl:231`)
- **Component:** Rust seed `pipeline/native_project` (`mangle.rs`, GlobalLoad/GlobalStore name resolution)
- **Repro (seed test):** `llvm_address_taken_import_survives_foreign_extern_shadow` in
  `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs`

## Symptom

```
llvm codegen: semantic: llvm global load referenced undeclared symbol `spl_shim_net_direct_socket_check`
```

## Cause (confirmed)

Arity is NOT the trigger (the 1- and 2-argument `spl_shim_net_direct_bind_check` /
`_listener_check` are affected too; only the first error per file is reported).
The trigger is that all five failing names are ALSO declared `extern fn` in
`src/os/services/netstack/netstack_init.spl`.

1. `imports.rs` registers `Node::Extern` as the identity binding `name -> name`;
   for an ambiguous bare name the project import map prefers that extern identity.
2. `mangle.rs` builds `known_mangled` from `import_map.values()`, so the bare
   name itself became "already mangled".
3. In the `GlobalLoad`/`GlobalStore` arm, the `known_mangled` short-circuit ran
   BEFORE the file's own `use_map`, so the explicit
   `use os.kernel.abi.syscall_shim_net.{...}` binding was never applied and the
   bare name reached LLVM, where no function or global by that name exists.

Minimal shape (fails on the pre-fix seed, both names):

```
# pkg/provider.spl
fn za_zero() -> i64: 42
fn za_one(x: i64) -> i64: x + 1
# pkg/other.spl
extern fn za_zero() -> i64
extern fn za_one(x: i64) -> i64
# main.spl
use pkg.provider.{za_zero, za_one}
fn keep() -> u64: (za_one as u64) + (za_zero as u64)
```

Removing the externs, or importing under an alias, makes it compile.

## Fix

`mangle.rs`: in the `GlobalLoad`/`GlobalStore` arm, consult this file's
`use_map` before the `known_mangled` short-circuit (a local `extern fn` still
wins). Needs a seed rebuild.

Pure Simple: `src/compiler` has no `known_mangled`-style short-circuit; not
reproduced there (the riscv64 gate uses `SIMPLE_NATIVE_BUILD_RUST=1`).
`InterpCall` has the same ordering in `mangle.rs`; it was not changed because
no call-site failure has been observed.

## Workaround in tree

`src/os/kernel/abi/syscall_shim.spl` imports the five names under `_ka_*`
aliases, tagged `WORKAROUND(extern_shadow_blocks_imported_fn_value_2026-11-20)`.
Restore the plain names once the fixed seed is deployed.
