# JIT de-JITs whole stage1: `rt_native_build` + `runtime_file_rename` unresolved (2026-08-22)

**Status:** FIXED
**Class:** unresolved `Linkage::Import` de-JITs the whole module — the same
class as `jit_unresolved_rt_process_read_stdout_checked_2026-08-22.md` and
`jit_runtime_symbol_unregistered_rt_value_unbox_int_2026-08-11.md`. Two symbols,
**two different root causes**, recorded together only because they were the two
remaining blockers on the same stage1 compile.

## Symptom

```
[jit-fallback] unresolved external symbol 'rt_native_build': whole module dropped to the interpreter
[jit-fallback] unresolved external symbol 'runtime_file_rename': whole module dropped to the interpreter
```

Reproduced against seed `/mnt/data/seedperf/simple.f593e9ce8dd` with
`native-build src/app/cli/bootstrap_main.spl`. One unresolvable name fails the
whole `compile_module` (`codegen/jit.rs::first_unresolved_import`), so every
function in stage1 interprets (~100-1000x).

## Symbol 1 — `rt_native_build`: a real definition in a crate nothing can link

Not a missing implementation. `native_all/src/lib.rs:143` defines it, correctly
and completely. The problem is *where*: `native_all` is
`crate-type = ["staticlib"]`, so **no crate can depend on it** — including the
seed binary. Measured: `nm <seed> | grep -c ' T rt_native_build'` = **0**.

The layering intent was real and is preserved: `pipeline/native_project/config.rs:77-90`
already documents that `rt_native_build` "IS the native-build driver", that
there is no C body and there cannot be one, and that the bootstrap lane must
*select* the hosted archive rather than widen the core C ABI. Nothing about that
requires the definition to sit in the staticlib. Its entire dependency set
(`simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder}`,
`simple_compiler::optimizations`, `simple_runtime::value`) is in or below
`simple-compiler`.

Also note the interpreter could not stand in: `interpreter_extern/mod.rs:1607`
registers it to `cli::rt_native_build`, which is `interpreter_not_supported`.

### Fix (a: link/register the existing definition; NOT a stub)

1. **Relocated** the one definition and its helpers to
   `compiler/src/native_build_sffi.rs`. No second definition; no behaviour change.
2. `native_all` now does `pub use simple_compiler::native_build_sffi::rt_native_build;`.
   It already carries `pub use simple_compiler;`, which is exactly how the
   `rt_cranelift_*` symbols defined in `simple-compiler` are rolled into
   `libsimple_native_all.a` today — so **the staticlib's exported symbol set is
   unchanged**.
3. `RUNTIME_SYMBOL_NAMES` is generated from the runtime crate + C runtime and
   cannot list a compiler-owned symbol, and a Rust `bin` does not put its
   `#[no_mangle]` symbols in the dynamic symbol table, so `dlsym` misses too.
   Added `codegen::jit::COMPILER_OWNED_RUNTIME_SYMBOLS` /
   `compiler_owned_symbol()` — a table of **real function addresses**, published
   to `JITBuilder` and consulted by `jit_import_resolves` so the guard's answer
   and the JIT's actual resolution stay identical. A stub returning nil was
   deliberately NOT written: that is the
   `unregistered_extern_silent_nil_2026-08-01.md` defect class.

Measured after: `nm <seed> | grep -c ' T rt_native_build'` = **1**.

## Symbol 2 — `runtime_file_rename`: not a runtime symbol at all

There is nothing to define, and defining anything would have been wrong.
`runtime_file_rename` is a **local alias** created by
`src/lib/nogc_sync_mut/io/file_ops.spl:218`:

```
use std.io_runtime.{file_rename as runtime_file_rename}
```

`hir/lower/lowerer.rs::collect_flattened_import_aliases` resolves such aliases
from the flattener's import-binding markers, in two tiers: the owner-mangled
symbol, else the bare `source_name` **if it is unique in the flattened unit**.
Neither tier fired here. Only `main` is owner-mangled
(`pipeline/module_loader.rs:668-686`), so tier 1 found nothing; and the
flattened unit contains **four** `file_rename` definitions (`io_runtime.spl:424`,
`file_system/file_ops.spl:145`, `fs.spl:643`, `io/file_ops.spl:220`), so tier 2
refused as ambiguous and left the alias unresolved — becoming a
`Linkage::Import` named after the *alias*.

### Fix (b: resolve it where it belongs — HIR, not the runtime)

Added a third tier keyed on the flattener's own module-owner tag
(`tag_function_module_owner`): if exactly one function named `source_name` is
tagged with the marker's `source_owner`, bind the bare name. This is not a
guess. The **non-aliased** spelling `use std.io_runtime.{file_rename}` is
already used in the tree (`src/lib/nogc_sync_mut/shell/file.spl:22`) and already
lowers to exactly that bare name; refusing only the aliased spelling made the two
forms disagree. The conservative "do not guess" branch is retained for the case
this tier cannot decide either.

## Sweep — 83 more of the same shape

`compiler/tests/native_build_and_alias_symbols_registered.rs` sweeps all
**1831** names in `RUNTIME_SYMBOL_NAMES` against the exact predicate the JIT
uses. **83 unique names have no definition reachable from the seed** — the same
population `check-no-unresolved-runtime-symbols.shs` reports RED. Too large to
fix here, so it is frozen as `UNRESOLVED_BASELINE` in that test: a NEW
unresolvable name fails, and a baselined name that became resolvable fails as a
**stale baseline**. Families: `rt_tls13_hkdf_*` (13), `rt_webgpu_*` (8),
`rt_simpleos_*_bytes` (8), `rt_torch_torchtensor_*_checked` (8),
`__simple_runtime_matrix_f64_*`/`gemm` (6), `rt_cuda_event_*` (5),
`rt_pbkdf2_hmac_*` (4), `rt_call_ptr_[0-3]` (4), `native_{tcp,udp}_set_*_timeout` (4),
`rt_vulkan_timestamp*` (3), `rt_process_owned_*` (3), plus singles including
`rt_dict_insert`, `rt_hostname`, `rt_char_from_code`, `rt_system_cpu_count`,
`rt_process_run_owned_bounded_value`.

## Regression gate

`src/compiler_rust/compiler/tests/native_build_and_alias_symbols_registered.rs`
— 3 tests: `rt_native_build` resolvable; the compiler-owned table is live and
discriminates (non-empty, every listed name has an address, a nonexistent name
is refused); and the ratcheted sweep with its own non-vacuity assertions.
Fails pre-fix on `rt_native_build`, passes post-fix.
