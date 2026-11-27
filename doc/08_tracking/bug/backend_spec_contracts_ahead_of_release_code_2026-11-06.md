# Backend source-contract specs ahead of release/1.0.0 code (2026-11-06)

Status: open. Found while repairing `test/01_unit/compiler/backend/` specs.

## 1. `dir_sync_runtime_contract_spec` (0/4) — feature never landed on release

`1c6c8d48762 feat(runtime): add fail-closed directory sync ABI` (2026-08-11) is
NOT an ancestor of `release/1.0.0`; only its spec arrived via the
`88aac2ffe28` transplant. `rt_dir_sync` exists nowhere under `src/` on
`release/1.0.0` or `origin/main`. A `git cherry-pick -n 1c6c8d48762` conflicts
in 9 shared files (`runtime.c`, `runtime.h`, `runtime_legacy_core.c`,
`sffi/io.spl`, `ffi/io.spl`, `io_runtime.spl`, `text_extern_abi.spl`,
`native_project/tests.rs`, the spec), so it needs an owner of the runtime/IO
surface to re-port it. Not done here.

## 2. `cranelift_aggregate_runtime_abi_spec` "keeps dictionaries on the heap runtime ABI"

Asserts `src/runtime/simple_core/core_array.spl` does not define
`pub fn rt_dict_new`. It has defined it since at least 2026-05-27, including at
the commit that added the assertion (`55bd6128887`), so the assertion has never
passed. The C runtime also defines `rt_dict_new` (`runtime_native.c`). Removing
the pure-Simple copy changes which provider the simple_core lane links, which
needs a runtime-lane owner's decision. The other 10 examples in that spec pass.
