# Windows producer AOT defects met while building runtime_owner_cede (2026-10-20)

Producer: `C:/dev/simple-bootstrap-storage/scope-producer-3d9d-20261018/strict-link-preparation/simple-scope-diagnostic-strict.exe`
(`simple-bootstrap 1.0.0-rc.1`), `native-build --backend llvm --runtime-bundle core-c-bootstrap`,
x86_64-pc-windows-msvc, C runtime from release_phase3 @ a41a729c5fd.
Each item was reproduced by a minimal native program; workarounds are in
`src/compiler/70.backend/linker/coff/coff_runtime_owner.spl` and
`src/app/runtime_owner_cede/main.spl`.

1. **`var copy = param` of a `[u8]` parameter yields corrupted bytes.**
   `fn f(archive: [u8]): var bytes = archive` then `bytes[56]` read 6 where
   `archive[56]` read 55 (the ar size digit). Reading the parameter directly
   is correct. Workaround: the archive buffer is read inside the function
   (`var bytes = rt_file_read_bytes(path) ?? []`), which mutates correctly.
2. **`rt_file_write_bytes(path: text, data: [u8]) -> bool` writes 0 bytes.**
   The file is created empty and `false` is returned, for 2-byte, 1003-byte
   and 70 MB arrays alike. `rt_file_write_bytes_array(path: Any, data: Any)`
   (RuntimeValue ABI) writes correctly. Every compiler call site that uses the
   `(text, [u8])` spelling (e.g. `linker_wrapper_helpers.write_bytes_to_file`)
   is exposed when built by this producer.
3. **`val r = f()?` on a struct-valued `Result` reads garbage `i64` fields.**
   `RuntimeOwnerCedeResultV1.undefined` printed 2081858137489 through `?`,
   4372 through `match ... case Ok(r): r`. The `[u8]` field was intact.
   Workaround: `match` instead of `?`.
4. **An `Any`-typed lambda passed to `rt_thread_spawn_isolated` /
   `rt_thread_spawn_isolated_with_args` returns handle 0** (no thread). The
   with_args body is unchanged by the runtime-owner work, so this is the
   closure value lowering, not the C owner. The C contract itself is pinned by
   `src/runtime/test/rt_thread_owner_contract_selfcheck.c`.
