# Native-all omits the existing SCV WASM bridge

Canonical bug: `nativeall_scv_wasm_bridge_missing_2026_11_06`; root session owns its registered claim and database row. This lane does not modify the shared bug database.

Base: `fd45e21b30f448e9e528b151bf3eb8179bd68574`. Root retained strict Windows nativeall link at 04c reports 97 rooted unresolved symbols, including `spl_scv_wasm_parse_blob_copy`. Input: `C:/dev/simple/.git/worktrees/dependency-resolution-io-d88f/evidence/windows-value-contract.sdn`.

The existing `src/runtime/runtime_scv_wasm_ffi.c` defines that single public symbol. Its seven raw arguments carry three callback addresses and borrowed grammar/source pointer-length pairs. It copies bounded inputs, copies provider output before releasing the provider handle, and returns an owned raw rt_alloc buffer. The Simple caller retains DynLib across the raw call, converts the returned C string, and rt_free releases it. No managed Rust/C object crosses this bridge. Other dependencies are existing rt_alloc/rt_free and libc memcpy/memchr owners.

Repair: register this existing TU in runtime/build.rs compilation and export scanning; add its source/header rerun inputs; include it in portable core-C and pure-Simple ordinary/core-C compositions. Add the header to portable core-C fingerprint inputs. No other provider family, Cranelift implementation, ABI, or Stage4 projection changes.

Cache proof (source review): runtime/build.rs feeds c_sources to cc and now explicitly watches both bridge files. Portable tools.rs runtime_inputs includes the new C source and header, then runtime_inputs_fingerprint hashes input names and contents before archive reuse. Pure-Simple runtime_compiler.spl builds source_sig from the selected names and passes it to the POSIX fingerprint owner; runtime_object_cache_posix.spl hashes all runtime C/header contents. Windows cached compilation receives src_path and runtime_context; runtime_object_cache_windows.spl hashes preprocessed TU bytes (including headers), compiler/toolchain and context before lookup. No manually forced cache identity.

Diagnostic verification: actual C TU linked with existing callback contract fixture using Windows clang 23.1.2, C11, -Wall -Wextra -Werror and -D_CRT_NONSTDC_NO_DEPRECATE. PASS: typed SCV WASM FFI contract. Strengthened boundary assertion verifies provider release poisons borrowed storage while returned first/last bytes remain intact. Fixture also tests bounds, embedded NUL grammar, invalid callbacks, load/parse failures and balanced allocation failures. Source composition regression PASS. git diff --check PASS. See adjacent SDN ledger for all three compile attempts.

UNRUN: rebuilt nativeall archive/link, source-matched admitted P2, SSpec runner and native integration. At diagnostic execution time the heavy build slot belonged to the root P0 cycle6 lane; root subsequently reported terminal PASS and released it. This lane performed no further runtime qualification. Diagnostic C/source checks do not establish runtime admission or complete the root release task. Stage4 parity is not claimed.

Original tool results exported (not contemporaneous logs), retained test executable and SHA256 receipts: `C:/dev/simple/.git/worktrees/nativeall-scv-d88f/evidence/`.
