# rt_cuda_launch_kernel_ex: native callers pass a C string, Rust reads (ptr, len)

**Status:** VERIFIED 2026-11-26 (GB10, aarch64). **Found:** 2026-11-26 (work/bug-cuda-module-get-function-abi-20261126). **Severity:** P2.
**Component:** `src/compiler/50.mir/text_extern_abi.spl`, `src/compiler_rust/runtime/src/cuda_runtime.rs`.

Native codegen splits a `text` extern argument into `(bytes, len)` only for
names that have a row in `text_arg_indices` (`text_extern_abi.spl`). Every
other text argument is passed as ONE word, the `rt_interp_cstr` C-string
pointer. Disassembly of a native probe shows exactly this:
`rt_cuda_module_get_function(module, "name")` gets `x1 = rt_interp_cstr(...)`
and nothing in `x2`.

`rt_cuda_launch_kernel_ex` has no row, but its Rust definition takes
`(module, func_name_ptr: *const u8, func_name_len: u64, ...)`. A native
caller therefore shifts every later argument by one slot, and `func_name_len`
becomes the caller's `grid_x`. Native callers exist:
`src/lib/nogc_sync_mut/cuda/mod.spl:121`,
`src/lib/nogc_sync_mut/io/cuda_sffi.spl:268`,
`src/lib/nogc_async_mut/cuda/mod.spl:857`.

Red, on the GB10, with `src/app/test/cuda_launch_kernel_ex_probe.spl` built
natively by integ25 Stage 2: `launch=-500 matched=0/4` in both the default
lane (core-C forwarder to the provider) and the `--runtime-path` lane
(cuda-featured native-all). The name word was read as `(ptr, len=grid_x)`.

## Resolution (2026-11-26, work/bug-cuda-launch-kernel-ex-abi-20261126)

The runtime now accepts what native callers send. This needs no bootstrap.
A `text_extern_abi.spl` row would only take effect in a rebuilt compiler.
- `cuda_runtime.rs`: both twins take `(module, func_name: *const c_char,
  grid..., shared_bytes, stream, args_ptr)`, 11 params.
- `runtime_dynload.c`: the forwarder takes and forwards `const char *`.
- `interpreter_extern/gpu.rs`: the cuda-feature call builds a `CString`.
  The dlopen branch already did.
- `codegen/runtime_sffi.rs`: the seed spec drops to 11 params.
- `gpu_provider_unload_load_race.c`: the fixture uses the C-string shape.

Scope: the pure-Simple compiler. A literal name is a raw C pointer and is
safe. A built name goes through `rt_interp_cstr`. Both lanes link the C runtime's
NUL-terminated version: `nm` and a disassembly of `ex_green_rp` show the C
body. The probe's heap-built name (`"probe_" + ...`) covers that case. The
Rust `rt_interp_cstr` returns unterminated bytes, but no pure-Simple lane
links it: `rt_interp_cstr_built_name_unterminated_runtime_path_2026-11-26`
(latent). The Rust seed's own native
codegen passes the tagged word, which is also out of scope.

This goes against the comment on `text_cstr_arg_indices` in
`codegen/instr/calls.rs`, which says new text externs should take
`(ptr, len)` with a registry row. That route needs a compiler rebuilt in
lockstep with the runtime, so it is left to the owner.

Green, on the GB10 (integ25 Stage 2, llvm; provider
`libsimple_runtime.so` sha256 `9b95b6c123e46f5a`, native-all
`c88e6a6555d3e4b3`): `launch=0 sync=0 copy=0 matched=4/4` in both lanes.
Without a provider: `launch=-3`. With `SIMPLE_CUDA_LIB` missing: the module
load returns -303 and launch_ex returns -1 (the `module <= 0` guard), with
no crash. `check-gpu-provider-unload-load-race.shs` as committed fails, both
before and after this change, on an unrelated `-Werror` at
`runtime_native.c` `rt_bdd_skipped` (unused-but-set-global). In a scratch
copy with `-Wno-error=unused-but-set-global`, it fails (rc 11) with the old
fixture against the new forwarder, and passes with the new fixture.
`check-gpu-provider-dynload-registry.shs` passes, and
`cargo check -p simple-compiler --features cuda` is clean.
