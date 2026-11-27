# rt_cuda_module_get_function takes a C string for a Simple `text` argument

**Status:** VERIFIED 2026-11-26 (GB10, aarch64). **Found:** 2026-11-26 (work/bug-cuda-native-20261126). **Severity:** P3.
**Component:** `src/compiler_rust/runtime/src/cuda_runtime.rs`, `src/runtime/runtime_dynload.c`.

The Rust `rt_cuda_module_get_function(module: i64, func_name: *const c_char)`
reads its name as a NUL-terminated C string. The Simple extern declares
`func_name: text`, whose native ABI is `(bytes, byte length)`, as for
`rt_cuda_launch_kernel` and `rt_cuda_launch_kernel_ex`. The core-C forwarder
set in `runtime_dynload.c` therefore leaves this one function out (27 of 28
forwarded) until the ABI is decided.

Found while fixing `native_c_runtime_missing_cuda_provider_forwarders_2026-11-22`.

## Resolution (2026-11-26, work/bug-cuda-module-get-function-abi-20261126)

The premise was wrong. Native codegen splits a `text` extern argument into
`(bytes, len)` only for names with a row in `text_arg_indices`
(`src/compiler/50.mir/text_extern_abi.spl`). Every other text argument is
passed as ONE word, the NUL-terminated `rt_interp_cstr` pointer. This
function has no row. Disassembly of the native probe shows
`x1 = rt_interp_cstr("probe_fill")` and nothing in `x2`. So the existing Rust
`*const c_char` signature is exactly what native callers emit, and the
interpreter call site (`interpreter_extern/gpu.rs`) builds a C string too.

Scope: this holds for the pure-Simple compiler and literal names. The Rust
seed's native codegen passes the tagged value word, not a C string, for
unlisted text args. Review reported that under `--runtime-path`, a BUILT name
is not NUL-terminated. That did not reproduce: `nm` and a disassembly of the
`--runtime-path` probe show the C runtime's `rt_interp_cstr` (`STR1` magic,
the 0x10000 raw-pointer check), and C strings store `data[len] = 0`. The
Rust `rt_interp_cstr` does return unterminated bytes. It is latent here and
filed as `rt_interp_cstr_built_name_unterminated_runtime_path_2026-11-26`.

A `(bytes, len)` Rust signature was tried first. The native probe then
aborted (`memory allocation of 192204177764371 bytes failed`, rc 134),
because it read a stray register as the length. It was reverted. Moving to
`(bytes, len)` needs a `text_extern_abi.spl` row, which takes effect only in a
compiler rebuilt from that source and so must land in lockstep with a
bootstrap. That is left to the owner.

Done:
- `runtime_dynload.c`: `rt_cuda_module_get_function(int64_t, const char *)`
  forwarder, so all 28 provider calls are forwarded. With no provider it
  returns -3, like the Rust non-cuda twin.
- `check-gpu-provider-dynload-registry.shs`: a fake that checks the name and
  a harness call. Red before the forwarder: `mold: error: undefined symbol:
  rt_cuda_module_get_function`. Green after: `fn=42`, or `-3` with a rejected
  provider.
- Proof: `src/app/test/cuda_module_launch_probe.spl`, natively built by integ25
  Stage 2, both lanes. Default (core-C forwarders to the provider DSO):
  `init=0 module_ok=true function_ok=true missing=-500 launch=0 sync=0 copy=0
  matched=4/4`. `--runtime-path` (cuda-featured native-all): the same, with no
  NEEDED libcuda. With no provider, every call gets `-3`, rc 0. With
  `SIMPLE_CUDA_LIB` missing, `init=303`, all calls fail cleanly, rc 0.
  Under host memory pressure (about 15 GB free), module load twice returned
  -2 `CUDA_ERROR_OUT_OF_MEMORY`, once in each lane. Both runs failed cleanly
  with rc 0, and repeat runs passed.

Found on the way, filed separately:
`cuda_module_load_data_unterminated_ptx_and_bad_handle_segv_2026-11-26`
(fixed), `cuda_launch_kernel_ex_text_abi_unregistered_2026-11-26`,
`native_text_literal_brace_escape_unprocessed_2026-11-26`.
