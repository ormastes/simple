# Rust `rt_interp_cstr` returns unterminated bytes for built strings

**Status:** OPEN (latent). **Found:** 2026-11-26 (review of
work/bug-cuda-module-get-function-abi-20261126). **Severity:** P3.
**Component:** `src/compiler_rust/runtime/src/value/collections.rs` (`rt_interp_cstr`).

Pure-Simple native codegen passes an unlisted `text` extern argument (one with
no `text_extern_abi.spl` row) as the single word `rt_interp_cstr(value)`. Callees
such as `rt_cuda_module_get_function` and `rt_cuda_launch_kernel_ex` then read
that word as a NUL-terminated C string.

The C runtime's `rt_interp_cstr` (`runtime_native.c`) returns a terminated
buffer (`data[len] = 0`). The Rust one returns `rt_string_data(value)`: the
raw bytes of a `RuntimeString`, with no terminator. A name built at run time
would over-read wherever the Rust symbol wins the link.

Review reported that the `--runtime-path` lane (cuda-featured native-all)
links the Rust one. That did not reproduce on integ25 Stage 2. `nm` plus a
disassembly of the `--runtime-path` probe `ex_green_rp` show one
`rt_interp_cstr`, and it is the C body: the `STR1` magic, the 0x10000
raw-pointer check, and a call to `rt_core_is_registered_immortal_ptr`. The
default lane is the same. So neither pure-Simple lane hits this today. It
is latent for any link where the Rust runtime's definition is chosen.

Also out of scope for the C-string fixes: the Rust seed's own native codegen
passes the tagged value word for unlisted text args (`codegen/instr/calls.rs`,
`text_cstr_arg_indices` must stay empty).

Fix options: terminate `RuntimeString` storage (one extra byte in
`rt_string_new`), or have the Rust `rt_interp_cstr` return a terminated copy.
