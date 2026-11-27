# Self-hosted native backend: extern `-> text` over a `*const c_char` runtime return is undecoded (unverified)

- **Filed:** 2026-11-23
- **Status:** open (unverified, so it is a gap until measured)
- **Found by:** Blocker 9 in `linux_gb10_n2_qualification_executable_blockers_2026-11-18.md`

## What is known

12 Rust runtime exports return a raw `*const c_char`, while Simple declares
them `extern fn ... -> text`:

- `rt_cuda_device_name`, `rt_cuda_get_error_string`
- `rt_metal_device_name`, `rt_metal_get_last_error`
- `rt_vulkan_device_driver_identity`, `rt_vulkan_device_name`,
  `rt_vulkan_device_type`, `rt_vulkan_get_last_error`
- `rt_vulkan_selected_device_driver_identity`,
  `rt_vulkan_selected_device_identity_v1`, `rt_vulkan_selected_device_name`,
  `rt_vulkan_selected_device_type`

The Rust seed handles them correctly: its native codegen decodes each through
`rt_cstring_to_text`, using `C_STRING_RETURNING_RUNTIME_FNS` in
`src/compiler_rust/compiler/src/codegen/instr/calls.rs`. When an entry is
missing, the call yields a raw pointer that code then uses as a text handle,
and `.split` / `.len` / `==` give garbage. That is what happened with
`rt_vulkan_selected_device_identity_v1` on 2026-11-22.

## Gap

There is no equivalent list or `rt_cstring_to_text` insertion in `src/compiler/`.
A grep of `src/compiler/` for the 12 names finds none of them. Its only
`rt_cstring_to_text` uses are the sffi_gen tools and the lld wrapper, which
call the function explicitly. It is unverified whether the self-hosted native
backend decodes these returns some other way.

## To close

1. Write a native spec that calls `rt_vulkan_device_name(0)` through the
   self-hosted backend. It must produce a text whose `.len()` equals the name's
   byte length.
2. If that spec is red, add the same decode list to the pure-Simple lowering.
   Alternatively, make the runtime return boxed text; that also changes the C
   weak stubs in `runtime_native.c`.
