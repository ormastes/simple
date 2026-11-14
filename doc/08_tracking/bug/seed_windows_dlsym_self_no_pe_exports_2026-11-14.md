# Seed on Windows: dlsym_self_compat cannot see runtime `rt_vulkan_*` symbols

Date: 2026-11-14
Status: open

## Symptom

`interpreter::interpreter_extern::vulkan::tests::text_return_is_text_not_int`
failed on Windows with `Runtime("Vulkan runtime entry point
'rt_vulkan_get_last_error' is not linked into this binary ...")`. Every
`rt_vulkan_*` entry point routed through `vulkan.rs` is unreachable from the
interpreter on a Windows seed build, although the runtime crate is linked in.

## Root cause

`vulkan.rs::symbol` resolves entries with
`dl_compat::dlsym_self_compat`, which on Windows is `GetProcAddress` on
`GetModuleHandleA(NULL)` (the running exe). The runtime's `#[no_mangle] extern
"C"` functions are linked into the exe but are not in its PE export table (no
`dllexport`, no `.def`/`/EXPORT`), so the lookup returns null. On Unix
`dlsym(RTLD_DEFAULT)` finds them via the dynamic symbol table.

## Fix options

1. Direct-link table: have `vulkan.rs` call the runtime crate's functions
   through a generated static `(name, fn ptr)` table instead of a dynamic lookup
   (works on every platform, no export dependency).
2. Export the symbols from the seed exe (`-C link-args=/EXPORT:...` or a
   generated `.def`), keeping the dynamic lookup.

## Test coverage

- Unix: `text_return_is_text_not_int` (cfg(unix)).
- Windows: `windows_text_return_fails_closed_when_symbol_not_exported` pins the
  current fail-closed error; replace it with the Unix assertion once fixed.
