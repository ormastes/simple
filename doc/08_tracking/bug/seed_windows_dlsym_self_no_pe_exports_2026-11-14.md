# Seed on Windows: dlsym_self_compat cannot see runtime `rt_vulkan_*` symbols

Date: 2026-11-14
Status: verification-pending

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

## Impact (Windows, before the fix)

`interpreter_extern/mod.rs` consults `EXTERN_DISPATCH` first and falls through
to `vulkan::dispatch` for every `rt_vulkan_*` name without a bridge handler in
`gpu.rs`. On a Windows seed each of those calls from interpreted Simple code
ended in the "not linked into this binary" runtime error: all 132 rows of
`VULKAN_FNS` were unresolvable (RED run below), so e.g.
`rt_vulkan_get_last_error` and the `rt_vulkan_selected_device_*` text getters
never returned. Names served by `gpu.rs` handlers were not affected, and the
native (AOT) lane links the runtime directly and never used this lookup.

`cache_host.rs` is NOT this bug: it calls `simple_runtime::*` functions
directly. Its `#[cfg(unix)]` test is gated because the runtime's cache host
authority fails closed on Windows (`open_root` returns -1), a separate gap.

## Fix

Option 1 with an existing registry, no new table: `vulkan.rs::symbol` now
consults the runtime's generated static symbol table
(`simple_runtime::RUNTIME_SYMBOL_ENTRIES`, published through
`simple_native_loader::static_provider()`, the registry the seed JIT already
links against; the compiler crate always enables `runtime-symbol-table`) and
keeps `dlsym_self_compat` only as the fallback. No linker export list, no
change to the PE image.

The new all-rows test found one family member absent from that table on every
host: `rt_vulkan_selected_device_identity_v1` was defined by the runtime but
never listed in `RUNTIME_SYMBOL_NAMES` (`common/src/runtime_symbols.rs`), which
is the table's only registration mechanism. It is now listed.

## Evidence

- RED (Windows, before): `every_registered_entry_point_resolves_in_process`
  listed all `rt_vulkan_*` names as unresolved; `text_return_is_text_not_int`
  failed with the "not linked into this binary" error.
- GREEN (Windows, after): `cargo test --profile bootstrap -p simple-compiler
  --lib interpreter_extern::vulkan::tests` passes, including both tests above.
  `text_return_is_text_not_int` is cross-platform again and the Windows
  fail-closed pin test is removed.

## Not covered / still open

- Not natively verified on a deployed Windows seed with a real Vulkan device;
  Unix lanes were not re-run here (the lookup order changed there too: table
  first, `dlsym` fallback).
- The same PE limitation still applies to the other process self-lookups,
  which this change does not touch: `spl_dlsym_process_checked`
  (`interpreter_extern/wsffi.rs`, returns status 3), the last-resort
  `resolve_process_runtime_symbol` in `runtime/src/loader/loader.rs`, and
  `native_loader::ProcessSymbolProvider`. The JIT's `default_runtime_provider` chains a second provider
  (static table or runtime library, by load mode) behind the process lookup,
  so it does not depend on PE exports alone. If one of them needs a
  host symbol outside `RUNTIME_SYMBOL_ENTRIES` on Windows, add that symbol to
  the table rather than exporting from the exe.

## Test coverage

- `every_registered_entry_point_resolves_in_process` (all hosts): every
  `VULKAN_FNS` row resolves to a non-null address.
- `text_return_is_text_not_int` (all hosts).
