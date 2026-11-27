# "cranelift: function address missing declaration" is a recovered probe miss

Status: open (diagnostic only, P3). Not a codegen failure.

## Observation

Bootstrap run 13 Stage 2 `compiler_cli_build.log` prints
`cranelift: function address missing declaration <fn>` for
`char_to_ascii` (x4), `cuda_device_count`, `cuda_sync`, `vulkan_device_count`,
`sleep_secs`, `file_read_bytes_result`, `elf_exec_plan`.

## Analysis

The line is an `eprintln!` in the seed runtime
(`src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs:1578/1588`,
`rt_cranelift_function_addr_in_func`) fired on the FIRST lookup of a function
value that names a function defined in another module. The Simple caller
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`
`cl_translate_const_value`, `FuncPtr` arm) then declares the import from the
FuncPtr signature (`CL_LINKAGE_IMPORT`) and retries; only a second miss panics
with `Cranelift function address missing declaration: <fn>`.

The panic string occurs 0 times in the run-13 log and none of the 9 failed units
fail for this reason (all 9 are `Failed to declare module statics`, see
`export_list_static_visibility_not_lifted_2026-11-06.md`). Every address was
declared and emitted.

## Remaining work

The stderr line is misleading: it reads as an error during triage. Make the
first probe silent (a probe-only SFFI entry, or demote the message to a debug
env flag) in the seed runtime when the seed is next rebuilt.
