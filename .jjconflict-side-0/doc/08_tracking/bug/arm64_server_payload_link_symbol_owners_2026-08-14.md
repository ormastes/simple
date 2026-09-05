# ARM64 server payload link symbol owners

Status: fixed in working tree; full payload rebuild remains owned by the parent verification lane.
Owner: `/root/arm_link_symbols` (symbol-owner diagnosis and focused fix).

## Reproducer

`SIMPLE_NATIVE_BACKEND=cranelift sh scripts/os/build_arm64_servers_payload.shs`
reached the generic cross-linker with unresolved `bytes_to_string` and
`rt_arm64_syscall`.

## Root causes

- `std.common.binary_io.bytes_to_string` was declared as an extern although
  the native runtime ABI exports only `rt_bytes_to_text`.
- ARM userlib called the boot-only `rt_arm64_syscall` symbol instead of the
  strong `simpleos_syscall` trampoline installed in `libsimpleos_c.a` by the
  ARM64 sysroot owner.
- Userlib file/network paths invoked unsupported `Array.data_ptr` lowering
  instead of the canonical `rt_array_data_ptr_u8` runtime primitive.
- Database core used `Array.enumerate`, which was retained as an unresolved
  method by the current cross-target LLVM lowering.

## Resolution and contract

The library helper is now a real Pure-Simple wrapper over `rt_bytes_to_text`.
ARM userlib calls the sysroot-owned `simpleos_syscall`, and its shared byte
pointer wrapper calls `rt_array_data_ptr_u8`. Database traversal uses indexed
loops with unchanged order and early-return behavior. The payload executable
gate rejects all obsolete unresolved spellings. The focused SSpec contract
checks these owners without fabricating aliases or fallback stubs.
