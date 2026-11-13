# Cranelift: imported C `bool` result read as a full word (LSP MCP stdout "write failed")

- **Date:** 2026-11-13
- **Status:** fixed in source (backend) + tagged workaround for the frozen Phase 2 compiler
- **Lane:** Windows x86_64, llvm-mingw UCRT, `native-build --backend cranelift`

## Symptom

`src/app/simple_lsp_mcp/main.spl` built by the frozen Windows Phase 2 compiler with
`--backend cranelift` answers `initialize`, then panics on `tools/list` with
`LSP MCP stdout transport write failed; output may be partial` (rc=1). The LLVM
build of the same source answers both requests.

## Root cause

`src/lib/nogc_sync_mut/sffi/fs.spl` `io_file_write_all` returns the result of
the C extern `bool rt_io_file_write_all(...)` (`src/runtime/runtime_native.c`).
A C `bool` result defines only `AL`; clang ends the function with
`setbe %bpl; movl %ebp, %eax`, so bits 8..31 of `EAX` carry the caller's saved
`%rbp` bits.

The Cranelift lane declares every imported result through `sig_type_to_cl`,
which widens Bool and sub-64 integers to `I64`
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`, both import
sites in `cl_translate_call`). The caller kept the whole register, and `not x`
lowers to `x xor 1`, so a true result with garbage upper bits became nonzero:
`if not io_file_write_all(...)` in `src/app/simple_lsp_mcp/json_helpers.spl`
`print_raw` panicked. Whether it fires depends on the stack address in `%rbp`,
which is why one request succeeded and the next failed.

Disassembly evidence (`build/diag-phase4/cl_lsp_mcp/lsp_mcp.exe`):
`lib.nogc_sync_mut.sffi.fs.io_file_write_all` stores `rax` from
`call *rt_io_file_write_all` unchanged; `print_raw` then does
`xorq $0x1, %rax; testq %rax, %rax; jne <panic>`.

## Fix

- Backend: `cl_import_result_narrow_plan` / `cl_normalize_import_result` re-extend
  an imported call's result from its DECLARED width (Bool/U8/U16/U32/Char:
  `ireduce` + `uextend`; I8/I16/I32: `ireduce` + `sextend`), only when the
  callee signature is known. The import signature itself is unchanged.
  Spec: `test/01_unit/compiler/backend/cranelift_import_narrow_result_spec.spl`.
- Workaround (`# @workaround bug=cranelift_lsp_mcp_stdout_write_failed_2026-11-13`):
  `_io_c_bool` in `fs.spl` masks the low byte so binaries built by the frozen
  Phase 2 compiler are correct. Remove once Phase 2 is rebuilt with the backend fix.
  Stays inside the existing SOSIX fs owner; no new `rt_*` extern.
