# SMF from `compile` has 0 code bytes on Windows; running it crashes calling `main`

**Status:** open. **Host:** Windows x86_64-pc-windows-msvc, stage-2 self-hosted `simple_cli.exe`
(#1606 and later).

## Symptom

`simple_cli compile hello.spl -o hello.smf` exits 0 and writes a 569-byte SMF.
`simple_cli hello.smf` then exits 0xC0000005 after about 3 s.

## What executes `run x.smf`

The SMF is not run by the HIR interpreter. It is copied into executable memory and called natively:

- `src/app/io/_CliCommands/run_commands.spl:110`: `cli_run_file` sends a `.smf` path to
  `moduleloader_execute_smf`, exported by `compiler.loader.runtime`
  (`src/compiler/99.loader/runtime/__init__.spl:10`) from `module_loader_compat.spl`.
- `src/compiler/99.loader/module_loader_compat.spl:1291-1340` (`load_with_intent`, SmfArtifact):
  for each exported SMF symbol, it reads the code bytes, calls `native_alloc_exec_memory(code.len())` (`:1317`),
  copies the bytes and marks the memory executable. No relocations are applied.
- `:1931`/`:1936`: `native_call_function_0(symbol.address)` calls `main`.

## Why the SMF is 569 bytes

The file holds the header, the launch-metadata note and the section and symbol tables, but **no machine code**.
The dump shows the `code` section and the `main` symbol both have size 0. The chain:

1. With #1606, debug `auto` resolves to `BackendKind.Llvm`: IR text is compiled by the external `llc`
   (`src/compiler/70.backend/backend/llvm_backend_tools.spl`, `compile_ir_to_object`).
2. `find_llc` resolved `llc-20` (`src/compiler/95.interp/interpreter/llvm/tools.spl:135`) on a host that
   has only `llc.exe` (LLVM 23.1.1). Separate record: `find_llc_posix_probe_windows_2026-09-26.md`.
3. `llc` runs through `backend_shell_tuple(cmd)` (`llvm_backend_tools.spl:224` -> `cmd.exe /c`,
   `70.backend/backend/io_compat.spl:13`). No `llc failed` error came back (`:231`), so the exit code
   reported for a command that cannot run was 0. The earlier `echo | xxd -r -p > file` SMF writer showed
   the same pattern (fixed in #1606): it wrote nothing and still reported 0.
4. `rt_file_read_bytes(obj_path)` (`:252`) reads a missing object file, so the object bytes are empty.
5. `src/compiler/80.driver/driver_aot_smf_output.spl:198` (`if val obj_bytes = module.object_code`) appends nothing,
   and `smf_writer.spl:399` emits `main` with size `code_bytes.len()` == 0.
6. The loader allocates and "executes" 0 bytes, and the native call faults.

Steps 2 and 3 are inferred from the output: `resolved=[llc-20]`, no `llc failed` diagnostic,
and an empty object. `process_run`'s exit status for a missing executable on Windows has not been
measured directly.

## Fail-open points to close (no fix yet)

- The compile succeeds with zero object bytes. `collect_smf_bytes` should reject an empty object from a
  native backend.
- The loader calls a size-0 `main`. `load_with_intent` should reject a 0-byte executable symbol.
- Exit status from `backend_shell_tuple`/`process_run` on Windows for a command that cannot be found.
