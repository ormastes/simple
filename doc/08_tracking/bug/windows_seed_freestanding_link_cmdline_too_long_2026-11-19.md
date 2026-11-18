# Windows seed: freestanding native-build link exceeds the 32 KiB command line (os error 206)

- status: verification-pending
- found: 2026-11-19 (lane ssos-launch)

## Repro
From WSL through `C:/dev/wt/xc-wsl-scripts/winlink.sh` (Windows `bin/simple.exe`):

    simple.exe native-build --backend cranelift --entry-closure --timeout 1200 \
      --entry examples/09_embedded/simple_os/arch/riscv64/nvfs_root_entry.spl \
      --target riscv64gc-unknown-none-elf \
      --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld -o kernel.elf

Result: `compiled=753 reused=0 failed=0`, then
`Build failed: link (clang): The filename or extension is too long. (os error 206)`.

## Root cause
The freestanding link in `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`
(the `use_direct_lld` / clang arms near the "Freestanding bare->qualified alias bridge"
message) passes every object path, `--defsym` and runtime archive as separate argv
entries. With ~770 objects under a `\?\C:\...` worktree the joined line exceeds
CreateProcess's 32 KiB. The hosted Windows link and the owner-member path already use
an `@response` file for this reason (same file, "os error 206 observed 2026-11-12");
the freestanding arm does not.

## Fix direction
Write the freestanding argv (objects, defsyms, archives) to a response file on Windows,
space-joined with `quote_cl_response_arg`, keeping link order. Needs a seed rebuild +
redeploy to take effect; a manual relink of the kept objects is not a substitute (the
kept object dir holds alternate runtimes that duplicate-define `rt_*`/`_start`).

## Update 2026-11-19 — fix landed (verification-pending)
`link_objects_freestanding` now spills argv > 24 KiB into `freestanding_link.rsp`
(`spill_args_to_response_file`, linker.rs; `--rsp-quoting=posix` for direct
ld.lld). Covered by 3 `linker_tests` unit tests. Not yet proven on a real
riscv64 kernel link: the Windows seed lacks the LLVM backend and Cranelift
rejects the kernel's inline asm, so the build stops before linking.
Status: verification-pending

Also fixed: a duplicate identical `_path_bytes_to_text` in
`src/os/kernel/loader/executable_source.spl` made the kernel build fail with an
ambiguous-call error; regression spec
`test/01_unit/os/kernel/loader/executable_source_single_definition_spec.spl`.
