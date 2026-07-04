# RV32 OS Build Dispatch Probe - 2026-07-02

## Result

- Source-level fix: `simple os build --arch=riscv32` dispatches through
  `get_target(...)`, selecting `src/os/kernel/arch/riscv32/boot.spl`.
- RV32 kernel smoke native-build args are scoped to `build/os/generated`,
  `src/os`, and `src/lib`, with `--opt-level=standard` and `--timeout 840`.
- A 1ms runtime probe confirmed the corrected command line.
- Full runtime attempts were invalidated by concurrent workspace churn: the
  source reverted before launch or before completion and the command fell back
  to the old broad/native aggressive path.

## Evidence

Focused guards previously run this turn:

```text
bin/simple test test/03_system/os/simpleos_native_build_entry_closure_spec.spl --mode=interpreter
PASS test/03_system/os/simpleos_native_build_entry_closure_spec.spl
2 examples, 0 failures

bin/simple test test/01_unit/app/cli/os_build_dispatch_spec.spl --mode=interpreter
PASS test/01_unit/app/cli/os_build_dispatch_spec.spl
1 example, 0 failures
```

Scoped 1ms runtime probe:

```text
[build][riscv32] phase=plan entry=src/os/kernel/arch/riscv32/boot.spl target=riscv32-unknown-none backend=llvm log=on
[build][riscv32] cmd: src/compiler_rust/target/release/simple native-build --source build/os/generated --source src/os --source src/lib --backend llvm --opt-level=standard --log on --timeout 840 --entry-closure --entry src/os/kernel/arch/riscv32/boot.spl --target riscv32-unknown-none -o build/os/simpleos_riscv32.elf --linker-script src/os/kernel/arch/riscv32/linker.ld
[build][riscv32] phase=native-build FAILED exit=-1 elapsed_ms=13 timeout_ms=1
Process timed out
```

Invalidated full attempt after concurrent revert:

```text
[build][riscv32] phase=plan entry=src/os/kernel/arch/riscv32/boot.spl target=riscv32-unknown-none backend=llvm log=on
[build][riscv32] cmd: src/compiler_rust/target/release/simple native-build --source build/os/generated --source src --source examples --backend llvm --opt-level=aggressive --log on --entry-closure --entry src/os/kernel/arch/riscv32/boot.spl --target riscv32-unknown-none -o build/os/simpleos_riscv32.elf --linker-script src/os/kernel/arch/riscv32/linker.ld
[build][riscv32] phase=native-build FAILED exit=-1 elapsed_ms=900008 timeout_ms=900000
Process timed out
```

Restored ELF metadata after failed attempts:

```text
elf_size=106404 elf_mtime=2026-05-13 21:35:01.518143948 +0000
```

## Status

Do not rerun the full RV32 build until the concurrent lane stops reverting
`src/app/cli/_CliMain/args_and_os_commands.spl` and
`src/os/_QemuRunner/os_build_run.spl`. The scoped command is proven by the
1ms probe; the long-run evidence above is for a reverted command line.
