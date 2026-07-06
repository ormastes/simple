# Bug: Baremetal --entry-closure imported-class instantiation FAULT

- **Status:** INVESTIGATING (root-cause candidates verified in binary artifacts; fix pending probe confirmation)
- **Date:** 2026-07-06
- **Where seen:** `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl:14-17` — instantiating a class imported from a shared module (e.g. `os.gui.shortcut.ShortcutHandler`) inside an x86_64 `--entry-closure` baremetal kernel faults at runtime. Workaround so far: procedural duplication (the 3603-line WM), factory free-functions in the defining module (`create_fb_engine`), and integer action codes instead of shared enums (arm64 `wm_entry_io`).
- **Impact:** blocks sharing `src/os/compositor` classes (`HostCompositor`, `CompositorBackend` trait impls) into the QEMU guest WM.

## Repro

- Probe entry: `examples/09_embedded/simple_os/arch/x86_64/class_fault_probe_entry.spl`
  (serial markers S1..S5/CLASSOK; commit d99740bcff13)
- Probe shared module: `src/os/gui/class_probe.spl` (scalar + heap-typed module
  globals + class with text field, modeled on `os.compositor.display_backend`)
- Build (same flow as `scripts/check/check-simpleos-wm-fullscreen-evidence.shs:192-202`):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=$PWD/src SIMPLE_OS_LOG_MODE=off \
SIMPLE_ALLOW_FREESTANDING_STUBS=1 PATH=/usr/lib/llvm-18/bin:$PATH \
bin/release/x86_64-unknown-linux-gnu/simple native-build \
  --source build/os/generated --source src/os --source src/lib \
  --source examples/09_embedded/simple_os/arch/x86_64 \
  --backend cranelift --cpu x86-64-v1 --opt-level=aggressive --log off \
  --entry-closure --entry examples/09_embedded/simple_os/arch/x86_64/class_fault_probe_entry.spl \
  --target x86_64-unknown-none -o build/os/class_fault_probe.elf \
  --linker-script examples/09_embedded/simple_os/arch/x86_64/linker.ld --mode=dynload
qemu-system-x86_64 -no-user-config -monitor none -net none -machine q35 -cpu qemu64 \
  -m 2G -serial file:serial.log -display none -no-reboot -kernel build/os/class_fault_probe.elf \
  -vga std -device isa-debug-exit,iobase=0xf4,iosize=0x04
```

Note: trailing `--mode=dynload` is required — `run_native_build_worker`
(src/app/cli/native_build_main.spl:198) injects `--mode=interpreter` into the
worker argv, which `cli_native_build` rejects
(src/app/io/_CliCompile/compile_targets.spl:595-597). Last-wins parsing makes
the explicit flag override it. This is a separate worker-arg regression.

## Verified findings (binary evidence)

Checked `build/os/simpleos_wm_simple_web_check_32.elf` (real WM kernel built by
the evidence-script flow) with llvm-nm:

1. **Module initializers never run in x86_64 baremetal kernels.**
   - `examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:305-311` calls
     `__simple_call_module_inits` through a `.weak` reference and jz-skips when
     unresolved.
   - In the kernel ELF the symbol is `w` (weak, undefined) and there are ZERO
     `__module_init_*` symbols → the skip branch is always taken.
   - The pure-Simple backend never emits per-module inits nor the aggregator:
     the only body in `src/compiler/70.backend` is the EMPTY riscv64 stub
     `void __simple_call_module_inits(void){}` at
     `src/compiler/70.backend/backend/llvm_native_link.spl:352`. The real
     emitter exists only in the Rust seed
     (`src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs:322-371`,
     generate_init_caller).
   - Consequence: module globals land in BSS (`llvm-nm` shows e.g. `_auth_db`,
     `_channel_count` as `b`) and stay ZERO at runtime; only const-foldable
     `val`s are materialized (e.g. `_aes_sbox` in rodata).

2. **Unresolved cross-module class methods are silently bound to NIL stubs.**
   - `examples/09_embedded/simple_os/arch/x86_64/boot/auto_stubs.c` (1.1 MB,
     checked in) defines weak `Class_dot_method` stubs returning NIL (0x3)
     "so execution continues past unresolved cross-module refs".
   - A ctor bound to such a stub returns NIL; the following method call on the
     NIL object faults.

3. **Two coexisting method-symbol manglings in the same kernel:** bare
   (`KLogEntry_dot_from_bytes`) and module-qualified
   (`os__services__vfs__vfs_boot_init__VfsFileSize_dot_to_i64`). A call/def
   scheme mismatch binds the call to the weak NIL stub (finding 2).

4. **Per-module MIR lowering with shared, order-dependent class metadata:**
   under `--entry-closure` each module is lowered separately
   (`src/compiler/80.driver/driver_pipeline.spl:331-384`) sharing one
   `MirLowering.field_map` built per module before its functions
   (`src/compiler/50.mir/_MirLowering/module_lowering.spl:277-303`), so a
   module lowered before the defining module of a class it instantiates sees
   no field layout for it.

## Root-cause candidates (to be discriminated by probe markers)

- Fault at S2 (simple imported ctor) → symbol-binding/mangling (findings 2+3)
  or field-map ordering (finding 4).
- S2-S4 pass, fault at S5 (heap-typed module global) → missing module inits
  (finding 1).

## Next steps

- Probe build in progress (full + minimal source-set variants).
- Fix at root cause in pure-Simple compiler; then re-verify CLASSOK marker.
