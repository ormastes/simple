# SimpleOS native-build: 815 unresolved symbols block kernel link (0.9.8 prep)

- Date: 2026-04-28
- Severity: BLOCKER for v0.9.8 SimpleOS release lane
- Reproduction:

```
sh scripts/os_qemu_test.shs --tier 1
# logs at build/release_0_9_8/simpleos_qemu.log (~45k lines)
```

## Symptom

`bin/simple native-build --entry-closure --entry examples/simple_os/arch/x86_64/os_entry.spl --target x86_64-unknown-none -o build/os/simpleos_x86_64.elf --linker-script examples/simple_os/arch/x86_64/linker.ld --source src/os` fails with:

```
Freestanding unresolved symbol check: 815 unexpected symbol(s)
Link failed. Objects kept at: /tmp/.tmpPbq4bT
Build failed: freestanding link has unexpected unresolved symbol(s)
FAIL: Kernel build failed (exit 1)
```

## Two distinct issues

### 1. Cranelift verifier errors → 10 stub fallbacks

Functions like `_apply_opacity` hit `ireduce.i32` with f32 operand:

```
inst52 (v58 = ireduce.i32 v57): arg 0 (v57) with type f32 failed to satisfy
type set { ints: 6,7 ; floats: <none> }
```

Cranelift verifier catches the type mismatch, native-build replaces the body with a stub and continues. `SIMPLE_NO_STUB_FALLBACK=1` would make this hard-fail instead of silently stubbing.

### 2. Freestanding link: 815 unresolved symbols

After stub fallback, the freestanding linker rejects the object set. Categories of unresolved symbol:

- Class type names (~700) — `apps__shell__shell_app__VfsManager`, `kernel__arch__hal__BootArgs`, `lib__common__ui__session__UIState`, etc. The class metadata symbols are referenced but not emitted/linked.
- Runtime extern primitives (~60) — `rt_arm64_*`, `rt_arm_virtio_*`, `rt_dma_*`, `rt_engine2d_*`, `rt_intel_engine2d_*`, `rt_opengl_*`, `rt_metal_*`, `rt_oneapi_*`, `rt_memcpy`, `rt_memset`. Cross-arch and cross-backend runtime stubs not stripped from the closure.
- Free functions (~50) — `serial_putchar`, `log_init_serial`, `pmm_free_page`, `theme_ui_theme`, `cuda_*`, `parse_*`, `bytes_to_*`, etc.

The cross-arch runtime leak is consistent with the prior `x86_64_kernel_build_riscv_asm_leak_2026-04-28.md` finding: `--source src/os` directory-crawls every `.spl`, and many transitively reference cross-arch / cross-backend primitives that never get implemented for `x86_64-unknown-none`. Even with `--entry-closure`, the import graph still pulls them in.

## Notes

- Latest existing kernel artifact is from 2026-04-26 02:38 (predates the recent merges). Today's build never produced a fresh ELF.
- All other release validation scripts pass: `check-mcp-package-smoke`, `check-executable-size-budgets`, `check-loader-dependency-closure`, `check-native-binary-dependency-closure`, `check-core-runtime-smoke`, `check-mcp-native-smoke`, `check_release_payload`.
- Bootstrap-from-scratch script accepts `--target=simpleos-x86_64`; the lane is wired (lines 25/97/126/127/137 of `scripts/bootstrap/bootstrap-from-scratch.sh`). Failure is at native-build, not at lane plumbing.

## Fix paths (not yet attempted)

1. Tighten `--entry-closure` to also drop transitively referenced cross-arch runtime stubs (e.g. `rt_arm64_*` should not survive in an x86_64 closure).
2. Audit class-metadata symbol emission: if `apps__shell__shell_app__VfsManager` is referenced as a type name in an object, the corresponding class descriptor must be emitted.
3. Fix Cranelift `ireduce.i32` from f32 (proper `fcvt_to_uint` / `fcvt_to_sint` intermediate). Without the stub fallback, this would surface as a compiler bug rather than masking link failure.
