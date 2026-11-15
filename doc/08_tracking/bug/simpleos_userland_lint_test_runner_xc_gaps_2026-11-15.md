# SimpleOS userland cross-build of `lint` / `test-runner`: concrete gaps (2026-11-15)

- Status: open
- Found: 2026-11-15, WSL Ubuntu-24.04. Builder `~/xc/simple-p2` (phase 2, sha256 prefix fcf9ad14c5e3d5f2, NOT stage2-admitted). Source `main` 1139820f170.
- Recipe: `scripts/os/simpleos-native-build.shs`, minus the admission gate:
  `native-build --source src/compositions/kernel_llvm_cranelift --source src --backend cranelift --runtime-bundle simple-core --entry-closure --entry <entry> --target <triple>`,
  with `SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_SIMPLE_CORE_PATH=build/os/simple-core-simpleos/libsimple_runtime.a`.
  Sysroot: `sh src/os/port/llvm/sysroot.shs`, which produces `build/os/sysroot/{lib/crt0.o,lib/libsimpleos_c.a,lib/libsimple_runtime_native.a,share/simpleos/simpleos.ld}`. Link is `ld.lld` (`link_simpleos_x86_64`).

## Gaps
1. **Only x86_64 has a userland link path.** `link_simpleos_arm64` links the freestanding `examples/09_embedded/simple_os/arch/arm64/boot/crt0.S` kernel image, and `link_simpleos_riscv64` links a kernel image (image header, kernel `linker.ld`). Neither consumes `simpleos-sysroot-{aarch64,riscv64}.shs`, so a user ELF cannot be produced for aarch64 or riscv64.
2. **The per-file worker fails on the lint closure (x86_64):** `FILE-WORKER-E-CLOSURE-INCOMPLETE: import-closure surface missing for src/lib/common/string_core.spl` (and `text_bytes.spl`), although the log shows that surface `released seq=89`. A MIR aggregate failure follows, `failed_modules=376`. NB_RC=1 after 7:46, RSS 2.1 GB.
   The same first error hits x86_64 test, aarch64 lint and aarch64 test, so it is target-independent (it happens in the parse phase).
2b. **The riscv64 lint and test builds are rejected:** `BACKEND_SESSION_AUTHORITY: load rejected: BACKEND_PLUGIN_TARGET: riscv64gc-unknown-simpleos`. The cranelift backend plugin does not admit the triple, although `is_simpleos_riscv64_target` lists it.
3. **The simple-core archive fails (x86_64):** `error=archive_part_failed:core_any_ops`, i.e. "per-file route selected but the file-worker pool produced no sealed ledger".
   - **Status: verification-pending (2026-11-15).** Two causes were found:
     - The real compile error was a HIR failure at `core_any_ops.spl:12:5`: `unresolved name: f64`. The source called `f64.from_bits`, a primitive static call that the pure-Simple compiler does not resolve. Fix: a pure IEEE-754 decoder that keeps -0.0 and computes pow2 by squaring.
     - The ledger message itself came from `--clean` on the per-file pool. The shard prepass returns no ledger, and the strict route refuses that, which masked the HIR error. A second problem: in-process, `--clean` fails with "failed to remove clean cache scope" when the dir is absent (`driver_aot_native_output.spl`, `_sffi_dir_remove_all` on a missing dir). This one is an open compiler bug.
     - Parts are now built with `--threads 1` and without `--clean`.
     - Open compiler gaps: `f64.from_bits` should resolve, and `--clean` should accept an absent scope dir.
     - Test: `test/01_unit/runtime/simple_core_archive_part_buildable_spec.spl`.
     - Result: core_any_ops plus 17 other parts now build (18 of 20). The **next blocker** is `core_string`: HIR rejects `__simple_rt_string_char_code_at` and `__simple_rt_string_byte_at` as "reserved for compiler-generated text calls". This is still open.
4. **On `main`, `runtime_native.c` calls `link()`.** SimpleOS libc does not declare it, and there are no hard links on SimpleOS; the sysroot cross-compile breaks. A local workaround was used: an ENOSYS stub.
   - **Status: verification-pending (2026-11-15).** The kernel has no link syscall (`src/os/kernel/ipc/syscall.spl` has unlink 39 and rename 44 only) and FAT32 cannot hold hard links, so `src/os/libc/simpleos_fs.c` `link()` now returns -1 with `errno = ENOSYS` and issues no syscall; declared in `include/unistd.h`. Test: `test/01_unit/os/libc/simpleos_link_enosys_test.c` (host clang, red before / green after). The runtime cross-compile census (`sosxc_rt_census.sh`) reports 0 errors.
5. **No 32-bit SimpleOS userland exists.** The triples exist only as constants (`simpleos_target_v1.spl`: i686, armv7, riscv32imac) and LLVM-port strings. Other facts:
   - There is no i686 or armv7 `is_simpleos_*` predicate and no link function for either.
   - riscv32 has a freestanding route only.
   - No 32-bit crt0, libc build or sysroot exists.
   - `check-simpleos-x86-32-user-elf.shs` assembles a hand-written ELF32 payload; it is not compiler output.
6. **The in-guest smoke cannot run.** `check-simpleos-hello-world-in-guest-ovmf.shs` (x86_64, OVMF) has no override for staging an arbitrary user ELF, and no artifact exists to stage.
