# SimpleOS C toolchain policy: clang only (2026-09-25)

**SimpleOS's default and only supported C/C++ compiler is clang (the
`ormastes/llvm-project` fork, branch `simpleos`). GCC is not used anywhere in
the SimpleOS toolchain — do not invoke it, do not add build steps that require
it, and do not document it as an alternative.**

## Why clang

- The in-repo toolchain lane (`src/os/port/llvm`, plan
  `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`) ports clang
  and ld.lld to `*-unknown-simpleos` targets: freestanding driver, static
  ET_EXEC output with zero INTERP segments, `__simpleos__`/`__SIMPLEOS__`
  predefines, auto-generated `ld.lld` link lines (crt0 + `simpleos.ld` +
  `-lsimpleos_c` + `-lclang_rt.builtins-*`).
- Guest-runnable static toolchains are built and verified for both
  `x86_64-unknown-simpleos` and `aarch64-unknown-simpleos`
  (`build-os-llvm/cross-*/bin/clang-20`, ~113–114 MB each); the aarch64 lane
  is the default on aarch64 hosts (no x86 emulation).
- The self-host milestone (rebuild clang by clang on SimpleOS QEMU) requires
  the clang driver; a second C toolchain would double the port surface for no
  gain.

## Current exceptions being removed (tracking)

- The Rust seed's runtime-C compilation
  (`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`,
  `target_c_compiler`) still selects `aarch64-linux-gnu-gcc` and friends for
  host-side C objects. This is a build-host detail, not an OS toolchain
  choice, but per this policy it must move to clang (host `clang` /
  `--target=` cross clang). Tracked in
  `doc/08_tracking/todo/seed_host_c_compiler_switch_to_clang.md`.
- Cross-build scripts that probe `*-gcc` for linking keep a compatibility
  fallback until the switch lands; new code must not extend gcc usage.

## Practical rules

1. Guest images stage `clang`, `ld.lld`, `llvm-ar` (8.3-safe FAT32 names) —
   never `gcc`/`cc1`/`collect2`.
2. SOSIX/POSIX compatibility work targets what clang+lld need to build
  FreeBSD-like sources (see the SOSIX interface design docs), not gcc
   extensions.
3. Build scripts set `-j10` (or the host's core count when larger jobs are
   requested) for every parallel build stage, per repo policy.
