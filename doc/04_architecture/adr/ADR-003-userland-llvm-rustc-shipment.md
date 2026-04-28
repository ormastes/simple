# ADR-003: Ship LLVM + rustc + Simple as Userland Binaries on SimpleOS

**Date:** 2026-04-28
**Status:** Accepted
**Supersedes:** the implicit "Simple binary only" stance recorded in
`doc/02_requirements/feature/app/bootstrap.md` and the bootstrap-strategy
research note `doc/01_research/local/bootstrap_strategy_research_2026-02-23.md`.

## Context

The Simple bootstrap chain on SimpleOS until now has been scoped to a single
deliverable: ship the Simple compiler binary in the FAT32 image so that a
booted SimpleOS instance can recompile its own source. The recorded
architectural decision was to defer everything else — `clang`, `lld`,
`libLLVM.so`, `rustc` — to the host toolchain.

In April 2026 the user explicitly overrode that scope. The new directive is
that a booted SimpleOS image must be able to compile C, Rust, and Simple
sources end-to-end, using `clang`, `rustc`, and `simple` loaded from the
in-image filesystem. This ADR records the override and the constraints it
imposes.

The supporting work already in place when this decision was made:

- `x86_64_fs_exec_spawn(path, argv, envp)` lands argv/envp threading
  (W-1 closed in commit `de51cc34d7`).
- FAT32 fast-path bake via `mkfs.fat` + `mcopy` bypasses the interpreter perf
  wall (commit `b233017dd2`).
- The Simple compiler is already baked as `/SIMPLSTC.SMF` (commit `7cc0ac9643`).
- The frozen interface contracts in `simpleos_interfaces.md` (IF-01..IF-13)
  cover 53 syscalls; IF-04 documents the Rust libstd PAL stage1 scaffold at
  the external fork `/home/ormastes/rust:simpleos`.

## Decision

SimpleOS will ship `clang`, `lld`, `libLLVM.so`, `rustc`, and `simple` as
userland binaries inside the FAT32 image, loadable by the in-OS ELF loader.

Concretely:

1. **libc:** Vendor musl 1.2.5 (MIT) as a subtree at `src/os/external/musl/`
   with a SimpleOS PAL overlay under `arch/simpleos-x86_64/`.
2. **Dynamic linker:** Use musl's `ld-musl-x86_64.so.1` as `PT_INTERP`. The
   kernel ELF loader parses `PT_INTERP` and `PT_LOAD` only, hands off auxv,
   and lets ld-musl perform `R_X86_64_*` relocations and `DT_NEEDED`
   resolution.
3. **C++ runtime:** Vendor LLVM's libcxx, libcxxabi, and libunwind
   (Apache-2.0) at the same revision as the in-tree LLVM. Exception
   unwinding uses libunwind's `dl_iterate_phdr` path (musl provides), so
   the kernel does not implement `__register_frame_info`.
4. **LLVM source:** External clone at `$HOME/llvm-project` pinned to a
   specific SHA, fetched on demand by `scripts/fetch_llvm_simpleos.shs`.
   In-image LLVM is built with `LLVM_TARGETS_TO_BUILD=X86` only.
5. **rustc link mode:** Static initially, then dynamic against the cross-built
   `libLLVM.so` once dlopen + TLS land.
6. **Simple in image:** Ship the Rust-built `simple` binary. Pure-Simple
   self-host on SimpleOS is out of scope for this ADR.
7. **Wave 2 syscalls:** Reserve 108=arch_prctl, 109=clone, 110=futex,
   111=exit_thread in IF-01. See `simpleos_interfaces.md` § "Wave 2 —
   userland dynamic toolchain".
8. **TLS:** Flip `has-thread-local: true` and `tls-model: "initial-exec"`
   in all four `src/os/port/rust/target/*-simpleos.json` specs once the
   kernel `arch_prctl(ARCH_SET_FS)` lands.

The earlier ADR `adr_rust_llvm_exclusion.md` (rust-llvm bootstrap-only)
remains accepted — that ADR is about which compilation paths count toward
the public LLVM family-completion claim, which is unrelated to whether
LLVM/rustc binaries are physically shipped in the OS image.

## Consequences

**Positive:**
- A booted SimpleOS image can self-compile C, Rust, and Simple programs
  without a host toolchain.
- The kernel loader gains a real ELF userland path (PT_INTERP + auxv) that
  also unblocks future ports of any dynamically linked Linux ELF.
- Wave 2 reserves the syscall numbers needed for pthreads and TLS, which
  every dynamic Linux binary needs anyway.

**Negative / trade-offs:**
- Image size jumps from ~32 MiB to ~150–280 MiB (FAT32 size knob bumped
  from 32 to 1024–2048 MiB). The bake fast-path keeps wall time under 30 s.
- The companion userland-runtime track (musl + libcxx + libunwind +
  pthread + dlopen) is a multi-week effort; see the implementation plan at
  `~/.claude/plans/complete-porting-llvm-rust-reactive-cosmos.md`.
- `process::Command` is deferred — there is no `cargo` in-image initially.
  rustc is invoked manually only.
- FAT32 LFN read parsing must land first (`libLLVM.so.18.1` and
  `ld-musl-x86_64.so.1` are unloadable with 8.3 names).

**Risks:**
- musl `clone()` flag-set must match the kernel's `sys_clone` exactly; any
  divergence breaks pthread immediately. Mitigation: implement only the
  exact flag set musl pthread uses; reject others with EINVAL.
- libunwind `dl_iterate_phdr` must see the kernel-loaded main image in the
  ld-musl link-map. If broken, add a `__dl_register_main_image` shim in
  `__libc_start_main`.
- Scheduler may not handle the 100+ threads rustc/lld want by default.
  Mitigation: cap with `RAYON_NUM_THREADS=2 LIBLLVM_THREADS=1` in the
  initramfs init env until scheduler scaling lands.

## Alternatives Considered

| Option | Pros | Cons |
|--------|------|------|
| **Bootstrap-only (Simple binary only)** | Matches the prior recorded decision; ~1–2 sprints | Fails the user's explicit ask; users still need a host toolchain to write C/Rust on SimpleOS |
| **Static clang/lld only (no rustc, no dynamic LLVM)** | 1–2 wks integration; no libcxx-shared, no dlopen | Reverses the recorded decision for LLVM but not Rust; awkward partial state |
| **Full toolchain (this ADR)** | Self-hosting OS for C/Rust/Simple; unblocks every future dynamic ELF port | 9.7–17.5 wks of work; depends on TLS gate going green first |

## References

- Implementation plan: `~/.claude/plans/complete-porting-llvm-rust-reactive-cosmos.md`
- Frozen contracts: `doc/04_architecture/simpleos_interfaces.md`
- Bootstrap requirement (amended in this cycle):
  `doc/02_requirements/feature/app/bootstrap.md`
- Prior ADR (still in effect): `doc/04_architecture/adr_rust_llvm_exclusion.md`
- TLS prerequisite (must land before Wave 2 syscalls):
  `doc/03_plan/agent_tasks/tls_live_bug_fix_restart.md`
