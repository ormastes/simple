# Port Dev Chain — SimpleOS QEMU Toolchain Index

**Date:** 2026-04-15

## Goal

Run a complete developer toolchain inside a QEMU SimpleOS guest:

- `clang hello.c` — C compilation via LLVM/clang cross-built for SimpleOS
- `rustc hello.rs` — Rust compilation via rustc with SimpleOS target + libstd PAL
- `simple` Stage2 == Stage3 — Simple compiler self-host convergence inside the guest

All three compilers must link and execute statically against the SimpleOS libc layer.

---

## Repo Layout

| Location | Role |
|---|---|
| `src/os/` | Reusable OS library: drivers, kernel, compositor, libc shims, port build drivers |
| `examples/simple_os/` | QEMU integration harness: boot entries, linker scripts, baremetal stubs |
| `$HOME/llvm-project` | Fork `ormastes/llvm-project:simpleos` — LLVM + clang + lld with Phase 2 embed-LLD |
| `$HOME/rust` | Fork `ormastes/rust:simpleos` — rustc with SimpleOS target specs + libstd PAL scaffold |

See [simpleos_layout.md](../04_architecture/simpleos_layout.md) for the canonical
`src/os/` vs `examples/simple_os/` boundary rules.

---

## Component Status

| Component | Phase 1 fork | Phase 2 embed-LLD | Phase 3 wave-3 scaffolds | Cross-build | In-guest |
|---|---|---|---|---|---|
| LLVM / clang | ✅ | ✅ | ✅ ToolChain class + compiler-rt OS | ⚠️ trial pending | ❌ |
| Rust / rustc | ✅ | ✅ | ✅ libstd PAL os/args/env/time/stdio | ⚠️ trial pending | ❌ |
| Simple (self-host) | ✅ | ✅ LLD FFI | ✅ bootstrap hardening + IF-09 verify | ✅ | ⚠️ partial |

Legend: ✅ done · ⚠️ in progress / trial pending · ❌ not started

### Wave-3 Landed (2026-04-15)

- **IF-01** syscall ABI: `spl_handle_fork/exec/wait/pipe/dup2` scaffolds — kernel arc grew 65 → 70 strong handles.
- **IF-02** fork/exec contract: `Scheduler::clone_task / exec_into / wait_for` signatures.
- **IF-06** disk image: `src/os/port/disk_image.spl` offline FAT32 builder scaffold.
- **IF-07** FAT32 driver: `src/os/kernel/fs/fat32.spl` `Fat32Filesystem` scaffold.
- **IF-09** native verify: `verify_native_convergence(stage2, stage3)` public API.
- **IF-11** LLD FFI: `src/compiler/70.backend/linker/{lld_ffi.spl, lld_shim.cpp}`.
- Libc: `simpleos_fork.c` + `simpleos_ipc.c` trampolines (10 symbols).
- Rust fork: 5 libstd PAL modules (os, args, env, time, stdio).
- LLVM fork: SimpleOS ToolChain class + compiler-rt OS recognition + `__simpleos__`.

---

## How to Build

- **LLVM cross-build:** [llvm_cross_build.md](llvm_cross_build.md)
- **Rust cross-build:** [rust_cross_build.md](rust_cross_build.md)

---

## libc Coverage

Full audit: [libc_coverage_audit.md](../04_architecture/libc_coverage_audit.md)

Top-5 gaps recently closed:

1. `waitpid` — process wait stubs wired to syscall shim
2. `poll` — fd poll shimmed via kernel SYSCALL arc
3. `popen` / `pclose` — subprocess pipe stubs
4. `pthread_rwlock_*` — read-write lock POSIX stubs (no-op for single-threaded guest)
5. `pthread_cond_*` — condition variable stubs (no-op baseline)

---

## Kernel SYSCALL Arc

**70 strong** `spl_handle_*` functions override the weak baremetal stubs.
Wave-3 added 5: `fork` (57), `exec` (59), `wait` (61), `pipe` (22),
`dup2` (33). The strong symbols are provided by the kernel library at link
time, ensuring syscall dispatch routes through the real kernel handlers.

Key files:

- `src/os/kernel/abi/syscall_shim.spl` — 70 strong `spl_handle_*` implementations
- `examples/simple_os/arch/x86_64/boot/syscall_entry.s` — entry trampoline
- `src/os/kernel/log/markers.spl` — IF-08 serial-marker registry

The linker resolves strong over weak automatically; no explicit `--defsym` is needed.

---

## Initramfs Packer

`src/os/port/initramfs_pack.spl` packages the guest filesystem image.

New capabilities:

- `--payload HOST:GUEST` — inject an arbitrary host file at a guest path
- `--zstd` — compress the cpio archive with zstd (requires zstd on host)

Example:

```
simple run src/os/port/initramfs_pack.spl \
  --payload $HOME/llvm-project/build/bin/clang:/usr/bin/clang \
  --output initramfs.cpio.zst --zstd
```

---

## Stub Gating

`src/os/port/bootstrap_cross.spl` controls which subtrees are included in a
SimpleOS cross-build. The following subtrees are **excluded** from SimpleOS
builds to avoid pulling in unsupported host dependencies:

- `gpu/` and `gfx/`
- `net-tls/`
- `db/` (database drivers)

To audit which stubs are active in the current build tree:

```
scripts/audit_stubs.shs
```

The script lists every `@weak` symbol that has no corresponding strong override,
flagging anything that may silently no-op at runtime.

---

## Known Deferred Items

| Item | Status | Notes |
|---|---|---|
| `fork` / `exec` | 🟡 Wave-3 scaffolds | `spl_handle_*` + `scheduler.clone_task` return ENOSYS/sentinels; wave-4 wires COW clone + ELF load |
| FAT32 disk image | 🟡 Wave-3 scaffolds | `Fat32Filesystem` (IF-07) + `disk_image.build()` (IF-06) scaffolds; wave-4 adds BPB + writer |
| Cargo network access | ❌ Permanent | No network stack in guest; `--offline` + vendored crates only |
| Rust libstd threads | ❌ Deferred | `std::thread` Unsupported until cooperative scheduler lands |
| Rust libstd net | ❌ Deferred | No guest socket support this cycle |
| Rust libstd process | 🟡 Wave-3 scaffold | `std::process::Command` Unsupported; embed-LLD covers linker path |
| Stage2 == Stage3 convergence | 🟡 Wave-3 scaffold | `verify_native_convergence` does byte-equality; wave-4 compares symbol tables |

---

## Related Docs

- [simpleos_layout.md](../04_architecture/simpleos_layout.md) — src/os vs examples boundary
- [libc_coverage_audit.md](../04_architecture/libc_coverage_audit.md) — full POSIX surface audit
- [llvm_cross_build.md](llvm_cross_build.md) — LLVM cross-build steps
- [rust_cross_build.md](rust_cross_build.md) — Rust cross-build steps
- [bare_metal_integration.md](../04_architecture/bare_metal_integration.md) — baremetal runtime notes
- [simpleos_launch_modes.md](../04_architecture/simpleos_launch_modes.md) — QEMU launch modes
