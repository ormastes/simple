# Port Dev Chain — SimpleOS QEMU Toolchain Index

**Date:** 2026-04-14

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

| Component | Phase 1 (fork+patch) | Phase 2 (embed-LLD) | Cross-build | In-guest |
|---|---|---|---|---|
| LLVM / clang | ✅ | ✅ | ⚠️ trial pending | ❌ |
| Rust / rustc | ✅ | ⚠️ in progress | ⚠️ trial pending | ❌ |
| Simple (self-host) | ✅ | N/A | ✅ | ⚠️ partial |

Legend: ✅ done · ⚠️ in progress / trial pending · ❌ not started

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

65 strong `spl_handle_*` functions override the weak baremetal stubs defined in
`examples/simple_os/`. The strong symbols are provided by the kernel library at
link time, ensuring syscall dispatch routes through the real kernel handlers
rather than the stub no-ops.

Key files:

- `src/os/kernel/abi/syscall_shim.spl` — 65 strong `spl_handle_*` implementations
- `examples/simple_os/arch/x86_64/boot/syscall_entry.s` — entry trampoline that
  calls the selected handler

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

| Item | Workaround / Notes |
|---|---|
| `fork` / `exec` | Not implemented; use embed-LLD (in-process link) instead of spawning a linker child process |
| Cargo network access | Network stack not available in guest; use `--offline` + vendored crates only |
| Rust libstd threads | `std::thread` PAL is a stub (panics); use single-threaded executors |
| Rust libstd net | `std::net` PAL is a stub; no socket support in guest at this stage |
| Rust libstd process | `std::process::Command` PAL is a stub; use embed-LLD path |

---

## Related Docs

- [simpleos_layout.md](../04_architecture/simpleos_layout.md) — src/os vs examples boundary
- [libc_coverage_audit.md](../04_architecture/libc_coverage_audit.md) — full POSIX surface audit
- [llvm_cross_build.md](llvm_cross_build.md) — LLVM cross-build steps
- [rust_cross_build.md](rust_cross_build.md) — Rust cross-build steps
- [bare_metal_integration.md](../04_architecture/bare_metal_integration.md) — baremetal runtime notes
- [simpleos_launch_modes.md](../04_architecture/simpleos_launch_modes.md) — QEMU launch modes
