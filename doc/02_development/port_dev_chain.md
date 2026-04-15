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
| LLVM / clang | ✅ | ✅ | ✅ ToolChain class + compiler-rt OS | ✅ I3 green (1040-byte ELF) | ❌ |
| Rust / rustc | ✅ | ✅ | ✅ libstd PAL os/args/env/time/stdio | ✅ I4 green (2056-byte ELF, out-of-tree) | ❌ |
| Simple (self-host) | ✅ | ✅ LLD FFI | ✅ bootstrap hardening + IF-09 verify | ✅ | ⚠️ partial |

Legend: ✅ done · ⚠️ in progress / trial pending · ❌ not started

### Wave-4 Landed (2026-04-15)

#### Phase-2: cross-toolchain green

- **I3 LLVM cross-clang green.** `build/os/llvm/cross-x86_64/bin/clang --target=x86_64-unknown-simpleos`
  compiles `hello.c` → `hello.o` (1040-byte ELF).
  Fixes: `ec87deb5ef` (drop cross-toolchain-file) · `f874b685c1` (add Release build type) ·
  `71fd4286b0` · `b0e99c4461`.
- **I4 Rust cross-build green** (out-of-tree recipe).
  `bash scripts/build_rust_hello_simpleos.sh` produces `hello_rs` ELF (2056 bytes, `_start` symbol).
  Script commit: `e25b0de45c`. Root cause: 11 edition-2024 ghost crates in
  `src/compiler_rust/vendor/` colliding with pinned nightly-2024-09-01 (cargo 1.82) vs
  default-nightly `rustc-literal-escaper` dep. Fix: out-of-tree build with empty
  `CARGO_HOME`, falls back to crates.io-vendored `compiler_builtins v0.1.123` (edition 2021).
- **LLVM compiler-rt SimpleOS variant built.**
  `build/os/llvm/cross-x86_64/lib/clang/20/lib/x86_64-unknown-simpleos/libclang_rt.builtins.a`
  (198K). Script commit: `5fe74ee9ec`.

#### Wave-4 gap-roadmap items

- **W4-K3** FAT32 BPB parser + cluster-to-lba + real mount — `def2569894` main. 22/22 fat32 tests pass.
- **W4-D1** FAT32 disk image builder (real BPB + FAT + root dir + 1 payload) — `fdb701e1d8` main. 223 lines.
- **W4-S3** ELF symbol-table compare in bootstrap_native_verify (prefixes: `spl_handle_`, `simpleos_`, `rt_`) — `05b552c4e8`. 3/3 tests.
- **W4-A1** compiler-rt SimpleOS CMake variant — `6f4502542` in ormastes/llvm-project:simpleos (wired via `5fe74ee9ec` main).
- **W4-R4** `Command::spawn/wait/kill` trampoline to libc — `66e5ce1c` in ormastes/rust:simpleos.
- **W4-R5** `Thread::new/join/yield_now` trampoline to pthread — `cf43f553` in ormastes/rust:simpleos.
- **W4-D2** `Fat32Filesystem.mount()` call site wired (scaffold log; no BlockDevice implementor on main yet) — `2a6bbb32c3`.
- **W4-K1 predecessor (wave-3a)** real COW `clone_task` scaffold (shallow TCB clone + fresh TaskId alloc + ready-queue enqueue) — `d339203a4f`.

#### Phase-3 spec hardened

`test/os/port/e2e_qemu_smoke_spec.spl` now has 7 it-blocks (6 steps + IF-08 marker registry).
Commit `9e3bb12f3a`. Passes with `SIMPLEOS_QEMU_SMOKE` unset (lint-only mode).

---

## Phase-3 Readiness

| Gate | Status | What it unblocks |
|---|---|---|
| **Disk image bake** (I5 harness) | `4535d03b06` scaffold on main; harness→actual-artifact wiring in progress | Without it, QEMU cannot boot a persistent FAT32 disk image |
| **QEMU smoke actual run** | Spec has 7 it-blocks (lint-only); Phase-3 harness has not yet booted QEMU against a produced image | End-to-end boot validation; unblocks Stage2==Stage3 in-guest |
| **Rust libstd rebuild for sysroot** | R-4/R-5 trampolines committed upstream; current script uses system nightly, not fork's rebuilt libstd | In-guest Rust compilation (`rustc hello.rs`); follow-up: `./x.py build library --target x86_64-unknown-simpleos --stage 1` (~15–40 min) |

**Wave-4b remaining:** K-1 page-table COW, K-3 readdir/read/write + BlockDevice probe(),
D-1 multi-payload, R-1/R-2/R-3 Unsupported residues in libstd PAL (fs, os, args, env, time, stdio),
libsimpleos_c genuine fork/exec kernel-backed impl.

---

### Wave-3 Landed (2026-04-14)

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
| `fork` / `exec` | 🟡 Wave-4a partial | COW `clone_task` scaffold landed (`d339203a4f`); `spl_handle_fork/exec` still return ENOSYS; wave-4b wires page-table COW + ELF load |
| FAT32 disk image | ✅ Wave-4a landed | Real BPB + FAT + root dir builder (`fdb701e1d8`); mount call site wired (`2a6bbb32c3`); BlockDevice implementor pending wave-4b |
| Cargo network access | ❌ Permanent | No network stack in guest; `--offline` + vendored crates only |
| Rust libstd threads | 🟡 Wave-4a trampolines | `Thread::new/join/yield_now` → pthread (`cf43f553` rust fork); libstd rebuild pending |
| Rust libstd net | ❌ Deferred | No guest socket support this cycle |
| Rust libstd process | 🟡 Wave-4a trampolines | `Command::spawn/wait/kill` → libc (`66e5ce1c` rust fork); remaining PAL residues wave-4b |
| Stage2 == Stage3 convergence | 🟡 Wave-4a symbol-table | `verify_native_convergence` now compares `spl_handle_/simpleos_/rt_` symbol counts (`05b552c4e8`); actual in-guest run pending QEMU harness |

---

## Related Docs

- [simpleos_layout.md](../04_architecture/simpleos_layout.md) — src/os vs examples boundary
- [libc_coverage_audit.md](../04_architecture/libc_coverage_audit.md) — full POSIX surface audit
- [llvm_cross_build.md](llvm_cross_build.md) — LLVM cross-build steps
- [rust_cross_build.md](rust_cross_build.md) — Rust cross-build steps
- [bare_metal_integration.md](../04_architecture/bare_metal_integration.md) — baremetal runtime notes
- [simpleos_launch_modes.md](../04_architecture/simpleos_launch_modes.md) — QEMU launch modes
