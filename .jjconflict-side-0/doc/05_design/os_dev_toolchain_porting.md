# SimpleOS Development Toolchain Porting Roadmap

## Current State (2026-04-06)

### What SimpleOS Already Has
- SSH server (Ed25519 auth, port 22)
- Shell (40+ builtins: 26 core + 14 extended tools, pipes, redirects, job control)
- VFS with FAT32 driver
- Full TCP/IP network stack (Ethernet, IPv4, TCP, UDP, ICMP)
- Process management (spawn_binary, ELF loading, signals)
- Package manager (dependency resolution)
- Build tool (simple_make — Makefile-compatible)
- Vi-like text editor
- POSIX compatibility layer (sockets, pipes, signals, FD table)
- Cryptography (Ed25519, AES-GCM, SHA-256/512)
- VCS: native file-level snapshots + **git wrapper** + **jj wrapper** (NEW)
- **LLVM/Clang cross-build scripts** for 4 targets (NEW)
- **Rust cross-build** with core/alloc for 4 targets (NEW)
- **Minimal libc** with string/math extensions for toolchain bootstrap (NEW)
- **4 Rust target specs**: x86_64, aarch64, riscv64gc, riscv32imac (NEW)
- **CMake/Ninja/Make ports** under examples/ (NEW)
- **Bootstrap verification & cross-compilation scripts** (NEW)
- **Master verification script** (`verify_all.spl`) checking all layers (NEW)

### What's Missing for Self-Hosted Development
- Full libc implementation (minimal libc exists, needs POSIX extensions)
- Dynamic linker/loader
- Cross-compiled LLVM/Clang binary running ON SimpleOS (scripts ready, build needed)
- Cross-compiled Rust seed binary for SimpleOS (scripts ready, build needed)
- Larger memory support (currently 128MB QEMU default)

### Verification

```bash
# Run full verification of all layers
bin/simple run src/os/port/verify_all.spl

# Quick check (skip toolchain builds)
bin/simple run src/os/port/verify_all.spl -- --skip-slow --verbose
```

See: `doc/07_guide/platform/simpleos_dev_guide.md` for full usage guide.

## Phase 1: Self-Hosted Simple Compiler (1-2 months)

### Goal
Run `simple native-build` on SimpleOS to compile Simple programs.

### Prerequisites
1. VFS service connected to FAT32 with source files on disk image
2. ELF loader for spawning compiled binaries
3. simple_make integration for build orchestration
4. Linker available (port mold or use built-in linking)

### Steps
1. Cross-compile Simple compiler binary for SimpleOS target (x86_64 ELF, no libc)
2. Create SimpleOS-specific runtime stubs (rt_file_read_text → VFS syscalls)
3. Ship compiler binary on FAT32 disk image
4. Test: compile hello_world.spl on SimpleOS → produce ELF → run it

### Key Files
- `src/os/port/simpleos_native_build_config.spl` — sysroot configuration
- `src/compiler/80.driver/driver.spl` — compiler driver
- `src/app/cli/bootstrap_main.spl` — bootstrap entry

## Phase 2: Linker & Build System (2-3 months)

### Goal
Native linking on SimpleOS without external tools.

### Options
- **Option A**: Port mold (Rust, ~50K LOC) — fastest linker, needs Rust stdlib
- **Option B**: Implement minimal ELF linker in Simple (~5K LOC) — simpler but slower
- **Option C**: Use Cranelift backend's built-in object emission — already exists

### Recommendation
Option C (Cranelift) — already produces object files. Add a minimal ELF linker in Simple that can combine objects + resolve symbols. This avoids porting any external tools.

## Phase 3: C Compiler Toolchain (3-6 months)

### Goal
Compile C code on SimpleOS for porting external tools.

### LLVM/Clang Porting
- LLVM is ~15M LOC C++ — full port infeasible on SimpleOS initially
- Instead: cross-compile clang for SimpleOS target on host
- Ship as statically-linked binary on disk image
- Needs: libc (musl port), libstdc++ or libc++, ~1GB RAM

### Alternative: TinyCC (tcc)
- ~50K LOC C, self-hosting, simple to port
- Produces adequate code for bootstrapping
- Can cross-compile itself
- **Recommended as Phase 3 target**

### Steps
1. Port musl libc to SimpleOS (POSIX compat layer already exists)
2. Cross-compile tcc for SimpleOS
3. Test: compile a C hello world on SimpleOS
4. Use tcc to build larger C programs

## Phase 4: Rust Toolchain (6-12 months)

### Goal
Compile Rust code on SimpleOS (needed for Cranelift/compiler backend).

### Practical Path
1. Use mrustc (alternative Rust compiler in C++) — can bootstrap without rustc
2. Or: cross-compile Rust std for SimpleOS target on host
3. Ship pre-built rustc + cargo on SimpleOS disk image
4. Incremental: start with no_std Rust, add std features as OS matures

## Phase 5: Git/VCS (DONE — wrapper approach)

### Status: Implemented (2026-04-06)
- **SimpleOS VCS** (`src/os/apps/vcs/`) — native file-level snapshots, works baremetal
- **Git wrapper** (`src/os/apps/git/`) — delegates to host `git` binary, 15 commands
- **JJ wrapper** (`src/os/apps/jj/`) — delegates to host `jj` binary, 14 commands
- All three integrated into shell as `vcs`, `git`, `jj` commands

### Future: Native Git (after Phase 3)
- Port libgit2 (C, ~100K LOC) — requires libc + zlib + OpenSSL
- Or: implement git plumbing in Simple (pack files, SHA-1, refs)

## Phase 6: jj (Jujutsu) VCS — Native (12+ months)

Wrapper available now. Native port requires Rust (Phase 4).

## Gap Analysis: Bootstrap Self-Build

| Capability | Status | Gap |
|-----------|--------|-----|
| File I/O (read/write source) | VFS + FAT32 | Need VFS service wiring |
| Process spawn (compiler) | spawn_binary syscall | Ready |
| Memory allocation (heap) | Heap + mmap | May need >128MB |
| Object file output | Cranelift backend | Ready |
| ELF linking | Missing | Need minimal linker |
| Shell for builds | 40+ builtins | Ready |
| Build orchestration | simple_make + cmake/ninja/make ports | Ready |
| Source file discovery | VFS readdir | Ready |
| Network (packages) | TCP/IP + HTTP | Ready |
| VCS | Native + git/jj wrappers | Ready |
| C compiler (host→target) | LLVM cross-build scripts | Scripts ready |
| Rust core/alloc | Cross-build scripts | Scripts ready |
| Libc | Minimal (string, math, printf, mmap) | Needs POSIX extensions |
| Sysroot | Builder script (sysroot.shs) | Scripts ready |
| Target specs | 4 arch (x86_64, aarch64, riscv64, riscv32) | Ready |
| Bootstrap verification | verify + cross scripts | Ready |

## Recommended Bootstrap Path

1. Build sysroot: `bin/simple run src/os/port/deploy_toolchains.spl -- --stage sysroot`
2. Cross-compile LLVM/Clang for SimpleOS: `bin/simple run src/os/port/deploy_toolchains.spl -- --cross`
3. Cross-compile Simple compiler: `bin/simple run src/os/port/bootstrap_cross.spl -- --target x86_64-simpleos --package`
4. Ship compiler + sysroot + toolchain on FAT32 disk image
5. Boot SimpleOS in QEMU
6. Run `simple native-build` on SimpleOS to compile Simple programs
7. Verify convergence with `bootstrap_verify.spl`

## Scripts Reference

| Script | Purpose |
|--------|---------|
| `src/os/port/verify_all.spl` | Master verification (all 5 phases) |
| `src/os/port/deploy_toolchains.spl` | Sysroot + LLVM + Rust deployment |
| `src/os/port/bootstrap_verify.spl` | 3-stage bootstrap verification |
| `src/os/port/bootstrap_cross.spl` | Cross-compile Simple for SimpleOS |
| `src/os/port/llvm/build.spl` | LLVM/Clang build (host + cross) |
| `src/os/port/rust/build.spl` | Rust core/alloc build |
| `src/os/port/llvm/test_smoke.spl` | LLVM smoke tests |

Full guide: `doc/07_guide/platform/simpleos_dev_guide.md`
