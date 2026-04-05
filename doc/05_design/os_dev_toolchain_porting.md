# SimpleOS Development Toolchain Porting Roadmap

## Current State (2026-04-06)

### What SimpleOS Already Has
- SSH server (Ed25519 auth, port 22)
- Shell (50+ builtins, pipes, redirects, job control)
- VFS with FAT32 driver
- Full TCP/IP network stack (Ethernet, IPv4, TCP, UDP, ICMP)
- Process management (spawn_binary, ELF loading, signals)
- Package manager (dependency resolution)
- Build tool (simple_make — Makefile-compatible)
- Vi-like text editor
- POSIX compatibility layer (sockets, pipes, signals, FD table)
- Cryptography (Ed25519, AES-GCM, SHA-256/512)
- VCS app (file-level snapshots via VFS)

### What's Missing for Self-Hosted Development
- Full libc implementation
- Dynamic linker/loader
- Cross-compilation toolchain on SimpleOS
- Larger memory support (currently 128MB QEMU default)

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

## Phase 5: Git/VCS (1-2 months, after Phase 3)

### Options
- **SimpleOS VCS** (implemented) — file-level snapshots, adequate for local dev
- **libgit2 port** — C library, ~100K LOC, needs libc + zlib + OpenSSL
- **Partial git port** — only plumbing commands

### Recommendation
Phase 5.1: Use SimpleOS VCS for immediate needs
Phase 5.2: Port libgit2 after libc is available (Phase 3)

## Phase 6: jj (Jujutsu) VCS (12+ months)

jj is Rust — requires Phase 4 completion. Long-term goal.

## Gap Analysis: Bootstrap Self-Build

| Capability | Status | Gap |
|-----------|--------|-----|
| File I/O (read/write source) | VFS + FAT32 | Need VFS service wiring |
| Process spawn (compiler) | spawn_binary syscall | Ready |
| Memory allocation (heap) | Heap + mmap | May need >128MB |
| Object file output | Cranelift backend | Ready |
| ELF linking | Missing | Need minimal linker |
| Shell for builds | 50+ builtins | Ready |
| Build orchestration | simple_make | Ready |
| Source file discovery | VFS readdir | Ready |
| Network (packages) | TCP/IP + HTTP | Ready |

## Recommended Bootstrap Path

1. Cross-compile Simple compiler on host → ship on FAT32 image
2. Boot SimpleOS in QEMU with disk image
3. Run Simple compiler to compile hello_world.spl
4. Gradually build up to self-hosting
