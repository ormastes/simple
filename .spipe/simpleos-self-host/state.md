# SStack State: simpleos-self-host

## User Request
> Complete roadmap item 2: LLVM/Rust/Simple Self-Host in SimpleOS. Get clang, rustc, and the simple compiler all running as file-loadable apps inside SimpleOS, achieving closed self-host bootstrap.

## Task Type
feature

## Refined Goal
> Build the `simple` compiler as a static ELF for SimpleOS x86_64, pack it into the initramfs, and verify it loads and executes inside SimpleOS QEMU. Add file-write syscall support so the compiler can produce output. Then cross-compile clang and rustc as static SimpleOS executables. End result: SimpleOS can compile Simple source files using its own hosted compiler.

## Acceptance Criteria
- [ ] AC-1: `native-build` produces a valid static ELF for SimpleOS x86_64 (the `simple` compiler binary)
- [ ] AC-2: The compiler binary is packed into the SimpleOS initramfs (zstd+cpio)
- [ ] AC-3: SimpleOS loads and runs the `simple` binary as a user process (posix_spawn path)
- [ ] AC-4: File-write syscall exists so compiler output can be persisted to FAT32
- [ ] AC-5: End-to-end: compile a trivial .spl file inside SimpleOS, producing an ELF that SimpleOS can load and run
- [ ] AC-6: clang (static) cross-compiled for SimpleOS and loadable as a user process
- [ ] AC-7: rustc (static) cross-compiled for SimpleOS and loadable as a user process
- [ ] AC-8: QEMU smoke test passes (scripted verification)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-11
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Feature slug:** simpleos-self-host

**Current state:**
- ELF SYMTAB bug fixed (Preemptible→Export + reemit_clean_macho weak-scope)
- SimpleOS has: x86_64 kernel, ELF loader, FAT32 VFS, process scheduler, posix_spawn, initramfs (zstd+cpio)
- Native-build infrastructure exists but `rt_native_build` is stub
- Missing: file-write syscall, dynamic linking, libc for hosted tools
- Cranelift codegen produces valid ELF objects now (SYMTAB fix)

**Key files:**
- `src/os/kernel/loader/elf_loader.spl` — ELF PT_LOAD segment parser
- `src/os/kernel/loader/executable_source.spl` — resolve_executable_bytes (initramfs + FAT32)
- `src/os/kernel/loader/process_image.spl` — build_user_process_image
- `src/os/kernel/ipc/syscall.spl` — syscall dispatch
- `src/os/port/simpleos_native_build_config.spl` — native-build target config
- `src/compiler_rust/compiler/src/codegen/cranelift.rs` — ELF emission
- `src/compiler_rust/compiler/src/codegen/common_backend.rs` — native-build entry

**Implementation strategy:**
- Stream A: native-build → static SimpleOS ELF for `simple` compiler
- Stream B: file-write syscall + FAT32 write support
- Stream C: initramfs packing + QEMU integration test
- Stream D: cross-compile clang/rustc static for SimpleOS (if feasible)

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
