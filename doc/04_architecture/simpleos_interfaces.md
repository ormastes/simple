# SimpleOS Port-Dev-Chain Interfaces — Frozen Contracts

**Status:** Locked 2026-04-15. PRs that change a frozen signature must update
this file in the same commit.

**Owner:** port-dev-chain maintainers. Changes require review from that group.

---

## Table of Contents

- [IF-01 Kernel syscall ABI](#if-01-kernel-syscall-abi)
- [IF-02 Fork/exec kernel contract](#if-02-forkexec-kernel-contract)
- [IF-03 libc C ABI (POSIX subset)](#if-03-libc-c-abi-posix-subset)
- [IF-04 Rust libstd PAL contract](#if-04-rust-libstd-pal-contract)
- [IF-05 LLVM sysroot layout](#if-05-llvm-sysroot-layout)
- [IF-06 Initramfs format + manifest](#if-06-initramfs-format--manifest)
- [IF-07 FAT32 disk image](#if-07-fat32-disk-image)
- [IF-08 QEMU boot serial protocol](#if-08-qemu-boot-serial-protocol)
- [IF-09 Bootstrap verifier contract](#if-09-bootstrap-verifier-contract)
- [IF-10 Cargo vendored protocol](#if-10-cargo-vendored-protocol)
- [IF-11 In-process LLD FFI](#if-11-in-process-lld-ffi)
- [IF-12 Stubs manifest format](#if-12-stubs-manifest-format)
- [IF-13 Interpreter-perf blocker for disk-image bake](#if-13-interpreter-perf-blocker-for-disk-image-bake)

---

## IF-01 Kernel syscall ABI

**Status:** frozen (existing 53 shims) + new-this-cycle (5 new syscalls below)

**Location:** `src/os/kernel/abi/syscall_shim.spl`
**Weak stubs:** `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`

### Calling convention

All syscall handlers share the same C-ABI signature: six `u64` arguments
(`a0`–`a5`) and an `i64` return value. The SYSCALL dispatch stub in
`examples/simple_os/arch/x86_64/boot/` copies `rdi, rsi, rdx, r10, r8, r9`
into those slots and places the return value in `rax`.

### Existing frozen shims (Wave 10F, 53 total — representative set)

```
# src/os/kernel/abi/syscall_shim.spl

@export("C", name: "spl_handle_debug_write")
fn spl_handle_debug_write(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64
  # syscall 60: a0 = byte to emit on COM1. Returns 0.

@export("C", name: "spl_handle_exit")
fn spl_handle_exit(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64
  # syscall 0: a0 = exit code. Does not return.

@export("C", name: "spl_handle_yield")
fn spl_handle_yield(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64
  # syscall 1: voluntarily yield CPU. Returns 0.

@export("C", name: "spl_handle_spawn")
fn spl_handle_spawn(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64
  # syscall 2: a0 = path ptr (user VA), a1 = path len.
  # Returns new TaskId on success, negative errno on failure.

@export("C", name: "spl_handle_wait")
fn spl_handle_wait(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64
  # Blocks until child exits. Returns exit status or negative errno.

@export("C", name: "spl_handle_getpid")
fn spl_handle_getpid(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_mmap")
fn spl_handle_mmap(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64
  # a0=addr_hint, a1=len, a2=prot, a3=flags, a4=fd, a5=offset

@export("C", name: "spl_handle_munmap")
fn spl_handle_munmap(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_mprotect")
fn spl_handle_mprotect(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_file_open")
fn spl_handle_file_open(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_file_read")
fn spl_handle_file_read(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_file_write")
fn spl_handle_file_write(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_file_close")
fn spl_handle_file_close(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_ipc_send")
fn spl_handle_ipc_send(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_ipc_recv")
fn spl_handle_ipc_recv(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_net_socket")
fn spl_handle_net_socket(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "spl_handle_clock_gettime")
fn spl_handle_clock_gettime(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> i64

@export("C", name: "shim_init")
fn shim_init(sched: Scheduler, ipc: IpcManager, klog: KernelLog)
  # Boot-time initializer. Call once before any SYSCALL can arrive.
```

Full list of 53 shims: see `_shim_keepalive()` in `syscall_shim.spl` lines 108–172.

### NEW syscalls — new-this-cycle

These five symbols are added in this cycle. Weak stubs must be added to
`baremetal_stubs.c`; strong overrides live in `syscall_shim.spl`.

```
@export("C", name: "spl_handle_fork")
fn spl_handle_fork() -> i64
  # Returns child pid in parent, 0 in child, -ECHILD on failure.

@export("C", name: "spl_handle_exec")
fn spl_handle_exec(path_ptr: u64, argv_ptr: u64, envp_ptr: u64) -> i64
  # Returns -1 on failure; does not return on success.

@export("C", name: "spl_handle_wait")
fn spl_handle_wait(pid: i64, wstatus_ptr: u64, options: i32) -> i64
  # Typed overload for the POSIX-style wait4; replaces the raw 6-arg form
  # for new libc callers. The raw 6-arg shim remains for compat.

@export("C", name: "spl_handle_pipe")
fn spl_handle_pipe(fds_ptr: u64) -> i64
  # Writes two i32 fds to *fds_ptr (read end, write end). Returns 0 or -errno.

@export("C", name: "spl_handle_dup2")
fn spl_handle_dup2(oldfd: i32, newfd: i32) -> i64
  # Duplicates oldfd onto newfd. Returns newfd or -errno.
```

**Consumers:** `src/os/libc/simpleos_process.c`, `src/os/libc/simpleos_process_wait.c`,
`src/os/port/init/`

### Wave 1 — Minix gap-fill syscalls (2026-04-17)

N = 98 (max existing = 97, SetHostname).

Implemented (dispatcher + shim wired):

```
sys_privctl       = 98   # G11: per-task kernel privilege table (SET/GET mask, ADD/REMOVE peer)
sys_grant         = 99   # G12: issue cross-task memory region grant → grant_id
sys_revoke        = 100  # G12: revoke a grant by id
sys_safecopy_from = 101  # G12: bounds-checked read through a grant
sys_safecopy_to   = 102  # G12: bounds-checked write through a grant
sys_mmap          = 103  # G13: map virtual address range into current task's space
sys_munmap        = 104  # G13: unmap virtual address range from current task's space
```

Reserved (documented only — no dispatcher entry; wired by owning agent):

```
sys_clock_get     = 105  # service agent
sys_schedule      = 106  # service agent
sys_schedctl      = 107  # service agent
```

**Files changed:** `src/os/kernel/types/capability_types.spl` (PrivilegeMask, Grant, SystemPrivilege),
`src/os/kernel/ipc/capability.spl` (PrivilegeTable, GrantTable),
`src/os/kernel/ipc/syscall.spl` (dispatcher cases + handlers),
`src/os/kernel/abi/syscall_shim.spl` (5 new @export shims + 2 G13 shims),
`src/os/kernel/types/vmspace_types.spl`, `src/os/kernel/memory/vmm.spl` (called, not modified).

---

## IF-02 Fork/exec kernel contract

**Status:** new-this-cycle

**Location:** `src/os/kernel/` (Scheduler implementation)

SimpleOS uses an exokernel model — there is no Unix-style fork that copies a
process context in the kernel. Instead the Scheduler exposes three primitive
operations that together implement POSIX fork+exec semantics.

### Scheduler contract

```
# src/os/kernel/scheduler/scheduler.spl

fn Scheduler::clone_task(self, parent: TaskId) -> Result<TaskId, KernelError>
  # Creates a new task with a COW page-table clone of parent.
  # Parent returns child_id (> 0); child starts at same rip+rsp but
  # syscall return value is 0 (matches POSIX fork() semantics).

fn Scheduler::exec_into(self, task: TaskId,
                        argv: List<text>, envp: List<text>) -> Result<(), KernelError>
  # Resolves argv[0], builds a UserProcessImage, and delegates to exec_image.
  # argv/envp are materialized on the new stack by the process-image builder.
  # TaskId is preserved across the exec; the old mapping tree is freed.

fn Scheduler::wait_for(self, parent: TaskId, child: Option<TaskId>,
                       options: i32) -> Result<(TaskId, i32), KernelError>
  # Blocks parent until a child exits.
  # child == None means "any child" (POSIX waitpid(-1, ...)).
  # options: WNOHANG (0x1) for non-blocking poll.
  # Returns (exited_pid, exit_status). Zombie entry removed after return.
```

### Memory model

- COW: parent page tables are marked read-only at `clone_task` time. A page
  fault in either task triggers a physical copy before resuming.
- Exec: `exec_into` allocates a new page table tree, maps the ELF segments,
  and swaps it atomically. The old tree and all COW pages are freed.
- Zombies: exited children remain in `Scheduler::exited_tasks` until
  `wait_for` collects them. Uncollected zombies are reaped when the parent
  exits.

**Consumers:** `src/os/libc/simpleos_process.c`, `src/os/port/init/`,
`spl_handle_fork`, `spl_handle_exec` (IF-01)

---

## IF-03 libc C ABI (POSIX subset)

**Status:** frozen

**Location:** `src/os/libc/include/` (headers), `src/os/libc/` (C sources)
**Built artifact:** `build/os/sysroot/lib/libsimpleos_c.a`

### Key header signatures (verbatim from `src/os/libc/include/`)

```c
/* unistd.h */
int open(const char *path, int flags, ...);
int fcntl(int fd, int cmd, ...);

/* dirent.h */
DIR           *opendir(const char *name);
int            closedir(DIR *dirp);
void           rewinddir(DIR *dirp);

/* dlfcn.h */
void *dlopen(const char *path, int mode);
void *dlsym(void *handle, const char *name);
int   dlclose(void *handle);
char *dlerror(void);

/* assert.h */
void __assert_fail(const char *expr, const char *file,
                   unsigned int line, const char *func);

/* locale.h */
char *setlocale(int category, const char *locale);

/* math.h */
double frexp(double x, int *exp);
double ldexp(double x, int exp);
double scalbn(double x, int n);
float  frexpf(float x, int *exp);
float  ldexpf(float x, int exp);
float  scalbnf(float x, int n);
```

Full header tree: `src/os/libc/include/{stdio,stdlib,string,stdint,stddef,
stdbool,stdarg,signal,setjmp,pthread,math,limits,locale,fcntl,errno,
dirent,dlfcn,assert,wchar,time,unistd}.h` plus `sys/` subdirectory.
`sys/wait.h` is part of the C process ABI and exposes `wait`, `waitpid`,
`WNOHANG`, and the standard `WIF*`/`W*STATUS` status helpers.

### libc syscall numbers

The C libc process/fd-composition wrappers use the normal `simpleos_syscall`
trampoline. Reserved IDs are:

| libc API | syscall |
|---|---:|
| `fork` | 57 |
| `execve` | 59 |
| `waitpid` | 61 |
| `pipe` / `pipe2` | 62 |
| `dup2` / `dup3` | 63 |
| `dup` | 64 |
| `dlopen` | 65 |
| `dlsym` | 66 |
| `dlclose` | 67 |

These IDs intentionally avoid existing time (`50`/`51`) and debug-write
(`60`) syscalls. Process and FD syscalls are backed by scheduler/FD-table
handlers; dynamic-library syscalls are backed by the kernel dylib registry.

Dynamic library loading follows the same async-first rule as file I/O:
native SimpleOS code uses `os.posix.dylib_async`, while libc `dlopen`,
`dlsym`, and `dlclose` are synchronous compatibility wrappers. The libc
self-handle (`dlopen(NULL, ...)`) resolves core libc symbols immediately;
path-backed SMF/ELF library loads use syscalls `65`-`67` to validate bytes,
create kernel handles, resolve `_start`/`main`, and refcount close. Full PIC
relocation, import binding, and unload-safe link namespaces remain future
shared-object mapper work.

**Consumers:** `src/compiler_rust/`, LLVM cross-toolchain, any userspace ELF
compiled for `x86_64-unknown-simpleos`.

---

## IF-04 Rust libstd PAL contract

**Status:** frozen (stage-1 scaffold)

**Location:** `$HOME/rust/library/std/src/sys/pal/simpleos/mod.rs`
(fork of upstream `unsupported` PAL, tracked separately from this repo)

```rust
//! SimpleOS PAL — stage 1 scaffold (derived from unsupported)
#![deny(unsafe_op_in_unsafe_fn)]

mod common;
pub use common::*;
```

The PAL delegates all unimplemented syscalls to `common.rs` stubs that panic
with `"not supported"`. As IF-01 syscalls land, each stub is replaced with a
real `syscall` instruction wrapper targeting the SimpleOS SYSCALL ABI.

**Required env var for cross-compile:**
```sh
export SDKROOT=$SIMPLEOS_SYSROOT   # = build/os/sysroot/
```

**Consumers:** `src/compiler_rust/`, `scripts/build_rust_simpleos_cross.shs`

---

## IF-05 LLVM sysroot layout

**Status:** frozen

**Location:** `build/os/sysroot/` (generated by `src/os/port/llvm/sysroot.shs`)
**Source of truth:** `doc/02_development/simpleos_sysroot_layout.md`

| Deliverable | Build path | Source |
|---|---|---|
| Headers | `build/os/sysroot/include/` | `src/os/libc/include/` |
| Static libc | `build/os/sysroot/lib/libsimpleos_c.a` | `src/os/libc/` Makefile |
| C runtime | `build/os/sysroot/lib/crt0.o` | `src/os/libc/simpleos_crt0.S` |
| Userspace LD script | `build/os/sysroot/share/simpleos/simpleos.ld` | embedded in `sysroot.shs` |

Linker script constants (userspace):

- Entry point: `_start`
- Load base: `0x10000000`
- No multiboot header (kernel script at `examples/simple_os/arch/x86_64/linker.ld`
  uses `_entry32` + `0x100000` — do not mix these)

Rebuild:
```sh
sh src/os/port/llvm/sysroot.shs
```

**Consumers:** `scripts/build_llvm_simpleos_cross.shs`,
`scripts/build_rust_simpleos_cross.shs`, any `cargo build --target x86_64-unknown-simpleos.json`

---

## IF-06 Initramfs format + manifest

**Status:** frozen

**Location:** `src/os/port/initramfs_pack.spl`
**Output:** `build/os/initramfs.img.zst` (newc cpio + zstd)

### Configuration class

```
# src/os/port/initramfs_pack.spl

class PayloadEntry:
    host_path: text
    guest_path: text
    is_dir: bool

class PackConfig:
    simple_binary: text      # default: build/bootstrap/stage3/simple_simpleos
    llvm_prefix: text        # default: build/os/llvm/cross/bin
    sysroot: text            # default: build/os/sysroot
    source_tree: text        # default: src
    output: text             # default: build/os/initramfs.img.zst
    staging: text            # default: build/os/initramfs-staging
    payloads: List<PayloadEntry>
```

### populate_staging contract

`populate_staging` copies in order:
1. Simple compiler binary → `/bin/simple`
2. LLVM tools (`clang lld llvm-ar llvm-nm llvm-ranlib llvm-objdump llvm-objcopy llvm-strip`) → `/usr/bin/`
3. Sysroot tree → `/usr/`
4. Source tree → `/src/`
5. Extra `PayloadEntry` items (user-supplied `--payload HOST:GUEST`)
6. Placeholder `/sbin/init`

Image is then packed with `cpio --format=newc` and compressed with `zstd`.

QEMU loads it via `-initrd build/os/initramfs.img.zst`.

**Consumers:** `src/os/port/port_all.spl`, QEMU runner (`src/os/qemu_runner.spl`)

---

## IF-07 FAT32 disk image

**Status:** frozen

**Location:** `src/os/services/fat32/fat32.spl`
**Spec:** `test/unit/os/services/fat32/fat32_spec.spl`

### Core traits and types

```
# src/os/services/fat32/fat32.spl

trait BlockDevice:
    fn read_sector(lba: u64, buffer: [u8]) -> Result<bool, text>
    fn write_sector(lba: u64, data: [u8]) -> Result<bool, text>
    fn sector_size() -> u32   # must return 512

class Fat32Bpb: ...           # BPB field layout per FAT32 spec
class Fat32DirEntry: ...      # 32-byte directory entry

class Fat32Driver: ...        # stateful driver; constructed over a BlockDevice

# Attribute constants
FAT32_ATTR_READ_ONLY  : u8
FAT32_ATTR_HIDDEN     : u8
FAT32_ATTR_SYSTEM     : u8
FAT32_ATTR_VOLUME_ID  : u8
FAT32_ATTR_DIRECTORY  : u8
FAT32_ATTR_ARCHIVE    : u8
FAT32_ATTR_LFN        : u8

# Cluster chain sentinels
FAT32_FREE : u32   # 0x00000000
FAT32_EOC  : u32   # >= 0x0FFFFFF8
FAT32_BAD  : u32   # 0x0FFFFFF7
```

**Consumers:** `src/os/kernel/` VFS layer, disk-image builder in
`src/os/port/`, installer

**Landed (wave-4, 2026-04-15):** `disk_image_bake.spl` produces a 32 MiB
FAT32-signature stub (BPB jump + OEM + `0x55AA` + zero pad) — commit
`a4ba52b6c5`. **Wave-4d (same day)** resolves the real payload embed via the
`rt_file_truncate` extern (commit `a47cd179a3`): structural bytes (~150 KiB)
written via `rt_file_write_bytes`, kernel zero-extends to 32 MiB via
`ftruncate()`. Verified: `build/os/simpleos_disk.img` is exactly 33554432 bytes,
`file` reports FAT32 BPB with SIMPLEOS OEM, and a `HELLORS` 8.3 directory entry
lands at sector 288 pointing to `first_cluster=3`. Multi-payload embed is a
wave-4a-builder limit (HELLOCO not yet written); follow-up.

---

## IF-08 QEMU boot serial protocol

**Status:** frozen

**Location:** `examples/simple_os/` (kernel boot path)
**Transport:** COM1 serial at 115200 baud (default QEMU `-serial stdio`)

### Marker tokens (from kernel source scan)

All markers follow the pattern `[tag] message` on a single line terminated by
`\n`. Consumers (test harness, CI) grep for these exact bracket-prefixed tags.

| Tag | Meaning |
|---|---|
| `[boot]` | Early boot progress (e.g. `[boot] init`, `[boot] calling`) |
| `[fault]` | CPU exception/fault (includes `rip`, `rflags`, `errcode`, `cr*`, `cs`) |
| `[dev-test]` | Device enumeration test output |
| `[gpu-test]` | GPU smoke test output |
| `[grant]` | Capability grant events |
| `[hello]` | Userspace hello-world confirmation |
| `[desktop]` | Desktop/compositor lifecycle |
| `[download]` | In-guest download progress |
| `[native-verify]` | Bootstrap convergence verifier (see IF-09) |

The test harness (`src/os/qemu_runner.spl`) waits for `[boot] init` within 30 s
as the liveness signal. A `[fault]` marker causes immediate test failure.

**Consumers:** `src/os/qemu_runner.spl`, CI boot-test scripts

---

## IF-09 Bootstrap verifier contract

**Status:** frozen

**Location:** `src/os/port/bootstrap_native_verify.spl`

### Entry point

```
# src/os/port/bootstrap_native_verify.spl

fn main() -> i32
  # Exit codes:
  #   0  — convergence confirmed (byte-identical OR same auto_stub count)
  #   2  — source tree missing under /src/
  #   3  — Stage 2 build failed
  #   4  — Stage 3 build failed
  #   5  — binaries diverge (byte offset + stub counts differ)
  #   6  — could not read one or both binaries
```

### Stage paths (fixed)

```
STAGE2_BIN = "/build/stage2/simple"
STAGE3_BIN = "/build/stage3/simple"
ENTRY      = "/src/app/cli/main.spl"
SOURCES    = ["/src/compiler", "/src/lib", "/src/app"]
```

### Convergence algorithm

1. `_check_source_tree_present()` — all SOURCES dirs + ENTRY must exist.
2. `_build_stage(STAGE2_BIN)` — compile from `/src/` using `/bin/simple`.
3. `_build_stage_with(STAGE2_BIN, STAGE3_BIN)` — compile from `/src/` using Stage 2.
4. `_byte_compare(STAGE2_BIN, STAGE3_BIN)` — byte-identical check.
5. Fallback: `_auto_stub_count_equal` — counts `auto_stub` ELF symbols via
   `compiler.backend.introspection.elf_symbols.count_symbols_matching`.

**Note:** Steps 2–3 currently return `Err` (in-process build not yet wired).
They unblock once `spl_handle_fork`/`spl_handle_exec` (IF-01) land.

**Consumers:** CI in-guest boot test, `src/os/port/verify_all.spl`

---

## IF-10 Cargo vendored protocol

**Status:** frozen

**Location:** `src/compiler_rust/.cargo/config.toml`

SimpleOS does not provide fork/exec at build time (until IF-01/02 land), so
`cargo` cannot spawn `git` or `curl`. All crates must be pre-vendored on the
host and committed to `vendor/`.

### Frozen config block

```toml
[source.crates-io]
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "vendor"
```

### Protocol

1. On host: `cargo vendor --respect-source-config` inside `src/compiler_rust/`.
2. Commit `vendor/` contents to repo.
3. Cross-build: `cargo build --target x86_64-unknown-simpleos.json` reads from
   `vendor/` with no network access.

**Consumers:** `src/compiler_rust/`, `scripts/build_rust_simpleos_cross.shs`,
in-guest self-build once fork/exec lands

---

## IF-11 In-process LLD FFI

**Status:** new-this-cycle

**Location (Simple wrapper):** `src/compiler/70.backend/linker/lld_ffi.spl`
**Location (C++ shim):** `src/compiler/70.backend/linker/lld_shim.cpp`

### C++ shim declaration

```cpp
// src/compiler/70.backend/linker/lld_shim.cpp
extern "C" int rt_lld_link_elf(uint64_t argc, const char** argv);
```

Implementation calls:
```cpp
lld::elf::link(
    llvm::ArrayRef<const char*>(argv, argc),
    llvm::outs(),
    llvm::errs(),
    /*exitEarly=*/false,
    /*disableOutput=*/false
)
```

### Simple FFI binding

```
# src/compiler/70.backend/linker/lld_ffi.spl

extern fn rt_lld_link_elf(argc: u64, argv_ptr: u64) -> i32
  # Calls lld::elf::link via C++ shim.
  # Returns 0 on success, non-zero on LLD exit-code failure.

fn lld_link_elf(args: List<text>) -> Result<(), text>:
    """High-level wrapper. Marshals args into a null-terminated argv array,
    calls rt_lld_link_elf, and converts non-zero returns to Err(stderr)."""
```

### Link requirements

`lld_shim.cpp` must be compiled with the same LLVM headers used to build the
Simple compiler's Cranelift/LLVM backend. Link with `-llldELF -llldCommon
-lLLVM` (or the monolithic `-lLLVM-19`).

**Consumers:** `src/compiler/70.backend/`, `src/os/port/build_tools/`,
bootstrap stage that links SimpleOS userspace ELFs

---

## IF-12 Stubs manifest format

**Status:** frozen

**Location:** `src/os/port/stubs_manifest.spl`
**Output:** `build/os/stubs_manifest.sdn`

### SDN manifest schema

```
[stubs_manifest
  [binary "<path-to-binary>"]
  [total_count <integer>]
  [groups
    [group
      [name "<prefix>"]
      [count <integer>]
      [symbols
        "<symbol_name>"
        ...
      ]
    ]
    ...
  ]
]
```

### Classifier prefixes (in priority order)

`gpu`, `cuda`, `vulkan`, `opencl`, `gfx`, `net`, `http`, `tls`, `ssl`,
`sqlite3`, `sqlite`, `db`, `torch`, `ml`, `audio`, `video`, `crypto`.

Symbols not matching any prefix are grouped under `"other"`.

### Entry point

```
fn main()
  # Invoked as: bin/simple run src/os/port/stubs_manifest.spl [-- options]
  # Options: --binary <path>, --output <path>
  # Scans binary with `nm`, extracts auto_stub_* and _stub_panic_* symbols,
  # groups by prefix (descending count), writes SDN manifest, prints summary.
```

**Consumers:** CI stub-audit step, `src/os/port/audit_stubs.spl`,
`src/os/port/verify_all.spl`

---

## IF-13 Interpreter-perf blocker for disk-image bake

**Status:** resolved-wave-4d (via candidate A; see `rt_file_truncate` below)

**Location:** `src/os/port/disk_image_bake.spl`, `src/os/port/disk_image.spl`

Building a 32 MiB FAT32 byte-buffer under the Simple **interpreter** is
prohibitively slow: even with the array-doubling trick `pad = pad + pad`,
the allocator-copy per iteration is O(n) and timed out at 30 s for ≥1 MiB
of payload. The native/compiled Simple backend does not hit this ceiling.

**Current workaround (wave-4, commit `a4ba52b6c5`):** `disk_image_bake.spl`
emits a 32 MiB FAT32-signature stub — BPB jump + OEM tag + `0x55AA` sector
signature + zeroed pad — without embedding real payloads. Kernel boot can
still probe the image but no files are readable.

**Wave-4d landed (candidate A, commit `a47cd179a3`):** `rt_file_truncate(path, size) -> bool`
extern added to `src/runtime/runtime_native.c` + interpreter bridge at
`src/compiler_rust/compiler/src/interpreter_extern/{file_io.rs,mod.rs}`.
`disk_image.spl:build()` now writes structural bytes (~150 KiB) via
`rt_file_write_bytes` then calls `rt_file_truncate` to have libc `ftruncate()`
zero-extend the tail. Verified end-to-end: the full bake completes and
produces a 32 MiB image with HELLORS payload embedded at cluster 3.
Interpreter `img.push(0u8)` in FAT-table builders is still the residual
~5-minute bottleneck for the ~150 KiB structural prefix; further wins
would come from a `[u8].extend_zeros(n)` stdlib helper or a native-compiled
bake (candidate B, deferred).

**Consumers:** Phase-2 Track I5 (unblocked), Phase-3 QEMU smoke.

---

## Verification

### Drift detection

A CI lint step should grep this doc for file paths appearing after
`**Location**:` and verify that each path exists in the repository. Signature
drift (e.g. a renamed `@export` symbol) must be caught by the port-dev-chain
integration test suite, which compiles a probe that imports each frozen symbol.

Suggested CI command:
```sh
grep -oP '(?<=\*\*Location\*\*: )`[^`]+`' doc/04_architecture/simpleos_interfaces.md \
  | tr -d '`' | while read p; do
      test -e "$p" || echo "MISSING: $p"
  done
```

### Change policy

PRs that rename, remove, or change the type signature of any frozen interface
listed here **must** update this file in the same commit. The PR description
must include the label `interface-change` and receive approval from a
port-dev-chain maintainer before merge.

### Ownership

| Interface | Primary owner file |
|---|---|
| IF-01, IF-02 | `src/os/kernel/abi/syscall_shim.spl` |
| IF-03 | `src/os/libc/` |
| IF-04 | `rust/library/std/src/sys/pal/simpleos/` |
| IF-05 | `src/os/port/llvm/sysroot.shs` |
| IF-06 | `src/os/port/initramfs_pack.spl` |
| IF-07 | `src/os/services/fat32/fat32.spl` |
| IF-08 | `examples/simple_os/arch/x86_64/` |
| IF-09 | `src/os/port/bootstrap_native_verify.spl` |
| IF-10 | `src/compiler_rust/.cargo/config.toml` |
| IF-11 | `src/compiler/70.backend/linker/lld_ffi.spl` |
| IF-12 | `src/os/port/stubs_manifest.spl` |

---

## Changelog

### 2026-04-15 — wave-4 landings

New wave-4 code citations for interfaces with real implementations this cycle:

- **IF-02** (Fork/exec kernel contract) — `Scheduler::clone_task` real COW scaffold
  and `Scheduler::exec_into` resolves `argv[0]`, builds a process image, maps
  PT_LOAD segments plus initial stack bytes, and preserves the task ID through
  `exec_image`. `wait_for` is implemented through waitpid-compatible collection.
- **IF-07** (FAT32 disk image) — `Fat32Filesystem.mount()` real BPB parser + cluster-to-lba:
  `src/os/services/fat32/fat32.spl:394` (commit `def2569894`). 22/22 fat32 tests pass.
  Mount call site wired at `2a6bbb32c3` (scaffold log pending BlockDevice implementor).
- **IF-09** (Bootstrap verifier contract) — `verify_native_convergence` now compares ELF
  symbol-table counts for prefixes `spl_handle_`, `simpleos_`, `rt_`:
  `src/os/port/bootstrap_native_verify.spl:199` (commit `05b552c4e8`). 3/3 tests pass.

### 2026-04-15 (afternoon) — wave-4b expansion

- **IF-07 BlockDevice probe** — `src/os/drivers/virtio/virtio_blk.spl:79`, commit `1948b85f0d` —
  `static fn probe() -> VirtioBlkDriver?` MMIO-scans `0xFEB00000..+32*0x200` for virtio-blk magic
  `0x74726976`; returns first matching device or nil. Unblocks the real-mount path in e2e tests.
- **IF-07 FAT32 readdir** — `src/os/kernel/fs/fat32.spl:161`, commit `2646266e96` —
  `Fat32Filesystem.mount()` now stashes the root-dir cluster sectors into `self.root_dir_data`
  (wave-4b shortcut); `readdir("/")` walks that buffer without a FAT-chain traversal.
  `next_cluster` + `read_cluster_chain` are stubbed public for wave-4c.
- **IF-02 COW scaffold** — `src/os/kernel/memory/vmm.spl:532`, commit `6bdd540c6e` —
  `fn vmm_cow_clone_pages(pml4_phys: u64) -> u64` marks parent PTEs read-only and returns a
  shallow-cloned PML4. Scheduler wire at `src/os/kernel/scheduler/scheduler.spl:514` calls
  `vmm_cow_clone_pages(parent.address_space)` inside `clone_task`.
- **IF-08 Phase-3 QEMU runner** — `src/os/qemu_runner.spl:1191`, commit `a08fe8f697` —
  `fn boot_disk_image_serial(image: text, timeout_ms: i64) -> (text, text, i32)` boots a raw disk
  image and returns captured serial output; `test/os/port/e2e_qemu_smoke_spec.spl:46` dispatches
  all 6 Phase-3 steps by grepping the shared capture for `[phase-3-*]` markers.

Cross-toolchain milestones (not IF-id changes, recorded here for traceability):

- I3 LLVM cross-clang green: `ec87deb5ef` + `f874b685c1`. Artifact: `build/os/llvm/cross-x86_64/bin/clang`.
- I4 Rust cross-build green (out-of-tree): `e25b0de45c`. Script: `scripts/build_rust_hello_simpleos.shs`.
- W4-A1 compiler-rt SimpleOS variant: `5fe74ee9ec` (main) / `6f4502542` (llvm-project fork).
  Archive: `build/os/llvm/cross-x86_64/lib/clang/20/lib/x86_64-unknown-simpleos/libclang_rt.builtins.a`.

### 2026-04-15 (afternoon) — wave-4c landings

- **I5 bake stub (IF-07)** — `src/os/port/disk_image_bake.spl`, commit `a4ba52b6c5` —
  `disk_image_bake` executes end-to-end and produces a 32 MiB FAT32-signature stub
  artifact. Real payload embed deferred to wave-4d; see IF-13 for the interpreter-perf
  blocker description and candidate fixes.
- **Sysroot compiler-rt install (IF-05)** — commit `0cfd73477f` —
  `libclang_rt.builtins.a` is now staged into
  `build/os/sysroot/lib/clang/20/lib/x86_64-unknown-simpleos/` as part of
  `sysroot.shs`, so `clang --sysroot=$SIMPLEOS_SYSROOT` resolves builtins without
  a separate `-L` flag (W4-A1 follow-up).
- **Wave-4b changelog publish** — commit `2d52ba74c7` — published the wave-4b
  landing changelog section above.
- **Rust fork target-spec typed-enum migration (Agent C, IF-04 adjacent)** —
  commits `8ae9c376` and `5de52281` on `ormastes/rust:simpleos` (NOT in this
  repo; cited for traceability). `8ae9c376` migrates the four
  `x86_64-unknown-simpleos*` target specs from legacy string fields to typed
  `Arch`/`Env`/`Os` enums and adds `Os::SimpleOs` to the `target_spec_enum!`
  registry (5 files). `5de52281` makes `pub fn target()` → `pub(crate) fn target()`
  on all four specs to satisfy `unreachable_pub` and fixes an `Lld::No`
  `link_args` assertion. Rust stage1 libstd remains red on 58 PAL errors
  (cfg_select gaps, extern-block `unsafe` in edition 2024, unresolved
  `libc::__errno_location` / `strerror_r` / `c_char`, `os::unix` missing,
  `unsafe_op_in_unsafe_fn` in `thread.rs`); separate agent E in flight.

### 2026-04-15 (evening) — wave-4d landings

Completes the Phase-3 prerequisite chain. All Rust/clang/disk-image pieces
needed for the QEMU smoke are in place; remaining blocker is the kernel ELF
build workstream (separate wave).

- **IF-13 resolved — `rt_file_truncate` extern (IF-07 follow-up)** — commit
  `a47cd179a3`. Added `src/runtime/runtime_native.c` POSIX `ftruncate` wrapper
  plus interpreter bridge in `src/compiler_rust/compiler/src/interpreter_extern/{file_io.rs,mod.rs}`.
  `src/os/port/disk_image.spl:build()` now writes structural bytes via
  `rt_file_write_bytes` and delegates zero-pad to the kernel via `rt_file_truncate`.
  After Rust bootstrap seed rebuild (cargo 2m40s) + redeploy (simple `cp` to
  `bin/release/.../simple`), the full bake completes in 5m31s and produces a
  32 MiB FAT32 image with the `HELLORS` payload embedded at cluster 3
  (verified: exact size, FAT32 BPB + SIMPLEOS OEM, HELLORS 8.3 entry at root
  sector 288).
- **Rust stage1 libstd GREEN (Agent E, IF-04 adjacent)** — fork commits
  (multiple) on `ormastes/rust:simpleos`. Fixed 58 libstd PAL errors: cfg_select
  branches added to `library/std/src/sys/{random,alloc,io,thread_local}/mod.rs`;
  `extern "C"` blocks wrapped with `unsafe` per Rust 2024 edition;
  `unsafe_op_in_unsafe_fn` wraps in `pal/simpleos/thread.rs`; local extern
  bindings for `__errno_location` / `strerror_r` / `c_char` in PAL files;
  new `library/std/src/os/simpleos.rs` module. Build produces
  `libstd-*.rlib` (1.2 MB), `libcore-*.rlib` (1.2 MB), `liballoc-*.rlib`
  (320 KB), `libcompiler_builtins-*.rlib` (3.6 MB) under
  `/home/ormastes/rust/build/*/stage1/lib/rustlib/x86_64-unknown-simpleos/lib/`.
- **Stage1 sysroot verification script (Agent H)** — commit `8974a794a8`.
  New `scripts/build_rust_hello_with_stage1.shs` (173 lines) cross-compiles
  against the fork's stage1 sysroot via `--sysroot` + bare triple
  (fork registers simpleos as a built-in target). libstd smoke build
  produces a 35544-byte ELF with 39 demangled `std::/alloc::/core::` symbols
  linked, proving the rlibs are usable, not just on-disk. Quirks documented:
  stage1 rustc requires bare triple (not JSON), `${SDKROOT}` requires a literal
  symlink (rust-lld doesn't env-expand), and `hello_rs/src/main.rs`'s hand-written
  `_start` collides with `crt0.o` — use `fn main()` instead for stage1 builds.
- **LLVM `__simpleos__` predefines (Agent I, IF-05 adjacent)** — commit `3b33ba807`
  on `ormastes/llvm-project:simpleos` (NOT in this repo; cited for traceability).
  Adds `SimpleOSTargetInfo<Target>` class in `clang/lib/Basic/Targets/OSTargets.h`
  with `getOSDefines()` emitting `__simpleos__`, `__SIMPLEOS__`, `__unix__`,
  `__ELF__`, `_REENTRANT`; wires `case llvm::Triple::SimpleOS:` into
  `Targets.cpp` x86_64 OS switch. Verified via
  `clang -dM -E --target=x86_64-unknown-simpleos`. Negative test against
  `x86_64-linux-gnu` confirms gating is correct.
- **Initramfs real bake (community, IF-06 follow-up)** — commit `14cff9cec6`.
  Initramfs is now a real cpio payload (not a 7-byte stub) built as part
  of the disk bake flow.
