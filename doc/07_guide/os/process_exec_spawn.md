# How SimpleOS Loads and Runs Executables

## Overview

SimpleOS supports loading and executing static ELF64 binaries and SMF (Simple Module Format) sheath packages. The full pipeline transforms a filesystem path into a running process with a properly initialized user stack, argv/envp arrays, and an auxiliary vector following the System V ABI.

The loading pipeline has five stages:

1. **Path Resolution** -- locate executable bytes on disk or in the initramfs
2. **Format Detection** -- determine if the payload is ELF, SMF, or unsupported
3. **ELF Parsing** -- validate headers and extract PT_LOAD segment layout
4. **Image Building** -- construct a `UserProcessImage` with entry point, segments, and stack
5. **Scheduler Handoff** -- register the new task and begin execution

## Supported Formats

### ELF64 Static Executables

SimpleOS accepts ELF64 static executables for x86_64, RISC-V 64, and RISC-V 32 architectures. The kernel validates:

- Magic bytes: `\x7FELF`
- Class: ELFCLASS64 (or ELFCLASS32 for RV32)
- Data encoding: little-endian only (ELFDATA2LSB)
- Type: `ET_EXEC` (static executable)
- Machine: `EM_X86_64` (62), `EM_RISCV` (243), or `EM_AARCH64` (183)

Dynamic linking is **not supported**. All executables must be statically linked.

### SMF Sheath Format

SMF (Simple Module Format) packages use a 128-byte trailer at EOF-128 with magic bytes `SMF\0` (83, 77, 70, 0). An SMF file can embed a native ELF stub that the kernel extracts and loads through the standard ELF pipeline. When the SMF header's `stub_size` field is nonzero, the kernel extracts the embedded ELF bytes and delegates to the ELF loader. See `doc/07_guide/simpleos_executable_format.md` for format details.

## Resolution Chain

When `resolve_executable_bytes(path, arch)` is called, the kernel tries these sources in order:

1. **Synthetic test entries** -- test-injected entries (skipped in production)
2. **Initramfs** -- zstd-compressed cpio archive set by the boot chain via `set_initramfs_blob()`; paths starting with `/` are looked up here first
3. **VFS** -- the in-kernel VFS layer (`g_vfs_read_executable_bytes`)
4. **App Registry Aliases** -- FAT32 short-name aliases (`/SYS/APPS/CLANGSMF.SMF`) and root aliases (`/CLANGSMF.SMF`) resolved via `app_registry_fat32_alias()` and `app_registry_root_alias()`
5. **Legacy stubs** -- hardcoded RV32/RV64 proof-of-concept ELF stubs for early boot smoke tests

On success, the function returns `Ok([u8])`. On failure, it returns `Err(text)` with POSIX-style errno prefixes:

| Prefix | Meaning |
|--------|---------|
| `EINVAL` | Empty or invalid path |
| `ENOENT` | File not found in any source |

## Spawn API: spawn_path(path, argv, envp)

The userspace spawn API lives in `src/os/userlib/process.spl`:

```
use os.userlib.process.{spawn_path}

val result = spawn_path("/sys/apps/hello", ["hello", "--name", "world"], ["HOME=/root"])
match result:
    case Ok(pid):
        println("Child PID: {pid}")
    case Err(errno):
        println("Spawn failed: {errno}")
```

### Function Signature

```
fn spawn_path(path: text, argv: [text], envp: [text]) -> Result<u32, i32>
```

- **path**: Filesystem path to the executable (must not be empty)
- **argv**: Argument vector. If empty, defaults to `[path]` so the child always sees `argv[0]`
- **envp**: Environment variable vector (e.g., `["HOME=/root", "PATH=/usr/bin"]`)
- Returns `Ok(pid)` on success, `Err(errno)` on failure (22 = EINVAL for empty path)

### Syscall ABI

`spawn_path` invokes **syscall 13** (SpawnBinary):

| Register | Content |
|----------|---------|
| arg0 | path pointer |
| arg1 | path length |
| arg2 | marshaled argv pointer (or 0) |
| arg3 | marshaled envp pointer (or 0) |

Argv and envp are marshaled into contiguous byte buffers by `sosix_marshal_string_vector()`. The layout is:

```
[string_0 bytes, NUL, string_1 bytes, NUL, ...,
 offset_0 (u64 LE), offset_1 (u64 LE), ...,
 NULL_terminator (8 zero bytes)]
```

## execve: In-Place Image Replacement

The exec syscall (**syscall 59**) replaces the current process image while preserving PID and file descriptors:

1. Validates path pointer and length (rejects null, oversized paths)
2. Copies path bytes from userspace via `_copy_user_bytes()`
3. Resolves executable bytes via `resolve_executable_bytes_from_path_bytes()`
4. Optionally copies argv/envp from userspace via `vmm_copyin_string_vector()`
5. Tears down the old address space via `vmm_teardown_user_space()`
6. Builds a new `UserProcessImage` from the loaded ELF
7. Replaces the current task's image in the scheduler

Error codes returned by exec:

| Code | Meaning |
|------|---------|
| -EINVAL (22) | Null pointer or zero-length path |
| -ENAMETOOLONG (36) | Path exceeds `MAX_BINARY_PATH_LEN` |
| -EFAULT (14) | Cannot copy bytes from userspace |
| -2 | Executable not found (ENOENT) |

## The Full Pipeline (Step by Step)

### 1. Path Resolution

```
val bytes_result = resolve_executable_bytes("/sys/apps/hello", Architecture.X86_64)
```

The resolver walks the resolution chain (initramfs, VFS, aliases, stubs) and returns the raw file bytes.

### 2. Format Detection and Normalization

```
fn _normalise_executable_bytes(data: [u8], arch: Architecture) -> Result<[u8], text>
```

If the data starts with `SMF\0` magic (at EOF-128 or offset 0), the SMF sheath's embedded ELF stub is extracted. If it starts with ELF magic (`\x7FELF`), the data is used directly. Otherwise, the format is rejected.

### 3. ELF Parsing

```
val elf = load_user_executable(native_data, arch)?
```

The ELF parser validates the header, checks architecture compatibility, and extracts PT_LOAD segments into `ElfLoadSegment` records containing virtual address, file offset, file size, memory size, flags, and alignment.

### 4. Image Building

```
val image = build_user_process_image(path, data, arch, argv, envp)?
```

The image builder:
- Computes stack size (scales with binary size, 8 MB floor, 128 MB cap)
- Builds the SysV initial stack frame with argc, argv pointers, envp pointers, and auxiliary vector
- Constructs `UserProcessImage` with entry point, stack layout, and mapped segments

### 5. Scheduler Handoff

The scheduler receives the `UserProcessImage` and:
- Creates a new `TaskControlBlock` (for spawn) or replaces the current one (for exec)
- Maps PT_LOAD segments into the new address space via `segment_mapper`
- Copies the initial stack frame to the user stack region
- Sets the instruction pointer to `image.entry` and stack pointer to `image.initial_sp`
- Marks the task as runnable

## Architecture Support

| Architecture | Status | Notes |
|-------------|--------|-------|
| x86_64 | Full | Primary target, complete pipeline |
| RISC-V 64 | Full | ELF64 static, tested with proof binaries |
| RISC-V 32 | Full | ELF32 static, tested with proof binaries |
| ARM64 | Partial | Freestanding closure with runtime ELF helpers |
| ARM32 | Stub | Dispatch stubs only, no real loading |

## Examples

### Shell Spawning a Child Process

```
# From the SimpleOS shell
val result = spawn_path("/sys/apps/ls", ["ls", "-la", "/home"], [])
match result:
    case Ok(pid):
        wait_(pid)
    case Err(e):
        println("Error: {e}")
```

### Desktop Application Launcher

```
# The desktop app launcher uses the app registry
use os.kernel.loader.app_registry.{app_registry_lookup}

val entry = app_registry_lookup("/sys/apps/editor")
if entry != nil:
    val e = entry.unwrap()
    spawn_path(e.canonical_path, [e.canonical_path], [])
```

### Programmatic fork+exec Pattern

```
# fork() is syscall 57 -- returns child PID in parent, 0 in child
# exec() is syscall 59 -- replaces the current image

# Currently, fork/exec are kernel-level only (no userlib wrappers yet).
# Use spawn_path() for the common case of launching a new process.
# The kernel internally handles the fork+exec lifecycle when spawn_path
# delegates to the SpawnBinary syscall.
```

## Error Codes

| Error | Value | Context |
|-------|-------|---------|
| EINVAL | 22 | Empty path, null pointer |
| ENOENT | 2 | File not found |
| ENAMETOOLONG | 36 | Path exceeds maximum length |
| EFAULT | 14 | Invalid userspace pointer |
| ENOEXEC | 8 | Invalid executable format (bad ELF magic) |
| ENOMEM | 12 | Insufficient memory (fork failure) |

## Related Files

| File | Purpose |
|------|---------|
| `src/os/userlib/process.spl` | Userspace spawn API (`spawn_path`) |
| `src/os/sosix/process.spl` | SOSIX process facade, argv marshaling |
| `src/os/kernel/ipc/syscall.spl` | Syscall dispatcher (fork=57, exec=59, spawn=13) |
| `src/os/kernel/loader/executable_source.spl` | Path-to-bytes resolution |
| `src/os/kernel/loader/elf_loader.spl` | ELF header parsing and validation |
| `src/os/kernel/loader/process_image.spl` | ELF-to-UserProcessImage builder |
| `src/os/kernel/loader/segment_mapper.spl` | PT_LOAD segment-to-page mapping |
| `src/os/kernel/loader/stack_builder.spl` | SysV initial stack frame builder |
| `src/os/kernel/loader/app_registry.spl` | Application registry and alias resolution |
| `src/os/kernel/loader/smf.spl` | SMF sheath format parser |
| `src/os/kernel/memory/vmm.spl` | Virtual memory manager, teardown |
