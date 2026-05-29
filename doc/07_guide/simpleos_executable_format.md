# SimpleOS Executable Formats

## Overview

SimpleOS supports two executable formats:

1. **ELF64** (and ELF32 for RV32) -- standard static executables produced by GCC, Clang, or rustc
2. **SMF** (Simple Module Format) -- a sheath format that can embed a native ELF stub alongside Simple bytecode metadata

Both formats are loaded through the same kernel pipeline. SMF files are unwrapped first, and the embedded ELF stub is handed to the ELF loader.

## ELF64 Header Structure

SimpleOS requires the following ELF header fields:

### ELF Identification (e_ident, 16 bytes)

| Offset | Size | Field | Required Value |
|--------|------|-------|----------------|
| 0 | 4 | Magic | `\x7F E L F` (0x7F, 0x45, 0x4C, 0x46) |
| 4 | 1 | Class | 2 (ELFCLASS64) or 1 (ELFCLASS32 for RV32) |
| 5 | 1 | Data | 1 (ELFDATA2LSB, little-endian only) |
| 6 | 1 | Version | 1 (EV_CURRENT) |
| 7-15 | 9 | Padding | Ignored |

### ELF Header (64 bytes total for ELF64)

| Offset | Size | Field | Notes |
|--------|------|-------|-------|
| 16 | 2 | e_type | Must be 2 (ET_EXEC) |
| 18 | 2 | e_machine | 62 (x86_64), 243 (RISC-V), or 183 (AArch64) |
| 20 | 4 | e_version | Must be 1 |
| 24 | 8 | e_entry | Virtual address of program entry point |
| 32 | 8 | e_phoff | Program header table offset (typically 64) |
| 40 | 8 | e_shoff | Section header offset (ignored by loader) |
| 48 | 4 | e_flags | Architecture-specific flags |
| 52 | 2 | e_ehsize | ELF header size (64 for ELF64) |
| 54 | 2 | e_phentsize | Program header entry size (56 for ELF64) |
| 56 | 2 | e_phnum | Number of program header entries |
| 58 | 2 | e_shentsize | Section header entry size (ignored) |
| 60 | 2 | e_shnum | Number of section headers (ignored) |
| 62 | 2 | e_shstrndx | Section name string table index (ignored) |

### Validation Rules

The kernel ELF loader (`elf_loader.spl`) validates:

1. Magic bytes at offset 0-3 must be `\x7FELF`
2. Data encoding must be little-endian
3. ELF version must be `EV_CURRENT` (1)
4. ELF class must match the target architecture (ELFCLASS64 for x86_64/RV64/ARM64, ELFCLASS32 for RV32)
5. Machine type must match the target architecture
6. At least one PT_LOAD segment must be present

Validation failures return descriptive error messages:
- `"ELF too small for ident"` -- data is less than 16 bytes
- `"invalid ELF magic"` -- magic bytes don't match
- `"only little-endian ELF is supported"` -- big-endian data encoding
- `"unsupported ELF class"` -- class byte is not 1 or 2
- `"ELF class does not match target architecture"` -- wrong class for the target
- `"truncated ELF64 header"` / `"truncated ELF32 header"` -- insufficient data for full header

## PT_LOAD Segments

PT_LOAD segments describe regions of the ELF file that must be mapped into the process address space. The kernel extracts these from the program header table.

### Program Header Entry (56 bytes for ELF64)

| Offset | Size | Field | Description |
|--------|------|-------|-------------|
| 0 | 4 | p_type | 1 (PT_LOAD) for loadable segments |
| 4 | 4 | p_flags | Permission flags (PF_R=4, PF_W=2, PF_X=1) |
| 8 | 8 | p_offset | Offset of segment data in the file |
| 16 | 8 | p_vaddr | Virtual address to map the segment |
| 24 | 8 | p_paddr | Physical address (usually equals p_vaddr) |
| 32 | 8 | p_filesz | Size of segment data in the file |
| 40 | 8 | p_memsz | Size of segment in memory (>= p_filesz) |
| 48 | 8 | p_align | Alignment requirement |

### How Segments Are Mapped

The `segment_mapper.spl` module processes each PT_LOAD segment:

1. **Page alignment** -- virtual address and size are rounded to page boundaries (4 KB)
2. **Memory allocation** -- pages are allocated from the physical memory manager
3. **Data copy** -- `p_filesz` bytes are copied from the ELF file to the mapped pages
4. **BSS zeroing** -- bytes from `p_filesz` to `p_memsz` are zeroed (BSS section)
5. **Permission setting** -- page table entries are configured with R/W/X flags from `p_flags`

The `segment_mapper` validates:
- `file_size <= mem_size` (BSS must not be negative)
- Stack ranges must not underflow

## SMF Sheath Format

SMF (Simple Module Format) is SimpleOS's native package format. It can wrap a native ELF executable alongside Simple bytecode metadata.

### Header Location

SMF v1.1 places a 128-byte header trailer at **EOF-128** (the last 128 bytes of the file). Legacy test fixtures may use offset 0.

The loader checks EOF-128 first; if no magic is found there, it checks offset 0.

### Magic Bytes

```
Offset 0-3 of the trailer: [83, 77, 70, 0]  ("SMF\0")
```

### Trailer Layout (128 bytes)

| Offset | Size | Field | Description |
|--------|------|-------|-------------|
| 0 | 4 | magic | `SMF\0` (83, 77, 70, 0) |
| 44 | 8 | entry_point | Entry point address (u64 LE) |
| 52 | 4 | stub_size | Size of embedded native ELF stub (u32 LE) |
| 56 | 4 | data_offset | Offset to SMF data section (u32 LE) |
| 60 | 1 | role | Binary role identifier |
| 61 | 1 | arch | Target architecture |
| 62 | 1 | abi | ABI version |

### ELF Stub Extraction

When `stub_size > 0`, the SMF file contains an embedded native ELF executable. The kernel extracts it via `smf_extract_executable_stub_for_arch()`:

1. Parse the SMF header to get `stub_size`
2. Extract the first `stub_size` bytes of the file as the ELF stub
3. Verify the extracted bytes start with ELF magic
4. Pass the stub to the standard ELF loader

If the SMF has no embedded stub (`stub_size == 0`), the kernel checks whether the raw file bytes themselves start with ELF magic (legacy compatibility).

## Static vs Dynamic Linking

**Only static linking is supported.** SimpleOS does not have a dynamic linker (ld.so), shared library loader, or PLT/GOT resolution. All executables must be fully self-contained.

When compiling with external toolchains, always pass `-static` or equivalent flags.

## How to Compile an Executable for SimpleOS

### Using Clang (x86_64)

```bash
# Cross-compile a static x86_64 executable
clang -target x86_64-unknown-none-elf \
    -static -nostdlib -nostdinc \
    -ffreestanding \
    -o hello hello.c \
    -Wl,-e,_start \
    -Wl,--no-dynamic-linker
```

### Using Clang (RISC-V 64)

```bash
clang -target riscv64-unknown-none-elf \
    -march=rv64gc -mabi=lp64d \
    -static -nostdlib -nostdinc \
    -ffreestanding \
    -o hello hello.c \
    -Wl,-e,_start
```

### Using rustc (x86_64)

```bash
# With a custom target JSON or the x86_64-unknown-none target
rustc --target x86_64-unknown-none \
    -C link-arg=-nostdlib \
    -C link-arg=-static \
    -o hello hello.rs
```

### Using the Simple Compiler

The Simple compiler produces SMF sheath packages by default. For bare ELF output:

```bash
bin/simple build --target=x86_64 --format=elf hello.spl
```

### Verifying an Executable

Use `readelf` to check that the binary meets SimpleOS requirements:

```bash
readelf -h hello    # Check header (Class, Machine, Type)
readelf -l hello    # Check PT_LOAD segments
file hello          # Quick format check
```

Key checks:
- Type is `EXEC` (not `DYN`)
- No `INTERP` segment (no dynamic linker)
- At least one `LOAD` segment
- Machine matches target architecture

## User Stack Layout

When a process is created, the kernel builds a System V ABI initial stack frame. From low to high addresses (starting at `initial_sp`):

```
initial_sp ->  argc           (u64)
               argv[0]        (pointer to string)
               argv[1]        (pointer to string)
               ...
               NULL           (u64 zero, terminates argv)
               envp[0]        (pointer to string)
               envp[1]        (pointer to string)
               ...
               NULL           (u64 zero, terminates envp)
               auxv[0].type   (u64, e.g., AT_ENTRY = 9)
               auxv[0].value  (u64, entry point address)
               AT_NULL        (u64 zero)
               0              (u64 zero)
               16 random bytes (for AT_RANDOM)
               argv string pool (NUL-terminated strings)
               envp string pool (NUL-terminated strings)
               padding to 16-byte alignment
```

Stack size is computed by `compute_stack_size(image_size)`:
- Floor: 8 MB (DEFAULT_USER_STACK_SIZE)
- Scaling: `image_size / 8`
- Cap: 128 MB (MAX_USER_STACK_SIZE)

## Related Files

| File | Description |
|------|-------------|
| `src/os/kernel/loader/elf_loader.spl` | ELF header parsing and PT_LOAD extraction |
| `src/os/kernel/loader/smf.spl` | SMF sheath format parser |
| `src/os/kernel/loader/segment_mapper.spl` | PT_LOAD to page-table mapping |
| `src/os/kernel/loader/process_image.spl` | ELF-to-UserProcessImage builder |
| `src/os/kernel/loader/stack_builder.spl` | SysV initial stack frame construction |
| `src/os/kernel/loader/executable_source.spl` | Path resolution and byte loading |
| `src/os/kernel/types/task_types.spl` | `UserProcessImage`, `UserLoadSegment` structs |
