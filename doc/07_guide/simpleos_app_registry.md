# SimpleOS App Registry & ELF Loading Guide

How the app registry resolves, loads, and maps executables from filesystem to process address space.

**Source files:**
- `src/os/kernel/loader/app_registry.spl` — manifest-driven registry
- `src/os/kernel/loader/elf64.spl` — ELF64 parser + segment loader
- `src/os/kernel/loader/executable_source.spl` — alias resolution layer
- `src/os/services/vfs/vfs_init.spl` — VFS integration + byte caching
- `src/os/kernel/memory/vmm.spl` — page table mapping + COW

---

## 1. App Registry

All app path resolution flows through `AppEntry` records in a central registry, replacing the former 6 hardcoded match tables.

### Data Model

```
struct AppEntry:
    canonical_path: text    # "/sys/apps/clang"
    fat32_leaf: text        # "CLANGSMF.SMF"
    boot_seed: bool         # eagerly cache at boot?
```

### Loading the Registry

At boot, VFS init attempts to read `/SYS/APPS/APPIDX.TXT` from the FAT32 volume. If found, `app_registry_load()` parses it. If not, `app_registry_load_hardcoded_fallback()` populates the 18 standard entries.

**Manifest format** (`APPIDX.TXT`):
```
# app registry manifest
/sys/apps/clang|CLANGSMF.SMF|true
/sys/apps/rust|RUSTSMF.SMF|true
/sys/apps/hello_world|HELLOSMF.SMF|false
```

Each line: `canonical_path|fat32_leaf|boot_seed` (lines starting with `#` are comments).

### Public API

| Function | Purpose |
|----------|---------|
| `app_registry_load(manifest_text)` | Parse `\|`-delimited manifest |
| `app_registry_register(path, leaf, seed)` | Add single entry dynamically |
| `app_registry_entries() -> [AppEntry]` | All registered entries |
| `app_registry_lookup(path) -> AppEntry?` | Find by canonical path |
| `app_registry_lookup_by_fat32(leaf) -> AppEntry?` | Reverse lookup by FAT32 name |
| `app_registry_fat32_alias(path) -> text?` | Returns `/SYS/APPS/<leaf>` |
| `app_registry_root_alias(path) -> text?` | Returns `/<leaf>` |
| `app_registry_canonical_from_bytes(bytes) -> text?` | Canonicalize path bytes |
| `app_registry_cache_bytes(path, bytes)` | Store executable bytes |
| `app_registry_cached_bytes(path) -> [u8]` | Retrieve cached bytes |
| `app_registry_boot_seed_entries() -> [AppEntry]` | Entries with `boot_seed=true` |
| `app_registry_is_loaded() -> bool` | Whether registry has been initialized |
| `app_registry_clear()` | Reset (for tests) |

---

## 2. Adding a New App

1. **Add a manifest line** to `APPIDX.TXT` on the FAT32 disk image:
   ```
   /sys/apps/my_tool|MYTOOLSF.SMF|false
   ```
   The FAT32 leaf must be a valid 8.3 uppercase name.

2. **Place the binary** at `/SYS/APPS/MYTOOLSF.SMF` on the FAT32 volume.

3. **No code changes needed.** The registry, VFS, and ELF loader handle the rest automatically.

For boot-critical apps (set `boot_seed=true`), the VFS init loop eagerly reads and caches the bytes at startup.

---

## 3. FAT32 Name Resolution

The central problem: canonical paths (`/sys/apps/clang`) don't match FAT32 8.3 names (`CLANGSMF.SMF`). The registry provides the mapping.

**Resolution chain** (in `g_vfs_read_executable_bytes`):

1. Check registry byte cache
2. Try VFS mounted path directly
3. Try FAT32 alias from registry (`app_registry_fat32_alias`)
4. Try root alias from registry (`app_registry_root_alias`)
5. Try direct C FAT32 read (for unregistered files under `/sys/apps/`)

Paths ending in `.smf` are stripped before lookup (e.g., `/sys/apps/clang.smf` resolves to `/sys/apps/clang`).

---

## 4. ELF Loading Pipeline

Once bytes are resolved, `loader_dispatch` sniffs the magic and routes to `elf64_load`:

```
loader_exec(path, argv, envp, space)
  -> rt_file_read_bytes(path)
  -> loader_dispatch(bytes, space)
       -> elf64_load(bytes, space)        # ELF64
       -> smf_load(bytes, space)          # SMF format
```

### elf64_load

For each `PT_LOAD` segment:

1. **Reserve VMA** via `vmm_mmap(space, p_vaddr, p_memsz, perms, ...)`
2. **Populate pages** via `vmm_copy_to_user(space, p_vaddr, bytes, p_offset, p_filesz, p_memsz, flags)`

`vmm_copy_to_user` processes one 4KB page at a time:
- Allocates a physical frame from PMM
- Zeros the page via HHDM + `mmio_write64`
- Copies overlapping file bytes via `mmio_write8`
- Maps the page into the address space with appropriate flags (W^X enforced)

BSS (the gap between `p_filesz` and `p_memsz`) is implicitly zeroed since each page starts zeroed.

---

## 5. COW Fork & Page Ref-Counting

When `vmm_cow_clone` forks an address space:

1. **Clone VMAs** — copies the VMA list, adding `VMM_VMA_COW` flag to writable entries in both parent and child
2. **Clear writable** — `_cow_clear_writable_recursive` walks the parent PML4 and clears `PTE_WRITABLE` on all user-half leaf PTEs
3. **Ref-count frames** — `_cow_ref_leaf_pages` walks the parent PML4 and calls `pmm_ref_page` on every mapped physical frame (handles 2MB huge pages at PD level)

Both walks are recursive 4-level traversals (PML4 -> PDPT -> PD -> PT), limited to the user half (indices 0..255 at PML4 level).

On COW fault, `vmm_handle_cow_fault`:
- Allocates a fresh page
- Copies the old page contents via HHDM
- Maps the new page as RW
- Calls `pmm_unref_page` on the old frame (frees it if refcount reaches 0)

---

## 6. Test Coverage

| Spec File | Tests | Covers |
|-----------|-------|--------|
| `test/os/kernel/loader/app_registry_spec.spl` | 22 | Registry parse, lookup, alias, cache, fallback |
| `test/os/kernel/loader/app_discovery_spec.spl` | 16 | Dynamic resolution, FAT32 fallback, canonicalization |
| `test/os/port/x86_64_elf_load_spec.spl` | 1 | ELF load contract |
