# Wine DLL Loading Guide

## Overview

The Wine PE/DLL loader implements PE image loading for SimpleOS's Wine compatibility layer. It handles PE section mapping, base relocation, IAT (Import Address Table) patching, and DllMain lifecycle management.

## Architecture

### PE Export Lookup

`pe_export_lookup_by_name(data, name)` walks the PE export directory's name table, matches the requested name, uses the ordinal table to index into the address table, and returns the function's RVA. Returns `-1` if the name is not found.

### Full Block-Iteration Relocation

`wine_pe_apply_all_relocations(data, preferred_base, load_base)` iterates all `IMAGE_BASE_RELOCATION` blocks in the PE relocation directory:

- Each block starts with `VirtualAddress` (u32) and `SizeOfBlock` (u32)
- Entries are 2-byte pairs: `(type << 12) | offset`
- Type 0 (`IMAGE_REL_BASED_ABSOLUTE`): padding, skipped
- Type 3 (`IMAGE_REL_BASED_HIGHLOW`): 32-bit relocation
- Type 10 (`IMAGE_REL_BASED_DIR64`): 64-bit relocation
- Delta = `load_base - preferred_base`

`wine_pe_apply_all_relocations_to_image(data, preferred_base, load_base)` returns the patched byte array with all relocations applied.

### PE Image Mapping

`wine_dll_map_pe_image(data, load_base)` performs actual PE section mapping:

1. Parses the PE header (sections, image base, size)
2. Allocates a flat image buffer of `SizeOfImage` bytes
3. Copies PE headers to the start of the buffer
4. For each section: copies raw data to the correct virtual offset
5. Applies relocations if `load_base != preferred_base`
6. Returns `WineDllMappedImage` with the mapped image, entry point RVA, and metadata

### IAT Patching

`wine_dll_patch_iat_from_mapped_image(image, descriptor_limit, symbol_limit)` patches the Import Address Table:

1. Walks import descriptors via `pe_import_descriptor_thunk_bindings`
2. For each import: resolves the DLL name against known modules (kernel32, user32, gdi32)
3. Looks up each symbol via `wine_kernel32_get_proc_address`
4. Writes the resolved address as a u64 at each IAT thunk offset

### DllMain Invocation

`wine_dll_invoke_dllmain(dll_name, image_base, entrypoint_rva, tls_callback_count, reason, reserved, load_evidence)` records a DllMain invocation without executing native code. Actual invocation requires `rt_dyncall_3` from the dynamic call subsystem.

Supported reasons:
- `1` = `DLL_PROCESS_ATTACH`
- `0` = `DLL_PROCESS_DETACH`

## Key Types

| Type | Module | Purpose |
|------|--------|---------|
| `WinePeRelocationResult` | `wine_pe_loader_runtime` | Relocation plan result with delta, count, target RVA |
| `WineDllMappedImage` | `wine_dll_image_loader` | Mapped PE image with sections copied and relocations applied |
| `WineDllIatPatchResult` | `wine_dll_view_import_binding` | IAT patching result with patched count and module count |
| `WineDllMainInvocationRecord` | `wine_dll_entrypoint_lifecycle` | DllMain invocation record (deferred, not executed) |

## Testing

```bash
bin/simple test test/lib/common/wine_pe_loader_spec.spl
```

The spec builds minimal PE64 fixtures programmatically and tests:
- DIR64 relocation with full block iteration
- ABSOLUTE entry skipping
- Zero-delta optimization
- PE export name lookup
- Image mapping with correct size
- DllMain invocation recording
