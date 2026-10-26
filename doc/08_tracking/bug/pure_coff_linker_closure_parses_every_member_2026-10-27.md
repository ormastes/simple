# Pure-Simple COFF linker: archive closure parses every library member per call

- **Status:** fixed (lazy index-driven closure + linear symbol lookups), 2026-10-27
- **Component:** `src/compiler/70.backend/linker/coff/archive_closure.spl`
  (`coff_archive_closure_retained_aliases`, `coff_archive_members`,
  `coff_archive_imports`)
- **Found:** 2026-10-27, Windows x86_64, internal COFF link of the stage2
  hello-world objects (43 objects + kernel32/user32/ws2_32/mswsock/bcrypt/
  advapi32/userenv/ntdll/msvcrt/d3d11/dxgi + default libs oldnames/uuid/
  vcruntime/ucrt)

## Measurement

Native-built probe, peak private bytes (PowerShell `PrivateMemorySize64`):

| stop point | peak |
|---|---|
| after 1 `coff_link_default_libraries` call | 1.7 GB |
| after 2 calls | 3.6 GB |
| 3 default-library rounds + final link | > 7.5 GB (killed at the 8 GB lane cap) |

lld-link on the same inputs: whole `native-build` peaks at 198 MB.

## Cause

Every closure call runs `ar_parse` on every library, copies every member's
bytes (`ar_member_data`), and fully parses every COFF member and every short
import, although a hello world selects a few hundred of several thousand
members. The prepare loop and the driver's default-library loop call the
closure repeatedly, and the module is `@no_gc`, so nothing is released.

## Direction

Drive selection from the archive symbol index (the first `/` linker member,
`ar_parse_symbol_index`) the way lld-link does: look up each undefined name,
parse only the member that defines it, and keep parsed members for the
duration of one link.

## Resolution (2026-10-27)

Two causes, both fixed with specs:

1. Every library member was materialized and parsed per closure call. Each
   closure call now reads every archive's linker-member index and parses only
   the members that define a still-undefined name (`coff_lazy_archive_spec.spl`).
   The view is rebuilt per closure call (not cached across the prepare and
   default-library rounds).
2. The dominant cost was not parsing at all: per-symbol linear scans that
   copy symbol/relocation records under `@no_gc` -
   `coff_symbol_at_table_index` per relocation, `coff_weak_primary_for_fallback`
   per undefined symbol, and `coff_symbol_is_relocated` for *every* undefined
   symbol during validation. Now a binary search, a one-pass weak-primary map,
   and a relocation scan only for weak fallbacks.

After the fix, hosted hello world (43 objects, 15 libraries, 3 default-library
rounds + final link) on the native-built probe:

| | wall | peak private |
|---|---|---|
| one closure call | 4 s | 0.24 GB (was 1.7 GB) |
| full link | 77 s | 4.1 GB (was > 7.5 GB, killed) |
| lld-link, same inputs | < 1 s | ~34 MB |

Still about 100x slower and 100x larger than lld-link; the remaining cost is
in section layout/relocation application and is not profiled yet.
