# Release linker specs: stale TLS entry + stale "libraries rejected" case

- status: fixed (2026-11-22)
- found: 2026-11-18 (lane ssos), on untouched release/1.0.0 with Windows bin/simple.exe

## Root cause (both are stale tests, not linker bugs)
1. `elf_boot_link_spec` "writes CODE_4 and CODE_6 GOTTPOFF through one SimpleOS TLS slot"
   linked `code_gottpoff_x64.o` (only global: `_start`) with `TLS_IE_SCRIPT`
   (`ENTRY(read_imported_tls)`), so it failed with `entry symbol not defined`.
   Fix: new `TLS_IE_START_SCRIPT` (same layout, `ENTRY(_start)`).
2. `native_linking_internal_spec` "rejects a config field ... (libraries)" asserted
   `libraries` is unsupported, but the internal engine now consumes libraries
   (sibling cases "consumes the configured library list" and "resolves a versioned
   shared library behind a GNU ld script"). Contradictory case retargeted to `debug=true`, which ELF and COFF both still reject (keeps the rejection path tested on any host).

## Not fixed: host-requirement cases (need owner decision)
Five `native_linking_internal_spec` cases (aarch64 hello, wide-str, libm, SIMPLE_LINKER
unset, single-SMF) document "Host requirement: aarch64 Linux with glibc". On a
Windows/x86_64 host the default target is COFF and the output cannot execute
(exit 127). They are environmental, not linker defects; gating them on
`host_arch()/host_os()` is a skip and needs approval.

## Verification
elf_boot_link_spec 48/48 pass; native_linking_internal_spec only the 5 host cases fail.

## Verification Update (2026-11-22)

- Confirmed `TLS_IE_START_SCRIPT` in `test/01_unit/compiler/backend/linker/elf_boot_link_spec.spl` and `debug = true` rejection test in `test/01_unit/compiler/backend/native_linking_internal_spec.spl` are landed and verified.
