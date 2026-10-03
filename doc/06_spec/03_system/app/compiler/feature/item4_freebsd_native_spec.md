# FreeBSD native loader acceptance

Authority: `test/03_system/app/compiler/feature/item4_freebsd_native_spec.spl`.
Requirements: ITEM4-REQ-002, 006. Status: **UNRUN**; authored manual awaits
canonical generation and actual platform evidence.

Run with a qualified self-hosted runtime on FreeBSD AMD64 or ARM64 and explicit
`SIMPLE_LINKER=internal`. Missing host or startup prerequisites fail the test.

1. Discover the installed FreeBSD executable and PIE startup inputs.
2. Link the real host-matching `main` fixture through the typed production facade
   with compiler-driver fallback disabled and no extra Simple runtime archive.
3. Require `internal:elf`, the requested path, FreeBSD OSABI and ET_EXEC/ET_DYN.
4. Execute each output with a five-second timeout. Require exit 42 and empty
   stdout/stderr, then remove the task-owned image.

Portable byte inspection cannot substitute for this native loader result.
