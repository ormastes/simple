<!-- codex-architecture -->
# Agent Plan: Shared SMF Runtime Replacement

## Goal

Make SMF the shared runtime envelope across hosted loader, interpreter, local JIT, remote JIT, baremetal, and SimpleOS, while preserving ELF as the initial process image mapper.

## Completed Slice

- Compiler memory reader recognizes v1.1 trailer headers and legacy offset-0 headers.
- Compiler memory reader normalizes payload offsets through `smf_data_offset`.
- Hosted module loader has `moduleloader_replace_live` for staged generation replacement and hot-reload routing.
- SimpleOS kernel SMF parser recognizes trailer headers.
- SimpleOS loader dispatch accepts SMF trailer packages.
- Focused specs cover compiler reader, kernel SMF parser, and kernel loader dispatch.

## Phase 1: Shared Header Contract

- Extract common header-location rules into a reusable module.
- Keep the rule identical everywhere: trailer first, offset-0 fallback.
- Add test vectors for pure SMF, stubbed SMF, embedded-ELF SMF, and malformed trailers.

## Phase 2: Hosted Atomic Replacement

- Add generation states: `loaded`, `candidate`, `active`, `retiring`, `failed`.
- Stage candidate mappings before global symbol table changes.
- Swap exports only after relocation and import validation pass.
- Teach lifecycle manager to free retired mappings after references drain.

## Phase 3: Interpreter and JIT Integration

- Route interpreter compiled-module loading through the same SMF source abstraction.
- Have local JIT produce replacement candidates with the same export/import metadata.
- Make remote JIT consume SMF as an upload manifest instead of raw bytes.

## Phase 4: SimpleOS Executable SMF

- Add executable SMF package metadata for app role, namespace, dependencies, and window hints.
- Extract embedded ELF executable bytes from SMF.
- Pass extracted ELF to existing SimpleOS ELF process-image loader.
- Keep drivers baremetal-only and apps host-OS-like.

## Phase 5: Dynamic Libraries

- Define library role metadata separate from `PIC`.
- Implement per-process link namespace.
- Add `dlopen`/`dlsym`/`dlclose` equivalent API over SMF library packages.

## Non-Goals For This Slice

- Full kernel SMF section mapping.
- Replacing ELF with SMF as direct process image.
- Atomic replacement in the SimpleOS kernel.
- Remote debug transport implementation.
