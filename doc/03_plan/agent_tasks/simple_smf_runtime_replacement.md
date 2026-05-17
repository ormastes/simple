<!-- codex-architecture -->
# Agent Plan: Shared SMF Runtime Replacement

> Status: PARTIAL — "Completed Slice" done (trailer headers, moduleloader_replace_live, kernel SMF parser); Phases 1-5 remaining

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

## Ownership Assumptions

- SimpleOS kernel owns the SMF loader for in-OS app dispatch.
- Hosted runtime owns the SMF module lifecycle for development and JIT use.
- The shared header contract (Phase 1) is the boundary — both sides implement
  the same trailer/offset-0 detection rules independently.

## Recommendation

Treat SMF as the shared packaging format for all runtime contexts. Do not split
into OS-specific and hosted-specific format variants. A single format with
role/namespace metadata is sufficient to distinguish app, library, driver, and
service packages.

## Phase 6: Integration Order

1. SMF reader harmony (shared header contract).
2. Executable SMF wrapper around existing ELF app payloads.
3. Namespace metadata and library search path contract.
4. Dynamic SMF library loader with PIC-only support.
5. WM IPC service boundary.
6. Remove resident fallback once syscall/process launch is stable.

## Risks

- ELF-in-SMF double-parsing overhead: acceptable for app launch; JIT path
  should produce native SMF directly to avoid wrapping.
- PIC enforcement for dynamic libraries may require linker script changes in
  the Simple toolchain.

## Open Dependency Hooks

- Syscall 13 gate must be lifted before Phase 4 (SimpleOS Executable SMF) can
  be exercised end-to-end.
- Per-process link namespace (Phase 5) depends on stable user address space
  isolation from the process-backed apps plan.
