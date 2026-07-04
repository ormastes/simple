<!-- codex-architecture -->
# Agent Plan: Shared SMF Runtime Replacement

> Status: DATA MODELS LANDED — all five phases have `.spl` scaffolding; orchestration
> wiring and specs are the remaining gap. See per-phase audit below (W13 audit 2026-05-19).

## Goal

Make SMF the shared runtime envelope across hosted loader, interpreter, local JIT, remote JIT, baremetal, and SimpleOS, while preserving ELF as the initial process image mapper.

## Completed Slice

- Compiler memory reader recognizes v1.1 trailer headers and legacy offset-0 headers.
- Compiler memory reader normalizes payload offsets through `smf_data_offset`.
- Hosted module loader has `moduleloader_replace_live` for staged generation replacement and hot-reload routing.
- SimpleOS kernel SMF parser recognizes trailer headers.
- SimpleOS loader dispatch accepts SMF trailer packages.
- Focused specs cover compiler reader, kernel SMF parser, and kernel loader dispatch.

## W13 Audit: Per-Phase Implementation Status

### Phase 1: Shared Header Contract — DATA MODEL LANDED, SPECS MISSING

File: `src/os/smf/smf_header_contract.spl` (192 lines)

Landed: `SmfHeader`, `TrailerDetection`, `HeaderFallback`, `SmfTestVector` structs;
`smf_header_offset`, `smf_has_header`, `smf_parse_header` functions.

**Gap:** No external callers — `smf_header_contract.spl` is self-contained with zero
imports from other modules. Test vectors (`SmfTestVector`) exist as a type but no spec
file exercises them. Next: add `src/os/smf/smf_header_contract_spec.spl` covering
pure-SMF, stubbed-SMF, embedded-ELF, and malformed-trailer vectors.

### Phase 2: Hosted Atomic Replacement — DATA MODEL LANDED, ORCHESTRATION MISSING

File: `src/os/smf/smf_generation.spl` (129 lines)

Landed: `GenerationState` (loaded/candidate/active/retiring/failed states + promote/retire),
`CandidateMapping` (relocation + import validation flags), `LifecycleManager` class.

**Gap:** Zero external callers. The module loader (`src/compiler/99.loader/loader/module_loader.spl`)
still uses `moduleloader_replace_live` directly without routing through `GenerationState`.
Next: wire `module_loader.spl` to import and use `GenerationState`/`LifecycleManager`; add spec.

### Phase 3: Interpreter and JIT Integration — PARTIALLY WIRED

File: `src/os/smf/smf_jit_bridge.spl` (89 lines)

Landed: `SmfSource` (file/jit/remote), `ExportMetadata`, `ImportMetadata`, `JitManifest`.

**Status:** `SmfSource`, `ExportMetadata`, `ImportMetadata` are referenced from:
- `src/compiler/70.backend/linker/__init__.spl`
- `src/compiler/70.backend/linker/object_provider.spl`
- `src/compiler/70.backend/linker/smf_getter.spl`
- `src/compiler/99.loader/loader/module_loader_lib_support.spl`

**Gap:** `JitManifest` has no callers. Remote JIT upload-manifest path not yet connected.
Interpreter `module_loader.spl` does not route through `SmfSource` abstraction yet.
Next: wire interpreter module loading to use `SmfSource.from_file`; connect remote JIT path.

### Phase 4: SimpleOS Executable SMF — WIRED AND ACTIVE

File: `src/os/kernel/loader/smf.spl` (252 lines)

Landed: `smf_extract_executable_stub`, `smf_extract_executable_stub_for_arch`,
`smf_executable_entry_point_for_arch`, `smf_extract_executable_stub_unchecked`,
`smf_load` (delegates to `elf64_load`); arch validation; role/ABI checks.

**Status:** Actively used in:
- `src/os/kernel/loader/loader_api.spl`
- `src/os/kernel/loader/process_image.spl`
- `src/os/kernel/loader/dylib_registry.spl`
- `src/os/kernel/loader/x86_64_fs_exec_spawn.spl`

**Gap:** Blocked end-to-end by Syscall 13 gate (see Open Dependency Hooks). Native SMF
code-section mapping returns -ENOSYS — intentional deferral documented in the code.
Window hints and dependency metadata fields not yet in the trailer spec.

### Phase 5: Dynamic Libraries — API STUBS LANDED (W13)

File: `src/os/smf/smf_dynlib.spl`

Landed (pre-W13): `LibraryRole` (runtime/plugin, PIC flag), `LinkNamespace` (global/per-process),
`DynLoadRequest` (lazy/eager), `DynLoadResult`.

Landed (W13): `DynSymResult`, `DynCloseResult`, `smf_dlopen`, `smf_dlsym`, `smf_dlclose`
API functions over the existing data model.

**Gap:** `LinkNamespace` is not consumed by any loader. `smf_dlopen` validates inputs but
does not perform actual mapping — deferred pending stable user address space isolation.
Blocked by Per-process link namespace dependency (see Open Dependency Hooks).
Next: wire `dylib_registry.spl` to use `LinkNamespace`; implement actual mmap-backed load.

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
