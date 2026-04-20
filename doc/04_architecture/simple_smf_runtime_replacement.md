<!-- codex-architecture -->
# Shared SMF Runtime Replacement Architecture

## Status

Proposed, with first implementation slice completed for trailer-header detection in the compiler memory reader and SimpleOS kernel loader.

## Problem

Simple currently has several execution surfaces that need compiled code:

- Hosted module loader and dynamic SMF loading.
- Interpreter and local JIT.
- Remote JIT upload/execution.
- Baremetal and SimpleOS app/process loading.

These surfaces must not invent separate binary contracts. They need one SMF package model, one header-location rule, and one replacement model.

## Decision

SMF is the Simple runtime envelope for executable modules, libraries, app metadata, and replacement metadata. ELF remains the first-class machine process image for SimpleOS until the kernel has a full SMF section mapper.

## Layering

### Common Format Layer

Owned by `src/compiler/70.backend/linker/` today:

- `smf_header.spl`: canonical 128-byte v1.1 header.
- `smf_reader_memory.spl`: in-memory parser used by loaders and tests.
- `lib_smf*.spl`: archive/index format for grouped modules.

Target state: move pure header-location and little-endian parse helpers into a shared common module once both compiler and kernel can import it without layer cycles.

### Hosted Loader Layer

Owned by `src/compiler/99.loader/loader/`:

- Maps exported SMF symbols into executable memory.
- Applies relocations.
- Tracks resource ownership and generations.
- Owns hot replacement for hosted/interpreter/JIT processes.

Replacement target:

1. Parse candidate SMF.
2. Validate target ABI, imports, exports, and relocation table.
3. Map candidate into a new generation.
4. Atomically update exported symbol records.
5. Retire old generation after references drain.

### Interpreter and JIT Layer

Owned by `src/compiler/95.interp/`, `src/compiler/70.backend/backend/jit_interpreter.spl`, and `src/compiler/99.loader/loader/jit_*`.

Interpreter and JIT should consume SMF metadata through the hosted loader contract:

- Interpreter can prefer source, SMF, or library SMF through load-session policy.
- Local JIT emits or consumes SMF sections for generated code and relocation metadata.
- Remote JIT uses SMF as an upload manifest with target ABI notes.

### SimpleOS Kernel Layer

Owned by `src/os/kernel/loader/`.

The kernel loader must remain minimal:

- Sniff ELF first.
- Sniff SMF by `EOF-128` trailer, then offset-0 fallback.
- Parse only enough SMF metadata to validate package role and extract/dispatch the process image.
- Do not perform hosted dynamic replacement in kernel space unless the process manager owns the generation boundary.

### App/Driver Boundary

Apps should behave as if running on a normal host OS:

- Load from filesystem paths.
- Run as separate processes.
- Use syscalls, file descriptors, namespaces, and IPC/window services.

Drivers should remain baremetal-aware:

- Use device memory, MMIO, IRQs, DMA, and bus capabilities.
- Expose services to apps through kernel/service capabilities, not direct app access.

## SMF Roles

### Executable SMF

- `flags.EXECUTABLE = true`.
- Contains an embedded ELF executable or process-image section initially.
- Carries app metadata, namespace requirements, window hints, and dependency notes.
- SimpleOS validates and passes embedded ELF to the ELF mapper.

### Library SMF

- `flags.PIC = true`.
- Contains exports, imports, relocations, init/fini metadata, and ABI notes.
- Loaded into a per-process link namespace.

### Remote JIT SMF

- Contains uploaded code bytes, relocation patch list, exported entry names, target ABI, and debug-transport requirements.
- The remote transport is not the loader; it only writes validated bytes and installs control breakpoints/trampolines.

## Runtime Replacement Model

Replacement is generation-based, not destructive unload/load:

1. `loaded:N` remains callable.
2. `candidate:N+1` is parsed, verified, relocated, and mapped.
3. A symbol table transaction swaps exports to `N+1`.
4. Old generation enters `retiring`.
5. Lifecycle manager frees old mappings when no live call frames or pinned handles remain.

Failure rule: if candidate validation or relocation fails, `loaded:N` remains active.

## Invariants

- Header detection is trailer first, offset-0 fallback.
- Offsets inside a stubbed SMF are interpreted relative to `smf_data_offset`.
- ELF mapping is not duplicated in SMF loader code.
- Hosted runtime replacement never leaves global symbols absent between generations.
- SimpleOS apps never access driver-only baremetal resources directly.

## First Implementation Slice

- `src/compiler/70.backend/linker/smf_reader_memory.spl` now parses v1.1 trailer headers and legacy offset-0 headers.
- `src/os/kernel/loader/smf.spl` now parses trailer headers, exposes `smf_has_header`, and reads v1.1 entry/stub metadata from the correct offsets.
- `src/os/kernel/loader/loader_api.spl` now dispatches SMF trailer packages to the SMF loader instead of rejecting them as unknown data.

## Remaining Work

- Add shared common SMF parse helpers to remove compiler/kernel duplication.
- Add hosted atomic replacement API to `ModuleLoader`.
- Add library-role metadata beyond `PIC` so PIE executables and shared libraries are not confused.
- Implement SimpleOS executable-SMF extraction to ELF process image.
- Define remote-JIT SMF note sections for target ABI, upload address, and debug-control policy.
