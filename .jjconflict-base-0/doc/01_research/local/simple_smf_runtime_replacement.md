<!-- codex-research -->
# Local Research: Shared SMF Loader and Runtime Replacement

## Scope

This research covers the shared SMF runtime path across:

- Compiler-side SMF readers and writers.
- Hosted/interpreter module loading.
- JIT and remote-JIT execution.
- Baremetal and SimpleOS executable loading.
- Runtime replacement / hot reload of already loaded SMF modules.

## Existing Code

### SMF format and readers

- `src/compiler/80.driver/smf_writer.spl` writes SMF v1.1 with section data first and the 128-byte header as a trailer at `EOF-128`.
- `src/compiler/70.backend/linker/smf_header.spl` is the canonical v1.1 header definition. It includes `EXECUTABLE`, `PIC`, `HAS_STUB`, `stub_size`, `smf_data_offset`, app hints, and window hints.
- `src/compiler/70.backend/linker/smf_reader_memory.spl` is the common in-memory reader used by module loading and linker helpers. It now prefers the v1.1 trailer header and falls back to legacy offset 0.
- `src/compiler/70.backend/linker/lib_smf.spl`, `lib_smf_reader.spl`, and `smf_getter.spl` define `.lsm` library archives and a unified single-SMF / library-SMF getter.

### Runtime module loading

- `src/compiler/99.loader/loader/module_loader.spl` loads SMF modules, maps exported symbols to executable memory, applies SMF relocations, and supports `moduleloader_reload`.
- `moduleloader_reload` currently unloads then reloads. This is acceptable for development but not atomic for running processes because global symbols disappear during the replacement window.
- `src/compiler/99.loader/loader/resource_lifecycle.spl` tracks mapped executable pages, JIT mappings, and SMF cache lifecycle. This is the right owner for generation-based replacement cleanup.
- `src/compiler/99.loader/loader/object_mapper.spl` already has an `allow_replace_on_reload` policy, which can become the atomic replacement backend.

### Interpreter and JIT

- `doc/04_architecture/jit_interpreter_integration.md` describes shared parser / HIR / MIR / execution infrastructure for interpreter and JIT modes.
- `src/compiler/70.backend/backend/jit_interpreter.spl` and `src/compiler/95.interp/*` are runtime consumers of compiled artifacts but do not yet share a single SMF image contract.
- `src/compiler/99.loader/loader/jit_context.spl` and `jit_instantiator.spl` provide JIT metadata and executable mapping. These should consume the same SMF symbol/import/export/relocation metadata as hosted module loading.
- `doc/01_research/local/remote_jit_execution_research.md` establishes remote JIT feasibility: host compiles code, uploads bytes to target memory via debug transport, and controls execution through debug breakpoints/triggers. SMF can be the signed metadata envelope for those uploaded code bytes.

### SimpleOS and baremetal

- `src/os/kernel/loader/loader_api.spl` dispatches executable bytes to ELF or SMF loaders.
- `src/os/kernel/loader/smf.spl` was a minimal stub. It now recognizes v1.1 trailer headers and legacy offset-0 headers.
- `src/os/kernel/loader/elf64.spl`, `elf_loader.spl`, and `process_image.spl` are still the real process-image path. SMF should initially wrap or reference ELF process images rather than replace ELF mapping logic.
- `examples/simple_os/arch/*/boot/baremetal_stubs.c` provide architecture-specific host/runtime bridges. Drivers stay baremetal; apps should see a host-like OS ABI through syscalls, filesystem paths, and process services.

## Findings

1. SMF should be the shared module/package envelope, not a replacement for ELF process mapping in the first implementation.
2. The compiler, loader, interpreter, remote JIT, and SimpleOS should all agree on one header-location rule: try `EOF-128`, then offset 0.
3. Runtime replacement needs a generation model:
   - Load and validate generation N+1 without disrupting generation N.
   - Patch symbol table / entry table to N+1 only after validation succeeds.
   - Retire N after no stack/frame/thread references remain.
4. Remote JIT should use SMF as a transport manifest:
   - Code section: upload bytes.
   - Reloc section: target-side patch instructions.
   - Exports: callable entry points.
   - Notes: target ABI, memory permissions, breakpoint/trampoline requirements.
5. SimpleOS should use the same metadata but enforce kernel boundaries:
   - Apps load via filesystem and process manager.
   - Drivers can access baremetal resources only through driver capabilities.
   - SMF loader validates package metadata; ELF loader maps the process image.

## Gaps

- File-backed Rust SMF loader status still appears older than the Simple writer and in-memory reader.
- Kernel SMF loader still returns `-ENOSYS`; it parses headers but does not map SMF code sections.
- Hosted `moduleloader_reload` is unload/load, not atomic replacement.
- No common SMF replacement manifest exists yet for loader, interpreter, remote JIT, and SimpleOS.
- Dynamic library loading still lacks a stable per-process link namespace.

## Recommended Next Work

1. Define a shared SMF runtime contract in architecture docs.
2. Keep ELF as the initial process image format and use SMF as package/container.
3. Add generation-aware replacement APIs to the hosted module loader.
4. Add SimpleOS kernel tests that verify trailer-header dispatch.
5. Later, move shared header parsing into a common Simple module consumed by compiler loader and kernel loader.
