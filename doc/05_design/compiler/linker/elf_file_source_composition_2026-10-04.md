# Operational ELF file-source binding

Base: `d945e61704c`; date: 2026-10-04. Owner: linker_research.
Worktree: `C:/dev/simple-item4-byte-source-docs-20261004`; branch:
`work/item4-byte-source-docs-20261004`; integration target: release/1.0.
Status: approved interface, test-first implementation pending; runtime UNRUN.

## Actual input boundaries

`native_freestanding.spl:25` reads object/archive paths in
`freestanding_inputs`; its file adapter subsequently calls the resident ELF or
Mach-O engine and `native_image_publish`. Hosted ELF is assembled in
`_LinkerWrapper/native_linking.spl:1428` (`internal_link_native`): it reads
CRT objects, explicit objects, runtime/system archives, and shared libraries,
then calls `elf_link_configured`, applies FreeBSD branding when appropriate,
and publishes the complete executable.

The hosted library resolver also reads candidate files in
`internal_elf_library_kind` before the selected file is read again for linking.
Merely changing the final object reader leaves this I/O bypass and a split
between classification and consumption. The selected path, returned bytes and
classified kind must stay together through resolution and linking.

## Frozen compatible API

Extend `ElfOperationProviderV1` with optional
`read_bytes: Option<fn(text) -> Result<[u8], text>> = nil`.
Add `ELF_OPERATION_READ_BYTES = 4`; its facet ID has existing facet hi and lo 4,
and its built-in capsule has existing capsule hi and lo 5.

Preserve the current three-operation contracts unchanged:

- `elf_builtin_operation_providers_v1()`
- `elf_builtin_operations_v1()`
- `elf_seal_operations_v1(providers, policy)`

Add file-aware constructors:

- `elf_builtin_file_operation_providers_v1()`
- `elf_builtin_file_operations_v1()`
- `elf_seal_file_operations_v1(providers, policy)`

Use one private constructor with a `requires_source` choice. The file engine
descriptor requires all four facets; the array engine requires the original
three. The owner retains an optional reader and exposes
`read_bytes(path) -> Result<[u8], text>`; absence rejects before any I/O.
Descriptor/callback correspondence and actual receipt-slot dispatch retain the
existing constructor rules. The file constructor's source callback must never
be replaced by an unsealed side callback after construction.

The pure array API neither needs nor claims to invoke a byte source. File
adapters select the four-facet constructor and use the **same owner** for input
acquisition, relocation, layout and image writing. Receipts describe bindings;
they are not a log asserting that every bound operation executed.

Add `link_freestanding_with_operations_v1(objects, archives, output, config,
operations)` alongside the existing default entrypoint. Add hosted
`internal_link_native_with_operations(os, arch, config, object_files, output,
operations)` alongside its existing entrypoint. Preserve existing return types.
Default file entrypoints construct the built-in file owner. ELF dispatch uses
`elf_link_with_operations` and consumes its image. Mach-O behavior must remain
compatible without claiming its operations use the ELF facets.

## Read ownership and compatibility

The portable built-in source uses `std.io_runtime.file_read_bytes_result`,
propagates named read failures, and preserves existing path/empty-input policy.
Its returned resident array is the acquired input used by the parser. Hosted
selection retains a record containing selected path, bytes and kind; classify
the callback's bytes and reuse them, rather than reopening the selected path.
Search ordering and skipping unsupported linker-script candidates stay intact.

Keep target/host admission, CRT order, library paths, runtime bundle, shared
names, PIE/interpreter, runpath, bind-now, hash style, as-needed, section GC,
retained symbols, strip and FreeBSD branding intact. Avoid changing SimpleOS or
external linker callers merely because they share a helper. New source-aware
helpers should be scoped or their compatibility callers explicitly migrated.

Preserve freestanding lexical output/input alias checks before reading, output
size checks before publication, and the existing transactional publisher.
Source, parse or relocation failure must not publish partial bytes or remove
an existing output. The caller still owns the output directory.

## Identity limits

The portable default has no retained handle or immutable filesystem authority.
A path identifies the requested input, not an authenticated artifact. Reusing
the same acquired bytes prevents classification/re-read disagreement for that
selection; it does not detect concurrent mutation during a read or authenticate
all inputs as one filesystem snapshot. No self-reported digest closes this gap.

The existing retained-file owner supports Linux/Windows and rejects final
symlinks. Making it universal here would regress FreeBSD/macOS and normal
hosted shared-library symlinks. A future verified retained source needs an
explicit host and symlink contract; do not silently substitute it or claim its
guarantees for ordinary path reads.

All inputs/images remain resident. Four-facet sealing certifies neither memory
limits nor RSS, GC absence, trust, signatures, sandboxing or native execution.
Zero declared reservations retain the prior meaning: no reserved accounting,
not zero real allocation. UnsupportedBudget remains honest.

## Acceptance matrix

| Case | Concrete oracle |
| --- | --- |
| Default parity | Existing file entrypoint and explicit default file owner produce equal fixture images and engine identity |
| Selected reader | A callback reads a real alternate definition file; its different symbol/data value appears in the actual output |
| One owner | The selected reader and a selected ELF operation both affect the same resulting link |
| Required source | File sealing rejects missing/mismatched/duplicate source; array owner read rejects without invoking I/O |
| Classification | Hosted selection classifies and consumes the same callback bytes, including archive/shared selection and search ordering |
| Read failure | Named source errors or malformed input return failure while a destination sentinel remains intact |
| Existing policy | Lexical aliases reject before reads; output limit, executable publication and configured link options retain their behavior |
| Compatibility | Array three-facet tests remain valid; ordinary filesystem symlinks and supported hosted platforms are not rejected solely by the new binding |

Use real fixture bytes, checked setup, canonical `std.spec.step`, and independent
output decoding. A diagnostic injected by a callback tests error propagation,
not detected identity mutation or native handle cleanup. Native-host-dependent
acceptance must state its prerequisites and remain UNRUN until admission.

Runtime owns binding-module extension and hosted integration; root owns the
freestanding adapter and common ledger; acceptance owns tests/manuals; research
owns this design and independent source review. Separate worktrees share the
base above. Sidecars: N/A. No runtime rebuild or diagnostic retry is authorized.
