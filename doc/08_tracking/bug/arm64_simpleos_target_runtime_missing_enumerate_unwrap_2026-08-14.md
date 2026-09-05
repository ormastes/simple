# ARM64 SimpleOS target runtime misses enumerate and trapping unwrap owners

Status: FIXED IN SOURCE / FOCUSED ARCHIVE CONTRACT PASS —
`/root/arm_runtime_symbols` (2026-08-14)

## Evidence

The retained current-source payload objects in
`.simple/native-objects-jWARot` contain one undefined reference each to
`rt_array_enumerate` and `rt_unwrap_or_trap`, and define neither symbol.
The ARM64 simple-core archive exports `rt_array_enumerate`, but does not export
`rt_unwrap_or_trap`; therefore the target runtime contract is incomplete and
the final link cannot resolve the complete payload without a stub.

## Root-cause hypothesis

The pure-Simple array-query owner already implements and exports enumerate.
The target runtime's enum/value owner exposes non-trapping unwrap helpers but
has no target implementation of the dedicated `.unwrap()` trap contract.
The focused link contract must also prove that archive extraction resolves the
retained object's enumerate reference rather than merely observing the symbol
with an archive-wide `nm` listing.

## Acceptance

- The ARM64 target runtime owns a real `rt_unwrap_or_trap` implementation with
  Ok/Some payload semantics and fail-closed Err/None behavior.
- The target archive exports both requested symbols with their exact linker
  names.
- A focused AArch64 relocatable link over the retained payload objects and the
  target archive leaves neither requested symbol undefined.
- No generated fallback stub supplies either symbol, and the retained payload
  objects are not rebuilt.

## Resolution

`core_values.spl` now owns `rt_unwrap_or_trap`. It returns raw non-enums and
arbitrary user enums unchanged, unwraps Option Some and Result Ok payloads,
and calls the target `abort` owner for Option None and Result Err. It accepts
both the ordinal Option discriminants constructed inside simple-core and the
stable variant hashes emitted by native lowering.

The focused combined archive initially exposed a second part-level defect:
extracting both the existing enumerate member and its array dependencies
produced duplicate no-mangle helper names shared by `core_array_query` and
`core_array_ops`. The array-query-local helpers now carry an owner-qualified
prefix, so both requested members can be extracted into one link.

## Verification (2026-08-14)

- Rebuilt only `core_values.spl` and `core_array_query.spl` as AArch64
  `--emit-archive --no-mangle` parts with the retained stage-2 compiler and
  `SIMPLE_NO_STUB_FALLBACK=1`: PASS (one source compiled per part).
- Constructed focused candidate archive from unchanged existing part objects
  plus those two rebuilt parts:
  `build/native_probe/arm64-runtime-symbols/candidate.DIFd7q/libsimple_runtime.a`.
- `scripts/check/check-arm64-target-runtime-symbols.shs` verified exact archive
  exports, absence from `_stubs_freestanding.c`, and an AArch64 relocatable
  link of retained `mod_27.o` + `mod_47.o`: PASS; neither requested symbol
  remains undefined.
- The retained payload objects were not rebuilt and no full payload build was
  run.
