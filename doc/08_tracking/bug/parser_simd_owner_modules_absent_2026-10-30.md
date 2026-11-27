# Parser SIMD owner modules absent: parser_byte_avx2_lowering and parser_simd_execution_capability_v1

Status: open. The specs are marked `@tag:in-development` until the owners exist.
Found by: the Lunar loader sweep, 2026-10-30.
Related: `doc/08_tracking/bug/resume2_missing_interface_owners_2026-10-03.md`
(section "Separate SIMD capability dependency", which already specifies the
required `parser_simd_execution_capability_v1` API).

## Symptom

| Spec | Error | Before (seed, one file at a time) |
|---|---|---|
| `test/01_unit/compiler/loader/parser_structural_guarded_call_v1_spec.spl` | unresolved `compiler.driver.parser_simd_execution_capability_v1` | 0/1 |
| `test/01_unit/compiler/loader/parser_structural_mask_mapping_authorization_v1_spec.spl` | unresolved `compiler.backend.native.parser_byte_avx2_lowering` | 0/1 |
| `test/01_unit/compiler/loader/parser_structural_package_owner_v1_spec.spl` | `function parser_structural_mask_scalar_v1 not found` | 1/4 |
| `test/01_unit/compiler/loader/parser_structural_mask_batch_v2_spec.spl` | `function parser_structural_mask_scalar_v1 not found` | 0/6 |

The resolver reports "module path segment `compiler` not found", which names
only the first segment. Each spec fails the same way when run alone, so the
cause is not the search roots.

## Root cause

The owners were never committed. `git log --all` has no history for
`src/compiler/**/parser_byte_avx2_lowering.spl` or
`parser_simd_execution_capability_v1.spl`, `git log --all -S'fn parser_structural_mask_scalar_v1'`
finds no definition, and neither `origin/main` nor
`origin/chore/merge-share-history` carries them. The consumers in
`src/compiler/99.loader/` import them anyway:

- `parser_structural_mask_batch_v2.spl:4,12`
- `parser_structural_package_owner_v1.spl:15,22`
- `parser_structural_guarded_call_v1.spl:11`
- `parser_structural_guarded_scope_v1.spl:11`

## Required APIs (from the consumers)

- `compiler.backend.native.parser_byte_avx2_lowering`:
  - `parser_structural_mask_scalar_v1(bytes: [u8], start: i64, count: i64, first_delim, second_delim) -> Result<u32, _>`:
    the scalar reference bitmask over at most 32 bytes.
  - `parser_byte_avx2_callable_bytes_v1(bool) -> Result<[u8], _>`: AVX2 machine code whose
    digest `parser_structural_mask_mapping_authorization_v1_spec.spl:122` pins.
- `compiler.driver.parser_simd_execution_capability_v1`: see the related record.
  Do not mint always-valid receipts.

This is a real feature (the native SIMD lowering plus the capability-receipt
design), not a rename. Stubbing it would hide the gap, so the specs stay
pending.

## To close

Implement both owners, remove `@tag:in-development` from the four specs, and run
them one file at a time.
