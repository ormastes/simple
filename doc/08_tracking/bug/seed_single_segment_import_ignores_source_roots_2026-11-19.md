# Seed resolver ignores --source roots for single-segment imports

- id: seed_single_segment_import_ignores_source_roots_2026-11-19
- status: verification-pending
- severity: P1 (blocks every riscv64 authenticated-media kernel build)
- found by: lane ssos-launch

## Symptom

`use rv64_auth_trust_config.{...}` in
`src/os/kernel/loader/riscv64_authenticated_media_fixture.spl`, with the
generated module at `<gendir>/rv64_auth_trust_config.spl` and
`--source <gendir>` on the `native-build` line, fails with E1034
"module `rv64_auth_trust_config` not found" (help names only the importer's
directory). Pre-existing: `rebuild-sosix-qemu-media.shs` riscv64 rows use the
same spelling and fail the same way; `scripts/check/use_target_resolves_baseline.txt`
lists the import as MODULE_MISSING.

## Cause

Native discovery finds the file through its source-root fallback
(`pipeline/native_project/discovery.rs`), but `ModuleResolver::resolve`
(`module_resolver/resolution.rs`) only tries source roots in Strategy 4, which
requires `segments.len() > 1`. A single-segment name never reaches them.

## Fix

Strategy 4b: a single-segment, non-`crate` name is resolved against each
ordered source root after the importer-directory attempt (so a sibling module
still wins).

## Tests

`module_resolver::tests::single_segment_import_resolves_from_extra_source_root`
(RED before the fix, GREEN after) and
`single_segment_import_prefers_importer_directory` (precedence guard).

## Verification still owed

riscv64 kernel native-build with the generated trust module, and the OpenSBI
rung `scripts/check/check-simpleos-riscv64-user-elf-opensbi.shs`.
