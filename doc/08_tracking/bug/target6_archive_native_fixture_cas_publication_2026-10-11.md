# Item 6 archived native object fixture stops before CAS publication  2026-10-11

Status: OPEN. This is a focused test blocker, not an Item 6 admission PASS.

## Reproduction

In isolated worktree `work/targets-release-20261010` after commit
`a64c73cae9d`, the admitted pure-Simple Stage 2 compiler
(`e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`)
built `test/fixtures/bootstrap_builder/archive_native_object_admission_main.spl`
with LLVM, `simple-core`, entry closure and `SIMPLE_NO_STUB_FALLBACK=1`.
The third bounded build linked 46 modules and produced
`/tmp/simple-target6-archive-fixture-llvm2` (SHA-256
`07f4359a145f1b7eced133db30c703327a5a0649d447e59ba71acf4d862a25a6`).
Running it in the worktree exits 11 and prints `FAIL CAS publication`.
The relative test CAS root and `objects/sha256/1c` directory exist, but
there is no blob. Therefore no archive admission assertion executed.

The first fixture build used Cranelift and stopped on existing imported-global
and module-static support gaps. The second used LLVM and linked all 46 modules,
then failed on an undefined cross-module
`BINARY_OBJECT_CAS_MAX_BYTES` global. The CAS now exposes
`binary_object_cas_read_full` so the cap stays inside its defining module;
the third build linked successfully. The remaining failure occurs inside
`binary_object_cas_put` or its filesystem primitives. It is not yet
attributed to temp-directory creation, byte writing, publish-noreplace, or
readback. The three-cycle verification limit has been reached.

## Next proof

Instrument each CAS publication stage with a typed result or run one
absolute-root fixture in a fresh scoped session, then require a real
publish/readback and all four fixture assertions to pass. Do not treat the
successful link alone as archive admission evidence. Run the full package
route and paired warm time/RSS cohorts separately.
