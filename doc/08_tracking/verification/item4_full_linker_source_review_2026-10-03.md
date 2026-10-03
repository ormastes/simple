# Item 4 linker source review — 2026-10-03

**Full-item STATUS: FAIL — required implementation and execution evidence remain
incomplete. Reviewed source slices do not qualify production or release PASS.**

## Reviewed snapshot and scope

Reviewer: Codex `/root/linker_research`; integration owner: `/root`.
Reviewed `C:/dev/simple-item4-linker-dev-20261003` at base commit
`69edfa7f629901a53b617ad576372b58f88dec3d`, including the root-owned working
versions of `native_freestanding.spl`, `native_image_publish.spl`, and their
wrapper wiring. This is not immutable final-head release evidence.

Follow-up source review inspected Mach-O lane commits `3bb1e6c722d` and
`95c693a3e70`, including `dylib.spl`, `export_trie.spl`, opcode/dependency
corrections, and their real-fixture specs.

Source review covered `macho/{input,layout,symbols,relocations,macho_static_link}.spl`
under `src/compiler/70.backend/linker`, the two native adapters, and their
acceptance specifications. Imported parser/relocation structures, function
signatures, runtime IO exports, `std.path.resolve`, and native receipt fields
were compared with their definitions. No compiler or interpreter was run.

## Findings and limits

- **Resolved in source review:** ARM64 PAGEOFF12 previously admitted SUB/SUBS.
  Mask `0x7f800000` now constrains ADD; real ADD fixture mutations cover SUB,
  flag-setting, and reserved encodings. The regression is still **UNRUN**.
- **Resolved in source review:** `LC_LAZY_LOAD_DYLIB` was omitted, potentially
  shifting dependency ordinals. Commit `95c693a3e70` uses the checked dependency
  parser and ordered append; its real-command mutation tests provider identity,
  versions and ordinal lookup. **UNRUN**. The command is defined in
  [Apple's Mach-O header](https://github.com/apple-oss-distributions/xnu/blob/main/EXTERNAL_HEADERS/mach-o/loader.h).
- No additional P0/P1 was identified in these reviewed source slices after the
  corrections. This does not clear the full-item implementation/evidence gates.
- The initially observed literal-path-only alias guard was superseded during
  review. The current adapter resolves lexical paths against `cwd`, folds case
  on Windows, and includes a dot-component alias regression. Filesystem identity
  and hostile-directory admission are explicitly outside this fast-path contract.
- Input validation, resolution, relocation, and size failures precede native
  publication. Publication stages permissions before replacement. Its backup /
  restore fallback is best-effort recovery, not gap-free atomic replacement.
- Mach-O produces a resident, fixed-address, stripped, freestanding image;
  explicit rejection of unsupported records does not complete hosted Mach-O.
- The dylib/export-trie reader checks record bounds, ULEB limits, owning string
  extents, mapped addresses, cycles, reexport ordinals and resolver metadata.
  Reading provider contracts is not dyld binding, loading or signature admission.

## Evidence not established

| Gate | Status |
|---|---|
| Executable acceptance specs / observed RED and GREEN | **UNRUN**; no admitted runtime result |
| SPipe generated manuals and zero-stub docgen | **UNRUN** |
| Branch coverage, fuzz/stress, native loader execution | **UNRUN** |
| Full compiler/lib checks, core runtime and MCP native smoke | **UNRUN** in this review |
| RSS, constrained-process/no-swap, performance comparison | **UNRUN** |

The three authored manuals `item4_freestanding_adapter_spec.md`,
`item4_freebsd_hosted_spec.md`, and `item4_freebsd_native_spec.md` under
`doc/06_spec/03_system/app/compiler/feature/` were compared with their executable
specs. Their scenario flows and explicit UNRUN status are accurate, including
lexical aliases, independent build-id hashing, CRT selection, and native exit 42.
This editorial review is not canonical generation or zero-stub evidence.

Five additional authored manuals were reviewed: Mach-O static/dylib, RV64
static, bounded storage, and ELF file reader. The owner corrected dylib
requirement IDs to match its executable spec and removed the reader manual's
unsupported-entry-width scenario claim, which had no corresponding test.
After RV64 integration through `fc52c20`, the ALIGN flow matches the authored
positive/negative scenarios. The storage manual correctly distinguishes committed
publication from pending cleanup. All eight retain explicit **UNRUN** labels;
manual flow review is accepted only as editorial source evidence.

## Remaining implementation and qualification gates

- **Bounded path:** checked file-backed spill, retained ELF records, and section
  emission exist. Full bounded resolution/indexing, archive consumption, layout,
  relocation/image streaming, and constrained-worker accounting remain open.
  Serialized metadata and output-byte caps are not RSS limits. Preserve
  `UnsupportedBudget` until the complete enforcing execution path exists.
- **Mach-O/dyld:** dyld application loading, GOT/TLV/TLS/authentication, unwind,
  signing and Darwin execution qualification remain separate open work.
- **G5 lifecycle:** generation-pinned callbacks and independent static recovery
  are implemented; actual capsule/provider loading, runtime replacement,
  composition admission, and host recovery qualification remain unproven.

Source inspection must not be reported as full compiler acceptance, coverage,
performance evidence, or production/release PASS.
