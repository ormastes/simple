# Item 4 linker source review — 2026-10-03

**STATUS: WARN — source review only; full item 4 and release acceptance remain open.**

## Reviewed snapshot and scope

Reviewer: Codex `/root/linker_research`; integration owner: `/root`.
Reviewed `C:/dev/simple-item4-linker-dev-20261003` at base commit
`69edfa7f629901a53b617ad576372b58f88dec3d`, including the root-owned working
versions of `native_freestanding.spl`, `native_image_publish.spl`, and their
wrapper wiring. This is not immutable final-head release evidence.

Source review covered `macho/{input,layout,symbols,relocations,macho_static_link}.spl`
under `src/compiler/70.backend/linker`, the two native adapters, and their
acceptance specifications. Imported parser/relocation structures, function
signatures, runtime IO exports, `std.path.resolve`, and native receipt fields
were compared with their definitions. No compiler or interpreter was run.

## Findings and limits

- **Open P1:** ARM64 PAGEOFF12 checks ADD with mask `0x1f000000`, also admitting
  SUB/SUBS immediate instructions. It can return a successful incorrectly patched
  instruction. Sent to the integration/Mach-O owners: constrain the opcode and
  add a real fixture mutation regression. Fix acceptance is pending independent
  source review; this finding is not an observed runtime failure.
- The initially observed literal-path-only alias guard was superseded during
  review. The current adapter resolves lexical paths against `cwd`, folds case
  on Windows, and includes a dot-component alias regression. Filesystem identity
  and hostile-directory admission are explicitly outside this fast-path contract.
- Input validation, resolution, relocation, and size failures precede native
  publication. Publication stages permissions before replacement. Its backup /
  restore fallback is best-effort recovery, not gap-free atomic replacement.
- Mach-O produces a resident, fixed-address, stripped, freestanding image;
  explicit rejection of unsupported records does not complete hosted Mach-O.

## Evidence not established

| Gate | Status |
|---|---|
| Executable acceptance specs / observed RED and GREEN | **UNRUN**; no admitted runtime result |
| SPipe generated manuals and zero-stub docgen | **UNRUN** |
| Branch coverage, fuzz/stress, native loader execution | **UNRUN** |
| Full compiler/lib checks, core runtime and MCP native smoke | **UNRUN** in this review |
| RSS, constrained-process/no-swap, performance comparison | **UNRUN** |

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
