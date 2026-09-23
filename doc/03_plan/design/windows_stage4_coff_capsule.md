<!-- codex-architecture -->
# Windows Stage 4 compiler-backfill capsule: bounded design

Status: blocked on a proven COFF archive-closure mechanism. Source revision:
`92af30bcf3dc7c1a79724479a513c2373d04628e` (exact92). This plan does
not admit Windows Stage 4 or change the full-CLI host guard.

## Existing contract and gap

- `src/compiler/70.backend/backend/stage4_symbol_closure.spl` already
  canonicalizes COFF provider symbols and validates several Windows runtime
  providers. Its compiler-backfill archive, format, manifest, localization,
  envelope, and provider-disjoint policies still accept only ELF/Mach-O.
- `src/compiler/70.backend/backend/llvm_native_link_stage4_archives.spl`
  derives the backfill export manifest, links an archive closure into one
  relocatable object, localizes all non-export definitions, rejects runtime
  ownership and initializer sections, and fingerprints the archived result.
  The closure invocation at lines 102-114 is ELF/Mach-O-specific; the object
  and member names are `.o`.
- `src/compiler/70.backend/backend/llvm_native_link_stage4_projection.spl`
  has a separate selected-archive closure at lines 266-299 using the same
  relocatable-link assumption. Windows needs this gate too.
- `scripts/bootstrap/bootstrap-from-scratch.sh` lines 1052-1059 deliberately
  permit `--full-cli` only on native Linux or macOS.

The current MSVC seed artifact
`src/compiler_rust/target/bootstrap/simple_compiler_backfill.lib` was
14,377,340 bytes with 345 archive members. LLVM 23 `llvm-nm -g -p` found 76
`rt_cranelift_*` definitions. The installed LLVM 23 `lld-link /?` supports
`/lib`, `/include`, and `/wholearchive`, but advertises no relocatable object
output. `ld.lld -m i386pep -r ...` rejects `-r` as an unknown argument.
These tool probes do not establish that an MSVC capsule can satisfy the
single-object localization contract.

## Required implementation boundary

1. Carry the already validated Windows object/linker ABI from
   `llvm_native_link_orchestrator.spl` into both archive builders. Choose
   `simple_compiler_backfill.lib` + `coff-msvc` only for MSVC and
   `libsimple_compiler_backfill.a` + `coff-mingw` only for MinGW. Reject mixed
   ABI inputs before any output is created. Preserve ELF/Mach-O behavior.
2. For COFF, derive roots from the exact raw `rt_cranelift_*` definitions.
   Preserve raw symbol spelling for linker and object tools; canonical names
   are only for ownership comparisons. Reject duplicate roots, excluded
   wrappers, unexpected `rt_`/`spl_` definitions or dependencies, empty scans,
   and archive/member scans that disagree. Inspect `.CRT$XI`, `.CRT$XC`,
   `.CRT$XP`, `.CRT$XT`, and `.CRT$XL` before accepting a capsule.
3. Prove an archive-member closure that extracts only needed COFF members,
   resolves their transitive references (including weak externs and COMDAT),
   and makes every non-ABI global private without breaking cross-member
   references. A member rewrite must compare raw and rewritten symbols and
   relocations, then validate the final archive index. If the available tools
   cannot supply this proof, return an explicit unsupported-toolchain error.
   `/wholearchive` of all 345 members is not a size-preserving substitute.
4. Apply the same proven mechanism to the selected-provider projection, or
   keep Windows Stage 4 closed. The compiler capsule alone does not complete
   the strict Stage 4 path.
5. Keep the full-CLI host guard until both ABIs pass a no-stub native link,
   symbol-ownership/section checks, and a measured default binary-size gate.
   A successful `llvm-ar` archive command or exit-zero build without a
   runnable binary is insufficient.

## Focused verification

- Unit: MSVC and MinGW archive identities, object formats, ABI mismatch,
  exact COFF manifest/localization, duplicate exports, `__imp_` dependency
  handling, provider overlap, and unsupported format rejection.
- Native fixtures per ABI: a two-member transitive dependency, duplicate
  strong definition, weak/COMDAT member, import dependency, constructor
  section, and private symbol collision with a runtime provider. Check the
  selected archive members and the final linked executable's symbol table.
- End-to-end: strict Stage 4 CLI built with
  `SIMPLE_NO_STUB_FALLBACK=1`, runnable smoke, selected archive proof, and
  default binary size compared with the admitted Windows baseline. Run the
  same gates separately for MSVC and MinGW. Remove the host guard only after
  this evidence is complete.

Sidecar lanes: N/A for this bounded design. Merge owner: Phase 4 integration
owner. Final reviewer: primary high-capability agent after executable proof.
