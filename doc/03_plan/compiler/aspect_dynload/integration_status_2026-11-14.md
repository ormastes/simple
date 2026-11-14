# Aspect integration status — 2026-11-14

Release checkpoint: `ecb2d5059efcb2f601334e4adc59fc0b24a6c861`.
Status: implementation in progress; neither full feature qualification nor Phase 3 is established.

This update supplements the existing aspect plans and the selected
`doc/02_requirements/feature/dir_tldr_aspect.md` contract. It does not remove
explicit/implicit get/set generation, pointer traversal plugins, visibility,
directory metadata, or build-runner/cache requirements from the active goal.
Historical exclusions must not override the subsequently restored accessor
and traversal scope. Runtime around-advice remains excluded.

## Landed fixes

| Change | Release evidence | Qualification boundary |
|---|---|---|
| Clear pending trace edges across explicit gaps and generation changes | [PR #9168](https://github.com/ormastes/simple/pull/9168), merge `c9fefd76051df962993583e346ff26c58ed5dd2c` | Native extracted production edge handling and normal control passed; not complete tracing qualification. |
| Share pointcut lexing across validation and compiler/interpreter matching | [PR #9175](https://github.com/ormastes/simple/pull/9175), merge `45454acb7c848f3e51ac73ca0da5e09b8accec00` | 57 native extracted-code checks passed. Full-module/SSpec execution remains unqualified. Named ownership and get/set lowering were not enabled. |
| Correct hosted text-to-bytes tagged ABI | [PR #9174](https://github.com/ormastes/simple/pull/9174), merge `ecb2d5059efcb2f601334e4adc59fc0b24a6c861` | Matched C baseline failed; both patched provider link orders and generated Simple indexed-byte/UTF-8/empty/roundtrip checks passed. Other platforms remain unqualified. Bug database updated. |

Each fix received Astra review and passed the blocking push gates. These
scoped bug fixes did not wait for Phase 3; their evidence does not qualify
the unfinished feature branches.

## Feature checkpoints and remaining production connections

| Lane | Implemented/evaluated checkpoint | Required next connection |
|---|---|---|
| Linux LLVM XRay linking | Private runtime materialization executor, compiler-rt/adapter objects, and executable link routes. Executed materialization and final link produced a harness with 40 passing XRay checks. | Probe used explicit existing tuple bindings and a shell file probe. Qualify ordinary imported IO, real Simple-generated instrumentation, handler ABI, and complete compiler/controller path before opening public capability admission. |
| Directory TLDR | Schema-2 roots/provider/guard fields and codec; 11 native codec checks passed with the supported `core-c` provider. [PR #9171](https://github.com/ormastes/simple/pull/9171) remains a draft. | Capture authoritative immediate-directory membership, source/TLDR identity, provider, guards and attributes from one compile epoch; invoke the real AOP cache consumer. Then construct all legacy PackageInit category roots and the complete directory projection. |
| Plugin identity/cache | Code/config descriptor, bounded pool, selector adapter and typed driver API. Native probes passed 11 canonicalizer, 16 SHA/descriptor/pool and 15 projected driver checks. | Actual builtin TraversalPlugin caller, immutable directory authority, generated traversal, closed placement, and admitted provider manifest. Projected closures do not prove full imported-module or HIR integration. |
| Named aspects/accessors | Shared scanner fix landed; accessor architecture reviewed. | Named owner through parser/AST/HIR/cache/codec, supported schema regeneration, then typed generated get/set helpers and native behavior/invalidation tests. Continue rejecting unsupported selectors until their implementation exists. |
| Build runner/Phase 3 | An independent admitted-P2 full-CLI build is being observed without restarting it. | Its command is Stage 2 verification. A live process or partial HIR progress is not a Phase 3 artifact, lineage receipt, or acceptance result. Directory-resident scheduling and performance gates remain open. |

## Integration constraints

1. A compilation's HIR module list is not proof of complete directory
   membership. The existing SCV diagnostic relation is not semantic authority.
   Bind the pinned source inventory to phase-1 source hashes and byte counts,
   actual TLDR embedded source identity, checked provider identity, and
   same-epoch guards/attributes. Missing or ambiguous inputs require the
   existing full traversal. Capture once per compile epoch, not per claim.
2. `PackageInitTldV1` has no production base constructor at this checkpoint.
   Parent, membership, aspect, trait, macro, extension, template and initializer
   roots need actual canonical aggregation. Do not substitute empty strings,
   global catalog hashes, or diagnostic facet digests for complete inputs.
3. HIR forward-advice traversal and MIR advice injection are separate phases.
   The builtin traversal adapter must call the real HIR owner; a typed MIR
   placement must preserve the matched advice form and original instruction
   coordinates. Do not infer advice form solely from join-point kind.
4. Existing `inject_around_advice` prepends a void call; that alone does not
   implement proceed/replacement semantics. A checked placement API must
   reject unsupported around behavior instead of advertising it as complete.
5. The ordinary process-wrapper ABI investigation must inspect both argument
   lowering and `MirCallOrigin.Runtime`. Preserve the origin guard: a callee
   with a similar name is not permission to remap arbitrary application calls.
6. Keep feature branches separate from scoped bug landings. Rebase owned
   branches onto release and use exact force-with-lease when rewriting them.
   Do not repeat passing tests solely because unrelated release files changed.

## Outstanding completion evidence

- Actual Simple-produced Linux LLVM tracing through the public facade,
  capability/profile qualification, low-overhead measurements and static-off
  artifact checks.
- Named ownership and explicit/implicit accessor generation with receiver/RHS
  evaluation, visibility, mutation, result retention and cache invalidation.
- Full selected directory requirements A1/B3/C1/D1/D-T3/E1/F1/G1/H1–H5,
  including authoritative fallback, immutable publication, signed provider
  admission, scheduler behavior and measured performance.
- Compiler/LSP/MCP visibility agreement, live-buffer behavior and the original
  development/release profile requirements.
- Actual Phase 3 artifact and lineage/acceptance evidence; final integration
  review and landing of the completed feature branches.

No item above is considered complete merely because a unit probe, source
review, or server check is green. Acceptance must cover the production path
and the scope of the requirement.
