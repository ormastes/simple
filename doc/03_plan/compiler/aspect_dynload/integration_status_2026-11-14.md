# Aspect integration status — 2026-11-14

Release checkpoint: `c541817df822dd0d371371034ad79a6a44fd3e1c`.
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

## Initial feature checkpoints at ecb2d5059ef (historical)

| Lane | Implemented/evaluated checkpoint | Remaining work at that checkpoint |
|---|---|---|
| Linux LLVM XRay linking | Private runtime materialization executor, compiler-rt/adapter objects, and executable link routes. Executed materialization and final link produced a harness with 40 passing XRay checks. | Probe used explicit existing tuple bindings and a shell file probe. Qualify ordinary imported IO, real Simple-generated instrumentation, handler ABI, and complete compiler/controller path before opening public capability admission. |
| Directory TLDR | Schema-2 roots/provider/guard fields and codec; 11 native codec checks passed with the supported `core-c` provider. [PR #9171](https://github.com/ormastes/simple/pull/9171) remains a draft. | Capture authoritative immediate-directory membership, source/TLDR identity, provider, guards and attributes from one compile epoch; invoke the real AOP cache consumer. Then construct all legacy PackageInit category roots and the complete directory projection. |
| Plugin identity/cache | Code/config descriptor, bounded pool, selector adapter and typed driver API. Native probes passed 11 canonicalizer, 16 SHA/descriptor/pool and 15 projected driver checks. | Actual builtin TraversalPlugin caller, immutable directory authority, generated traversal, closed placement, and admitted provider manifest. Projected closures do not prove full imported-module or HIR integration. |
| Named aspects/accessors | Shared scanner fix landed; accessor architecture reviewed. | Named owner through parser/AST/HIR/cache/codec, supported schema regeneration, then typed generated get/set helpers and native behavior/invalidation tests. Continue rejecting unsupported selectors until their implementation exists. |
| Build runner/Phase 3 | An independent admitted-P2 full-CLI build is being observed without restarting it. | Its command is Stage 2 verification. A live process or partial HIR progress is not a Phase 3 artifact, lineage receipt, or acceptance result. Directory-resident scheduling and performance gates remain open. |

## Integration constraints

### Later implementation and qualification checkpoint

The release checkpoint now includes AOP error admission and advice-form/MIR
placement fixes (PRs #9177 and #9178), enum metadata preservation through eight
MIR transformations (#9185), and the `Value.get_type` aggregate-pattern arity
repair (#9188; tracker follow-up #9189). Each is a scoped repair with retained
evidence, not full aspect qualification. PR #9181 corrected CI wiring and the
canonical bug-database checksum; its structural and platform checks passed.

Feature branches have been rebased onto the release checkpoint. Named ownership
now has parser/HIR/cache propagation and regeneration through the actual codec
generator; its native transport projection passed 12 assertions. Whole-parser
and cache integration remain unqualified. Generated accessors are not enabled:
receiver retention across advice still needs an actual runtime/backend lifetime
contract. Returning the receiver in a helper tuple is not sufficient proof.

At the earlier feature checkpoint, the directory lane wired source-authority capture to the actual traversal
adapter on the cold path. The full HIR producer/SCV route remains unrun;
bounded ordinary F1 activation is not runtime-proven. Initializer-plan transport is implemented in the
feature branch; final native-link binding and complete category aggregation
remain open. Warm restoration, generated traversal and signed-provider admission
were not established. The canonical codec gate remains closed: the two real-import
qualification attempts hit their 4 GiB and 8 GiB bounds before producing an executable
or runtime golden evidence.
Ordinary bounded snapshots must not be described as canonical qualification.

The Linux current-image identity factory passed a real imported-module native
probe built by the admitted P2 compiler. Its observed executable SHA matched
external hashing. Producer lineage and the executing image remain separate
identities; this does not qualify non-Linux hosts or all loaded provider code.

Visibility intent and resident LSP overlay work remain drafts (#9183 and #9190).
Their source reviews and capped build attempts do not establish runtime access
parity, canonical visibility semantics, or measured query performance.

PR #9191 makes `HirModule.imported_layouts` identity-only. New rows intentionally
contain no fields. Accessor and traversal planning must resolve field layout
from the declaring module or its frozen surface, never from this importer-side
table or redundant payload retained in older caches.

### Bootstrap evidence at this checkpoint

The independent old full-CLI build's tracked processes are no longer present;
its retained records contain no terminal verdict and no full-CLI artifact.
Its outcome is unclassified, not successful.

Owned provisional attempt 1 reached all 1,665 HIR modules and failed on the two
aggregate-pattern arity errors subsequently fixed by #9188. Attempt 2 uses
frozen source `a6ba3cf0566096df12336d9edeab73439f6db36b` and the admitted P2
compiler whose SHA-256 begins `855f48d3c9f9d915`. It reached MIR under a
16 GiB cgroup limit and was OOM-killed (terminal exit 143); there is no
Phase 3 executable/Hello result or admission claim. Logs are retained under
`/home/yoon/dev/simple-phase3-next-20261114/build/phase3-provisional/attempts/002`.
Later upstream changes do not mutate this frozen build. The first attempt's
shared HIR cache use is retained in provenance; attempt 2 selects a private
HIR cache and relies on normal identity validation rather than restamping.

The earlier feature table records initial checkpoints; the following update
supersedes their live-process and implementation-status statements without
upgrading their limited test evidence.

### Subsequent integration evidence

| Area | Retained evidence | Remaining admission |
|---|---|---|
| Target profiles | PR #9219 merged as `cda4d2d059a08ddc77d430d2f1ea54fc2662c9bc`; target profile is independent of optimization and enters managed receipts/cache identity. | Full managed bootstrap and final artifact/profile qualification. |
| Source manifest | PR #9230 merged as `4fb2cc2d3e028e48425412c661d77b5f9213b041`; byte/codepoint slicing repair has native RED/GREEN evidence for Unicode membership. PR #9232 closed its tracker claim. | This does not qualify the entire rebuilt compiler. |
| Linux LLVM observer | Draft PR #9240 at `89b6906053fc02dc571ec25afdc6e29b490e570f` connects semantic maps, resident session source, typed runtime hooks and post-initializer readiness. Public prepare/start reject unqualified profiles before runtime effects. | Real Simple-produced instrumentation through the public facade, qualified handler ABI, bounded process storage and actual quiescence authority. Readiness alone is not quiescence. |
| Handler correction | `92d27334df4` forces two audited hot leaves inline. Retained Clang 18 AArch64 objects show the original calls and the corrected no-call/no-external-branch/no-vector handler. | New CI must qualify its own target; object inspection is not runtime capture evidence. |
| Thread integration | Fixture branch `work/xray-thread-context-fixture-20261114`, checkpoint `7a2bbd23bc9`, links actual runtime thread/native/memory owners; no value/closure stubs. | Execution remains unrun. Its explicit compiler-rt stand-ins cannot qualify sled patching even when this fixture passes. |
| Accessors | Checkpoint `1ab519e7b27728a476e752b51d3fa65153213bd9` has field consumers, hidden helper linkage and transient-root checks (18 static invariants). | Do not land it alone: selector inventory misclassifies an ordinary function named `get`/`set`; atom-aware correction and actual PlanSet production are being integrated. Imported provider layouts and worker-local type relocation need real qualification. |
| Traversal | `cab5dcaf7b099fdef367a186167970165e17d764` contains actual warm restore/reuse/removal source and a scoped core-C lifetime audit. | Actual caller execution/performance, complete session resets, process-image memo ownership and full provider admission. Cross-session reuse is not established. |
| Directory linking | Draft PR #9171 at `d173f40b2ea9216eeebc9eb6e001c89c72049922` joins selected current-build object receipts to fresh initializer/startup/output evidence in four hosted link callers. Receipt helpers passed 13 native checks. | Actual object/aggregate pipeline execution and full PackageInit category roots. Missing, warm or external evidence yields no aggregate authority. |
| Visibility | Semantic-origin draft #9236 at `93c030b670590b764b6b2bbb3be4b68eb37a1361` preserves typed origin facts; policy-only ancestor manifest observation and requester routing remain in progress. | Compiler/LSP/MCP access parity and live-buffer/performance tests. Narrow source roots are not visibility boundaries. |

A distinct peer bootstrap service, `simple-bootstrap-stage3-1794658041-1796856`,
failed with exit 1 at 22:40:17 local time. Its journal reports 28.2 GiB peak RAM
and 5.1 GiB peak swap. The first attributed failure is a Cranelift ABI refusal:
`CudaBackend.compile_const` calls `PtxBuilder.emit_const_float` with an unknown
callee signature and an `f64` argument. Its 1,664 aggregate MIR failures and
zero objects are fallout, not 1,664 independently diagnosed bugs. This peer
used a different producer; it is not owned attempt 2 and yielded no Phase 3
artifact. Missing systemd unit defaults must not be read as a successful exit.

The declared-parameter repair preserves parameter metadata independently of
an absent inferred return type, including imported nominal identities. Source
`c255b7a1938` and generated-code/test checkpoint `b0ad096fc9d` are unqualified:
the actual generator reproduced the release baseline and generated 99
declarations, but authored compiler/MIR/roundtrip tests remain unrun. An old
receiver-tail workaround cannot handle this call's named enum parameter.
Changing target source alone cannot repair the already-running P2 producer.

The next provisional bootstrap controller has source review and focused
control tests, but no third attempt has launched. A new frozen source/producer,
live build inventory, memory admission and disk admission remain mandatory.

Remaining directory work has explicit owners: the PackageInit lane owns
A1/B3 roots/publication; cutoff/scheduler owns C1/D1/D-T3; traversal owns F1;
the admission lane owns H1–H5. Coordinate E1/G1 interfaces with those owners.
Complete PackageInit authority is a prerequisite for propagation cutoff;
descriptor code identity alone is not an admitted plugin allowlist.

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
