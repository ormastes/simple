# G1 generic collector semantic port — source evidence

## Provenance and scope

Authorized checkout `/home/yoon/dev/simple-phase3-mir-followup-20261018`; pre-edit HEAD `bca7d65434cc1b72e012ea30b8f1605800b553ab`. Collector preimage SHA-256 `42f7b4c4c9ce649fe1e031edb8c1502256db4c81444427bd232a7947b1ffd3df`; preimage record `/tmp/g1-collector-port-preimage-20261021.json`. The main worktree, immutable captures, prior current-input checkpoint and active MIR files were not edited. MIR ownership coordinator confirmed the collector is disjoint.

Known reviewed candidate `f392d4f24996becb7312b407e6f2b1dca2c47524` contains the retained-values/scalar-index collector change. `a9e752067a828e1e45afc9d69f6f1c47ec7ac22b79a94653ead0ad4c95e3e7f2` is the SHA-256 of `/tmp/9ce-collector-incremental-20261021/production.patch`, not a commit. It changed captured producer source `14ce1cc8…` to `83b5a163…`. Earlier independent review `/tmp/phase3-collector-port-independent-static-review-20261021.json` covers a different remote-composed source result; this G1 result requires its own review.

Only the collector walk and extraction helper were semantically ported; raw patch application failed because G1 has different surrounding source. The port retains typed `HirFunction` values and accesses them by scalar array index instead of copying aggregate `SymbolId` keys and looking up the dictionary again. Existing symbol/name/return/template registration remains unchanged. Existing `SIMPLE_MONO_DIAG` emits provider summary and at most 32 entry descriptions; no new semantic option was added.

The unit/native regressions derive from f392. G1 lacks its separate class-static template owner API, so that independent Factory scenario is omitted explicitly while standalone generic, ordinary and existing generic-impl owner assertions remain. No class-static feature was silently ported. The original bug note is preserved verbatim; this report records current evidence limits.

## What the retained failure proves

`helper-attempt2-9ce/terminal-assessment.json` records producer `9ce404cd5e5383a62cdc06c1e0f84152a9b07e057f5bd34266fac116025c1cc8`, 97 closure modules completed, 80 emitted native objects, 123.7757779052481 seconds, and link failure. `undefined-symbol-evidence.json` identifies consumer `aot-565e8afc…` with undefined ordinary `lib.nogc_sync_mut.sffi.transient.transient_promote`; provider `aot-55cf043e…` defines only the three nongeneric scope wrappers. Both files are under `/tmp/phase3-r4-link-recovery-20261020/helper-attempt2-9ce` and remain immutable. The generic template was not emitted into the linked provider, while its caller retained an unspecialized call. This alone does not prove which current producer stage is faulty.

Earlier final inferred diagnostics reported no discovered generics before root traversal; roots=0 was an early-return profile value, not independent missing-function evidence. The copied-key collector defect is the known source correction, not a newly diagnosed cause in the newer producer.

## Newer producer evidence stays separate

Candidate `11e2fe732e73eb392e414e4e4f58e073dfab236778a65ca99c4810b12266ff3f` already includes the captured-source collector patch and passed native Hello World. Its inferred promotion build timed out once after 300.416 seconds, exit 124, with HIR 2/2 reported, zero native objects and no link/runtime result. Evidence: `/tmp/rebuilt-compiler-qualification-20261021/revision3-target-hello/inferred-terminal-assessment.json`. That timeout does not prove the previous undefined symbol remains, nor identify the hot phase. The queued jobs=15 phase-profile/mono diagnostic belongs solely to the execution owner.

## Verification and remaining work

This G1 port is source-only; tests/builds/runtime UNRUN. No rebuilt compiler, failed-object repair, successful promotion lifetime, helper link, 41 runtime/startup regeneration, or final 302-object runner link is claimed. No existing object compatibility changes merely because source was ported. Preserve the old producer/source/runtime/tool bindings and requalify any changed producer before reuse. Independent exact-file source review and local checkpoint follow this freeze; runtime launch remains prohibited in this lane.

Required next evidence is the bounded changed-producer phase/mono trace locating the timeout. A completed promotion specialization must show the emitted specialization and caller target at HIR/mono and MIR/object boundaries, plus the linked native lifetime assertion. Only then can the failed object/helper path be repaired and linked without silencing undefined symbols or mixing unproven objects.
