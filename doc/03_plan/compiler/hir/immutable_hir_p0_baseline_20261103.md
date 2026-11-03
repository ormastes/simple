# Immutable HIR / TargetHIR P0: revision and execution evidence

Date: 2026-11-03 KST. Status: source inventory in progress; runtime and performance baseline incomplete.

## Scope and revision

The governing plan is `immutable_hir_targethir_mir_refactor_plan_2026-11-03.md` in this directory. This adoption lane starts at release commit `4fccb94e564b25a0a2effdd711113da5a1b1e20c`, on `work/targethir-foundation-20261103`. This lane changes documentation only. It does not enable TargetHIR, change a compiler default, introduce a portable-cache authority, or claim completion of P1–P8.

The previous `work/hir-host-view-20261103` experiment is separate, unmerged, and frozen. Its closure-wide preparation, codec-dependent admission, incomplete deep-freeze ownership, and default strict routing do not meet the governing plan. Its authored tests are unexecuted. It is reference material, not an admitted implementation or a benchmark baseline.

P0 companion inventories:

- `immutable_hir_p0_ownership_inventory_20261103.md`: ownership, freezing, publication, container aliasing, and pin primitives.
- `immutable_hir_p0_mir_inventory_20261103.md`: entry points, target context, mutation, streaming, and transient/archive ownership.
- `immutable_hir_p0_cache_inventory_20261103.md`: semantic target dependence, cache/codec admission, transitions, and final-object reuse.
- `immutable_hir_p0_field_classification_20261103.md`: field ownership and semantic-versus-target classification at the subsequent pinned release revision.

## Existing bootstrap evidence inspected

The provisional producer binary was hashed during this inventory. Its SHA-256 is `e08760304ddc7a441fe7f9d9a71afebdd3b129f217d6e49b04cb47bb70411553`.

Local evidence root:

`/private/tmp/simple-tuple-value-contract-20261101/build/cross-bootstrap/tuple-value-contract/worktree-storage/build/bootstrap/stage3/aarch64-apple-darwin/`

| Evidence | Observed result | Limit |
|---|---|---|
| `stage2-admitted/simple` | Hash matches the exact provisional producer above | Directory naming is not qualification authority |
| `stage2-sanity.env` | Records version, unsupported-command, and frontend bootstrap-0/bootstrap-1 smoke success; stable candidate hash | Historical bounded smoke receipt; no new execution in P0 |
| `stage2-receiver.env` | Records receiver probe and runtime comparison success; stable candidate hash | Narrow receiver evidence, not a full compiler/test-runner qualification |
| Phase 3 attempt-6 `inputs.sdn` | Explicitly records `formal_admission: false`, `deployment: false`, and a separate full-stage-2 rejection receipt hash | Successful earlier smoke must not be promoted into general runner authority |
| Phase 3 attempt-6 scheduler | Waiting for resources when inspected; no candidate compiler launch or new-candidate Hello result | Not a build/test pass |

The Phase 3 campaign is separate from this documentation lane:

`/private/tmp/simple-provisional-phase3-20261102/build/cross-bootstrap/phase3-campaign-12h-20261102/`

Its frozen source is `7e01401d530aa79a56e0d11ef859aefb372571d6`, tree `1e063060a3de86e19aabf009a6b3961ad8056144`. This contains two separately reviewed common fixes; it contains no TargetHIR implementation. The producer hash is the one above. Attempt 6 records a 12 GiB reserve, a 13.5 GiB launch threshold, one build job, and an original campaign deadline of `2026-11-03T00:24:52Z`. At the inspected 23:45:29 UTC sample, available-memory accounting remained below the launch threshold. A host-memory sample is not compiler peak RSS.

The full-stage-2 rejection was subsequently located, read, and hashed at `worktree-storage/build/bootstrap/stage2-compiler-tests/aarch64-apple-darwin/rejection.env` under the producer lane. Its SHA-256 is `f5e46d7700cb0fd249f67a8c5e6acfef9573fe33f8fb9319480a22eb87d10f1c`; it explicitly rejects producer `e087…1553` with `stage2-compiler-tests-failed`. Byte-identical copies of this receipt, its verification summary, and its process resource receipt are preserved in `doc/09_report/evidence/immutable_hir_p0_20261103/`.

The historical verification summary records CLI build failure (status 255, 1,817 seconds, maximum RSS 10,718,544 KiB) and test-runner build failure (status 117, 96 seconds, maximum RSS 2,638,000 KiB). Both artifacts have `producer-failed` status and `behavior_qualified=0`. The process receipt records an unsuccessful campaign with peak RSS 10,849,600 KiB and enforced RSS limiting. These are measured failed-run observations, not successful compile benchmarks, not CPU time, and not a comparable p50/p95 baseline for the proposed refactor.

## Baseline matrix and outstanding work

| Baseline | Current evidence | P0 disposition |
|---|---|---|
| Exact current source and artifact identities | Recorded above | Identified, not qualified |
| Stage 2 narrow smoke | Existing receipts inspected | Historical narrow evidence only |
| Full CLI and test-runner qualification | Exact rejection, summary, and process receipts inspected and preserved | Not admitted; retain historical failures separately from new refactor findings |
| Fresh Phase 3 link and exact-candidate Hello | Resource scheduler waiting | Missing |
| Stage 4 native qualification | No current successful evidence established in this inventory | Missing |
| Single-target compiled wall p50/p95 and CPU time | No equivalent admitted run collected | Missing; no speed claim |
| Compiler peak RSS, retained bytes, allocation counts | No current comparable measurement collected | Missing; scheduler headroom is not a substitute |
| One/two/four/eight-target comparisons | Not executed | Missing |
| Warm final-OBJ no-HIR path | Source contracts inventoried separately | Consumer execution evidence missing |

Before calling P0 complete, review the source/SSpec map and collect a reproducible CPU/RSS baseline using a qualified runtime when resource admission permits. Preserve immutable successful artifacts and record unsuccessful commands; do not repeat unchanged failures or already-green checks.

## Implementation and landing boundary

The first source increment must follow PR-A: nominal IDs and read-only facades without changing existing lowering, cache authority, or defaults. A facade over a mutable `Dict`, list, or `SymbolTable` is not proof of P1 freezing. No `FrozenRef`, publication primitive, private-constructor enforcement, or runtime pin capability may be invented as if already implemented.

The mandatory TargetHIR-only MIR boundary is a staged destination. Keep legacy adapters available until the migration matrix and native gates pass. Preserve fused per-region source-to-object execution; do not replace it with the previous experiment's whole-closure serialization/admission barrier.

Documentation review and a documentation-only merge do not establish compiler verification PASS, P0 runtime-baseline completion, or permission to enable the refactor by default.

## Follow-up observation: 2026-11-03 00:07 UTC

The governing plan and initial inventories landed through documentation-only PR #5973, merge `2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d`. The source findings above remain observations of their recorded revisions. The field-classification follow-up uses this merge as its source pin; it does not silently refresh earlier source claims.

The separate bootstrap lane was rebased onto that merge. Its new frozen candidate is `0ec4fe1b0854d437c8112092a91a58ab689df300`, tree `94347e7a3ebdf5bfc0c75c59d93a055f9e3a19d5`. Upstream now supplies the tuple production corrections; the candidate's sole production delta removes a duplicate enum-provider method. Astra approved this exact candidate for freeze/build, with landing still conditional on fresh Phase 3 link and exact-candidate Hello.

Attempt 6 stopped without launching a compiler. Attempt 7 started its resource scheduler at 00:05:51 UTC, retaining producer `e087…1553`, the 12 GiB reserve, 13.5 GiB launch threshold, one build job, and original 00:24:52 UTC deadline. At that first sample, narrow available memory was 11,751,260,160 bytes and canonical available memory was 12,136,136,704 bytes. Both were below the launch threshold; no compiler child had started. This is a scheduler observation, not execution or performance qualification.

The candidate contains no TargetHIR implementation. This follow-up adds no runtime pass, does not complete P0, and does not admit the frozen host-view experiment.
