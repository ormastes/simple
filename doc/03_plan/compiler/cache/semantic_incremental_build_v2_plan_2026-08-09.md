# Semantic Incremental Build v2 — Implementation Plan

**Status:** Proposed
**Date:** 2026-08-09
**Design:** `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md`
**Supersedes scope of:** `doc/03_plan/compiler/cache/global_cas_interpreter_cache_option_c_plan_2026-07-24.md` (Option C remains the identity substrate; this plan wires it into tiers, GC, AOP groups, block reuse, and Lean verification)

---

## 1. Scope in one paragraph

Wire the existing Phase-1 CAS (`src/compiler/80.driver/cache/cas_store.spl`) into a
three-scope cache (workspace / machine / remote), add bounded storage with GC and
leases, split the coarse AOP digest into layered invalidation groups, add
function-private block-level reuse for selected dataflow passes, and generate both
the Simple encoders and the Lean 4 model from one SDN schema. Git history controls
**admission** only — never semantic action identity.

## 2. Non-goals for v2

- No second CAS, no second action-key scheme.
- No block-level machine-code emission or independent relocation.
- No remote-main writes from developer machines, ever.
- No prefix/restore-key/nearest-branch cache fallback for compiler artifacts.
- No automatic proof synthesis; generated definitions + durable manual theorems only.

---

## 2b. Reality gaps found during C0 recon (2026-08-09)

The design doc was written against the intended architecture. Recon against the
actual tree found four assumptions that are **false today**. Prerequisite work is
now explicit rather than implied.

| Design assumes | Actual tree | Consequence |
|---|---|---|
| Pointcuts with normalized queries, a matcher schema, and `pub pointcut` publicization (§16) | **No pointcuts exist.** `85.mdsoc/weaving/` has join points only (`join_point_kind.spl:4-10`, `join_point.spl:7-21`). "Matching" is an untyped `WeavingRule.predicate_text` string (`weaving_config.spl:48`). No visibility rules on join points — all are global. | `AopSurfaceKey` / `AopSelectionKey` are SPEC-FORWARD. Prerequisite: a normalized pointcut query + typed matcher replacing `predicate_text`. Until then a selector can only read `JoinPointContext`'s real fields: function_name, module_path, signature, attributes, effects. |
| Per-target weave artifacts (§16.2 `AopWeaveKey`) | Weaving **mutates MIR in place** (`50.mir/mir_aop_injection.spl:21-86` returns a modified `MirFunction`). No per-target artifact is produced. | `AopWeaveGroup` is SPEC-FORWARD. Prerequisite: make weaving emit a per-target artifact before it can be cached or invalidated per target. |
| Stable block identity (§17.2) | `BlockId` is a bare integer: `struct BlockId: id: i64` (`50.mir/mir_instruction_support.spl:9-21`), entry = 0. `JoinPoint` also references its target by this transient `BlockId`. | `BlockKey` must be a **new, separate** type. `BlockId` is a transient in-run handle and must never be serialized into a cache key. A `BlockId → BlockKey` mapping is required. Join-point identity is likewise unstable today. |
| An existing dataflow framework to attach block reuse to (§17.4) | **None.** No lattice, no worklist, no transfer-function abstraction in `50.mir` or `60.mir_opt` — one inline "backwards dataflow" comment in `dce.spl` and nothing more. | Block-level reuse has no substrate. Phase 7 gains a prerequisite: build the worklist/lattice abstraction first. Also: the optimizer path is `60.mir_opt`, not `60.optimizer` — correct this in all agent file-ownership assignments. |

Additional baseline facts:

- `src/compiler/80.driver/cache/action_key.spl` (221 lines) already exists and already computes the canonical key — Phase 1, compute-and-log only.
- The canonical KEY list is already frozen at **15 fields** and already proven in `cache_identity/Model.lean`. The AOP group split is a **refinement of the single existing `aopSelection: Sha` field**, so `aop_change_visible` must be re-derived over the new group roots.
- Ten theorems already proven, including `no_false_hit` and `stamp_fast_eq_strict`.
- `cas_store.spl` and `action_key.spl` have **zero callers** — free to reshape, nothing breaks.
- The live cache is `.build_cache.sdn` plus `.build/mir_cache/`, whose keys are function names run through `replace("/","_").replace(":","_")` — a sanitization collision, and the concrete reason Phase 2 retires it.

## 3. Wave plan and file ownership

### Wave C0 — serial contract freeze

**C0 — Cache protocol and formal schema owner**

Owns `src/compiler/80.driver/cache/schema/` and the design doc.

Delivers cache tier/trust enums, namespace model, result and promotion manifests,
AOP group identities, block key/input/result schemas, GC root/lease/state schemas,
canonical encoding rules, generator input, and the exported-name contract.

**Gate:** canonical order fixed; every semantic field classified as key,
provenance, local state, or GC metadata; no downstream agent invents another key.

### Wave C1 — parallel foundations

| Agent | Owns | Delivers |
|---|---|---|
| **C1** CAS + tier router | `cache/cas_store.spl`, `cache/tier_router/`, `cache/action_index/` | wire CAS into local/machine paths; immutable result manifests; exact lookup + read-through/backfill; action-mapping conflict detection; process single-flight; streaming + strict digest verification |
| **C2** Remote policy + provenance | `cache/remote/`, `cache/promotion/`, `scripts/cache/promotion/` | remote client; repository identity; authenticated main-snapshot receipt; Git ancestry gate; signed `PromotionReceipt`; main/branch namespace policy; squash/rebase handling; read-only developer mode |
| **C3** Quota, metadata, leases, GC | `cache/gc/`, `cache/lease/`, `cache/metadata/` | high/low/hard watermarks; free-space reserve; fast eviction; full mark-and-sweep; pins and leases; crash-safe trash/quarantine; refcount repair; dry-run/explain |
| **C4** AOP cache groups | `src/compiler/85.mdsoc/aop_cache/`, `aop_index/` | group manifests; candidate Merkle partitions; selector read sets; reverse dependency tables; per-target selection shards; precise invalidation transaction; trust eligibility |
| **C5** Block dependency + result cache | `src/compiler/50.mir/incremental/`, `src/compiler/60.optimizer/incremental/` | stable `BlockKey`; block/region manifests; incremental dataflow worklist; function fallback; pass eligibility policy; small-result packing; pre/post-weave identity derivation |
| **C6** Generated Lean model | `src/app/gen_cache_model/`, `src/verification/cache_protocol/`, `scripts/check/check-cache-protocol-formal.shs` | SDN→Simple and SDN→Lean generator; generated field-coverage theorems; promotion/AOP/block/GC models; durable manual proofs; no-trust-bypass gate; executable trace checker; golden vectors |
| **C7** SSpec + adversarial fixtures | `test/0{1,2,3}_*/compiler/cache_v2/`, `scripts/check/check-cache-v2-*.shs` | branch/main history fixtures; corruption and poisoning cases; concurrent put/GC/read; AOP mutation matrix; block CFG mutation matrix; disk-pressure and crash-recovery; clean/cached equivalence harness; baseline telemetry. **No production compiler edits.** |

### Wave C2 — integration

| Agent | Depends on | Owns | Delivers |
|---|---|---|---|
| **C8** Semantic query/build integration | C1, C3, C4, C5 | `cache_integration/`, `query_store/` | query result manifests; workspace-DB→machine/remote artifact bridge; AOP and block roots in action keys; exact tier lookup; strict shadow comparison; explain paths |
| **C9** CI promotion + remote gateway | C1, C2, C3, C6 | `.github/workflows/cache-*`, `scripts/ci/cache-*`, `src/app/cache_gateway/` | trusted-main writer workflow; optional branch namespace; policy gateway/backend adapter; signed receipts; remote quota/TTL; metrics and admin |

### Wave C3 — bootstrap and certification

| Agent | Depends on | Owns | Delivers |
|---|---|---|---|
| **C10** Bootstrap/component integration | C8 | `scripts/bootstrap/cache/`, `src/app/cli/native_build_cache_v2/` | componentized bootstrap lookup; retained bootstrap roots; selected-backend closure caching; strict release/bootstrap policy; no full-source probe on warm component build |
| **C11** Formal + adversarial certification | C7, C8, C9, C10 | `src/verification/cache_protocol/certification/`, `doc/09_report/cache_v2_certification_*.md` | proof gate results; strict/fast/tier parity; clean/cached artifact equality; remote-main attack simulation; GC model/impl trace equivalence; AOP precision+soundness; block incremental/full equivalence; readiness decision |

### Merge order

```text
C0
↓
C1 + C2 + C3 + C4 + C5 + C6 + C7
↓
C8 + C9
↓
C10
↓
C11
```

### Execution policy — worktree isolation

Every parallel agent from Wave C1 onward runs in **its own git worktree**
(`isolation: "worktree"`), never in the shared working copy. Seven agents editing
one tree concurrently is the documented failure mode in this repo: uncommitted
edits get clobbered by a sibling's snapshot, and a stale whole-WC commit reverts
landed work. Isolation also makes each agent's diff independently reviewable
before it merges.

Consequences:

- Each agent's result is a diff against its own worktree; integration is a
  deliberate merge step, not an implicit side effect of it running.
- Agents must not assume a sibling's files exist. Cross-agent contracts flow only
  through the C0 frozen schema and freeze note, both landed in the shared tree
  before Wave C1 starts.
- Merge order (below) is also the review order. Nothing merges before C0's schema
  is on `main`.
- C0 itself runs in the shared working copy — it precedes the fan-out and its two
  new files are touched by no other agent.

### Per-stage harden-and-push loop (mandatory)

Sibling agents bootstrap off `main` continuously. A stage that pushes a tree
which does not bootstrap does not only break itself — it burns a session for
every agent that fetches next, chasing a failure that is not theirs. So each
stage hardens **before** it pushes, never after.

For every stage that lands:

```bash
# 1. lint only what this stage changed
bin/simple lint <changed .spl files>

# 2. the stage's own runnable checks must be GREEN, and each negative
#    check must have been OBSERVED failing when its bad state was injected
bin/simple test <stage spec paths>

# 3. one composed gate: 3 pre-push guards + bootstrap smoke, fail-closed
sh scripts/check/check-cache-v2-stage-gate.shs

# 4. only on PASS
sj bookmark set main -r @- && sj git push --bookmark main
```

`scripts/check/check-cache-v2-stage-gate.shs` composes the existing
`check-no-conflict-tree-push`, `check-no-conflict-markers-push`, and
`check-tree-size-push` guards, then adds `check-bootstrap-essential-tools-smoke`
— the gate that makes this a *stage* gate rather than a repo-integrity gate. A
tree can be structurally perfect and still leave `main` unbootstrappable.

Contract: verdict is always the last line of stdout. `PASS` (exit 0) states how
many gates ran and how many commits were checked; `FAIL` (exit 1) and `ERROR —
nothing was checked` (exit 2) both mean do not push. There is no flag or env var
that skips a gate. Verified fail-closed on 2026-08-09 from a non-repo cwd, on a
bare revision, and on an empty range — all exit 2.

Anti-clobber rules from `.claude/rules/vcs.md` still apply in full, and matter
more here because stages land from separate worktrees: rebase onto
`main@origin` before snapshotting, commit only paths this stage authored, and
never whole-WC-commit a stale tree.

### Coordination rules

1. C0 schemas are frozen before parallel implementation starts.
2. C1 is the sole owner of `cas_store.spl`.
3. C3 accesses CAS only through the C1 storage API.
4. C4 and C5 emit manifests; C8 is the sole owner of query/action-key wiring.
5. C6 owns generated formal artifacts and manual cache-protocol proofs.
6. C7 owns tests but never production fixes.
7. C9 is the sole owner of remote-main write credentials and workflows.
8. Each agent supplies an invalidation table and `cache explain` evidence.
9. No agent declares cache correctness from hit-rate tests alone.
10. C11 alone declares the feature release-ready.

---

## 4. Migration sequence

| Phase | Content | Exit condition |
|---|---|---|
| **0** Observability + schema | Land C0 schema and generator. Record current cache size, build times, file reads, MIR cache usage, invalidation breadth. Add `cache explain` with no reuse change. Extend Lean identity model compute-only. | Baseline telemetry recorded; explain output non-empty |
| **1** Local/machine CAS, bounded | Wire CAS into immutable action/result paths. Add metadata, watermarks, leases, GC **before** enabling broad writes. Legacy cache stays authoritative; shadow-compare. | Strict hash parity; corruption becomes a miss |
| **2** Workspace semantic query | Persist declaration/function query records. Store immutable results in machine CAS. Query graph stays workspace-local. Retire ad hoc filename-sanitized MIR cache paths. | Equivalence tests green against legacy MIR cache |
| **3** Remote-main read-only | Deploy remote CAS/action backend. Developer and branch builds read main only. Verify all blobs and manifests. | Hit/miss and non-hermetic-key diagnostics collected; zero remote writes from local machines |
| **4** Trusted main publication | Enable main CI receipts and protected writer. Detect action-mapping conflicts. Pin current bootstrap/release roots. Branch cache disabled. | No unresolved mapping conflicts over a full release cycle |
| **5** Optional branch namespace | Trusted branch CI namespace with TTL/quota. Post-merge ancestry promotion. Rebuild-on-main stays default. | Merge, rebase, squash, cherry-pick, force-push, deleted-branch cases all tested |
| **6** AOP group cache | Shadow precise group invalidation against conservative whole-scope invalidation. Public scoped groups first; legacy unpublicized stays conservative; mission-critical rejects unpublicized cross-scope. | Identical selected target/advice sets over the mutation matrix |
| **7** Block-level cache | Start with dataflow transfer results and diagnostics on selected large/expensive functions. Shadow every reuse against full-function analysis. Add region reuse. Defer block codegen. | Incremental fixed point == full fixed point on the whole corpus |
| **8** Bootstrap + release default | Componentized bootstrap reads from trusted main. Dev uses local/machine/remote-read. Release does strict verification, proofs, provenance, clean/cached equality. Legacy path-keyed cache loses authority. | C11 certification signed |

---

## 5. First integrated milestone (build only this first)

1. One cache-protocol SDN schema.
2. Generated Simple and Lean identity definitions.
3. Existing CAS wired as workspace/machine storage.
4. Exact action/result manifest closure.
5. High/low/hard limits, leases, and mark/sweep GC.
6. Remote-main **read-only** lookup.
7. Promotion receipt model with writes still **disabled**.
8. AOP surface, candidate, selection, and advice-implementation group digests.
9. One block-level dataflow cache with whole-function fallback.
10. Lean proofs for: cache identity, GC root preservation, symbolic advice-body separation, block transfer reuse.
11. Strict shadow comparison against clean recomputation.

Remote-main writes, branch promotion, broader AOP group reuse, and additional
block-level passes stay disabled until this slice shows **zero** semantic
divergence.

---

## 6. Risk register

| Risk | Mitigation |
|---|---|
| Cache poisoning via untrusted action mapping | Trusted-writer-only main namespace + signed receipts; CAS bytes accepted only after digest verification |
| Silent nondeterminism in compiler actions | Same-`ActionDigest`/different-result conflict → quarantine both + strict recompute; release fails |
| GC deletes a live artifact | Leases + mark-and-sweep from roots; refcounts are an optimization only; trash grace period |
| Cache fills the disk | High/low watermarks with hysteresis, hard limit, free-space reserve; write rejection never fails the build |
| Block identity churn on unrelated edits | Semantic anchors + roles, never lines/indexes; ambiguous match → whole-function fallback |
| Broad root pointcut causes global reweave | Publicized scoped contracts; whole-root candidate index enters the key so the cost is explicit, not hidden |
| Proving one model while executing another | Shared SDN generation, cross-language golden vectors, regeneration diff gate, executable trace checker |
| Formal gate weakened over time | `sorry`/`admit`/unapproved-axiom scan in CI; field-count == theorem-count coverage gate |
