# Semantic Build Cache (v2) — developer guide

**Read this first: none of what follows is wired into your build yet.**

For the caches and SCV source admission that *are* live today, see
[simple_cache_scv.md](simple_cache_scv.md).

As of 2026-08-10 the semantic build cache v2 modules exist, are tested, and are
formally modelled. The legacy cache (`.build_cache.sdn` plus `.build/mir_cache/`)
still makes **every** build decision. The one v2 code path a normal build can
reach is **shadow mode** — opt-in via `SIMPLE_CACHE_V2_SHADOW=1`, which runs v2
lookup/publish/byte-compare alongside the legacy path in the incremental driver
and prints one summary line (hits/misses/mismatches/errors). Shadow mode never
changes build output; a v2 failure is counted, never propagated.

This guide documents what is in the tree and what is deliberately not, so you can
tell the difference. It will grow a "how to use it" section when there is one.

---

## What exists today

| Capability | State | Reachable from `bin/simple`? |
|---|---|---|
| SHA-256 action identity + CAS | implemented, tested | **No** — zero callers |
| L1 workspace / L2 machine tier router | implemented, tested | **No** |
| Storage watermarks, leases, GC | implemented, tested | **No** |
| Remote-main lookup | read-only stub, no transport | **No** |
| Remote-main writes | **deliberately disabled** | **No — and must stay that way** |
| Shadow mode (v2 alongside legacy, compare-only) | implemented, opt-in env | **Yes** — `SIMPLE_CACHE_V2_SHADOW=1`; recompiled modules only; coarse key (see gaps) |
| Block dependency cache (C5 slice 1) | keys + worklist + manifests, in-memory | **No** — consumed by nothing yet |
| CI promotion gateway (C9 slice 1) | local validator + main-only workflow | CI-only; no remote write step exists |
| AOP invalidation groups | implemented, mostly conservative | **No** |
| `CompileInterfaceDigest` | compute-and-log | **No** |
| Lean proofs of the identity model | 74 theorems, green | Yes — via the gate script |
| `simple cache …` CLI | **not implemented** | **No** |

The CLI surface described in the design doc (`simple cache status/explain/gc/…`)
is a specification, not a shipped feature. Do not cite it in other docs as though
it works.

## What you can actually run

The formal gate is the one thing here that is genuinely runnable and meaningful:

```bash
sh scripts/check/check-cache-protocol-formal.shs
```

Verdict is the **last line** of stdout and the exit code is authoritative:

| verdict | exit | meaning |
|---|---|---|
| `PASS — …` | 0 | proofs built, no trust bypass, coverage complete, regeneration clean |
| `FAIL — …` | 1 | a proof, coverage, or regeneration check failed |
| `ERROR — nothing was checked` | 2 | could not find the project; **not** a pass |

Capture the exit code directly — `… | tail -1; echo $?` gives you `tail`'s status,
not the guard's.

The unit specs:

```bash
bin/simple test test/01_unit/compiler/cache_v2/tier_router_spec.spl   # 6
bin/simple test test/01_unit/compiler/cache_v2/gc_spec.spl            # 8
bin/simple test test/01_unit/compiler/cache_v2/aop_group_spec.spl     # 12
bin/simple test test/01_unit/compiler/cache_v2/promotion_spec.spl     # 33
bin/simple test test/01_unit/compiler/interface_compat/compile_interface_spec.spl  # 7
```

Trust only the `SPEC FILE VERDICT … executed=N` line with N > 0. `simple test`
given an **absolute** path runs nothing and still exits 0.

## Things you need to know before touching this

**The cache decides what may be reused instead of recomputed.** A false hit is a
silent miscompilation — wrong bytes served with confidence. A false miss just
costs time. Every ambiguity resolves toward recomputation, and that asymmetry is
why several parts here deliberately over-invalidate.

**Exact-key lookup only.** If you are ever tempted to add a "close enough"
fallback so more things hit, don't. That is a correctness bug wearing a
performance costume.

**Your branch does not affect cache identity.** Branch, commit, and CI run are
recorded as *provenance* for deciding what may be published, never as part of the
key. Two identical builds on different branches are supposed to share results.

**You cannot publish to the shared main cache from your machine.** That is
enforced structurally, not by configuration, and there is intentionally no flag
to override it.

## Known gaps (do not rediscover these)

Full list: `doc/08_tracking/bug/cache_v2_first_milestone_known_gaps_2026-08-10.md`.
The ones most likely to bite:

- **All verification used the Rust seed binary**, not the self-hosted compiler.
  GREEN here does not prove self-hosted correctness.
- `CompileInterfaceDigest` is missing generic constraints, effects, and parameter
  passing modes, because `ApiSurface` does not carry them. A generic-bound change
  may not move the digest — that is an under-invalidation risk, and the reason it
  drives no decisions.
- The `abi`/`semantic`/`link` digests are placeholder re-hashes. They mean nothing.
- Free-space admission is scoped to the cache's own byte budget; it cannot see
  that the *disk* is filling from some other cause.
- **The SMF header is not wire-identical between the Simple and Rust
  implementations** (96 B padded vs 128 B packed, fields shifted by 4 from offset
  20 onward). See
  `doc/08_tracking/bug/smf_header_wire_layout_diverges_rust_vs_simple_2026-08-10.md`
  before touching any SMF layout. Do not change either side unilaterally.

## Where the real documentation lives

- Design (normative): `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md`
- Waves and ownership: `doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md`
- Frozen field contract: `doc/03_plan/compiler/cache/c0_schema_freeze_2026-08-09.md`
- Agent/LLM notes: `doc/00_llm_process/feature_expert/cache_tiering/skill.md`,
  `doc/00_llm_process/layer_expert/driver_cache/skill.md`

<!-- wave-f-perf-analysis-collection-refactoring-2026-11-19 -->

## Performance Summary Cache Identity, Dynamic Implementation Changes, and Unknown Handling (2026-11-18)

Canonical plan: [Simple Performance Analysis and Collection Refactoring](../../03_plan/compiler/performance_analysis_and_collection_refactoring_2026-11-18.md) (§12, §13.3, §16.2; contracts in `src/compiler/35.semantics/perf/perf_analysis_contracts_v1.spl` and `src/compiler/35.semantics/perf_facts/registry.spl`).

### `PerfCacheKeyV1` Identity for Cost Summaries and Refactoring Proofs

Cached `FunctionCostSummaryV1` records and `LoopIdiomCandidateV1` safety proofs are keyed by every semantic input that can alter resource bounds or rewrite legality — never by function name, file mtime, or ABI signature alone (§12.1):

1. `function_semantic_revision` — canonical digest of the function's typed HIR body and local bindings.
2. `type_and_representation_instantiation` — concrete generic/monomorphized element, key, equality, and hash representations.
3. `relevant_callee_summary_hashes` — exported cost/effect summary digests of resolved callees (`dependency_summary_hashes`; insignificant formatting edits in a callee that preserve its summary do not cascade-invalidate callers, whereas an effect or bound change invalidates both caller bounds and caller `VerifiedSafe` fix proofs, `I02`, `I04`).
4. `library_implementation_identity` (`implementation_digest`) — identity of the analyzed library/plugin implementation or verified interface contract.
5. `analyzer_and_model_versions` — `analyzer_version` + `model_version` (`CollectionOperationRegistry.metadata_version`).
6. `language_effect_numeric_policy` — active `nogc`, checked-overflow, floating-point, and strict-contract policy digest.
7. `target_configuration_if_relevant` — target/backend dimensions when backend-refined cost models are queried.
8. `analysis_profile_and_precision` — tier (`T1`..`T3`) and budget configuration (`configuration_fingerprint`).

### Static Linking, Dynamic Plugins, SFFI, and Fail-Closed Metadata (`I03`, `I08`)

- **Static and closed target sets:** Known static callees substitute their exact summary; closed finite dispatch sets combine all feasible targets conservatively while retaining assumptions.
- **Open dispatch, SFFI, and dynamic plugin replacement (`I03`):** Open trait/interface dispatch uses an enforced interface contract or emits an explicit `UnknownTerm`. Unmodeled SFFI/native calls keep cost and effects `Unknown`. Replacing a dynamic plugin or shared module with an ABI-compatible implementation that has a different `implementation_digest` (for example, changing an `O(1)` lookup to an `O(n)` scan) invalidates implementation-specific cost and safety summaries; cost-contract load rejection occurs only when an explicit verified-resource profile is enabled (§12.4).
- **Bounded versioned metadata and non-poisoning timeouts (`I06`, `I08`):** Library cost registries (`collection_registry_parse` in `src/compiler/35.semantics/perf_facts/registry.spl`) enforce size/depth caps, schema/version checks, and duplicate-key rejection. Malformed or unsupported model versions downgrade cleanly to `Unknown` (`PERF-ANALYSIS-001`) without crashing compilation or silently trusting unverified claims. Budget-exhausted or cancelled `T2`/`T3` runs record `Partial`/`Cancelled` status without permanently poisoning subsequent higher-budget runs, and file-based build caching remains the normal compiler scheduling boundary (§13.3).
