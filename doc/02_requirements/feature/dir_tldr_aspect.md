# dir_tldr_aspect: Feature Requirements (FINAL)

**Status: SELECTED by the user (2026-11-02).** Selection: A1, B3, C1, D1 + D-T3, E1, F1, G1, H1-H5.
Unchosen options were deleted from `dir_tldr_aspect_options.md`.
Implementation is deferred (non-essential): each requirement has only a fail-fast spec and a TODO row.
Plan: `doc/03_plan/sys_test/dir_tldr_aspect.md`. NFRs: `doc/02_requirements/nfr/dir_tldr_aspect.md`.

| REQ | Selected option | Requirement | TODO | Spec |
|---|---|---|---|---|
| REQ-DTA-A1 | A1 | Extend `PackageInitTldV1` (`__init__.tld`) with `file_tldr_root_digest` (Merkle root of member file TLDR digests) and `join_point_facts_digest` (`directory_facts_key_v1`). Identity = (scope path, parent_scope_digest, membership_root, compiler/provider id, guard root). The wire must stay parseable by stage2. | 418 | `dir_tldr_aspect_a1_contract_spec.spl` |
| REQ-DTA-B3 | B3 | The dir TLDR stores roots (digests) of file TLDRs, generic-TLDR views and macro RR families, plus an inline join-point fact table as the only inlined data. | 419 | `dir_tldr_aspect_b3_join_point_facts_spec.spl` |
| REQ-DTA-C1 | C1 | Early-cutoff recompute: rebuild the dir TLDR when a member TLDR digest, membership, guard root or ancestor aspect root changes; propagate to children only when the output digest changes (uses `OldNewMembershipV1`). | 420 | `dir_tldr_aspect_c1_invalidation_spec.spl` |
| REQ-DTA-D1 | D1 | One job per dir with the dir TLDR resident. If `dir_count < split_threshold`, split large dirs into chunks of at least K files sharing a read-only dir TLDR snapshot. Threshold = `min(jobs, mem_budget / per_job_rss_est)`, jobs = 80. | 421 | `dir_tldr_aspect_d1_scheduler_spec.spl` |
| REQ-DTA-D-T3 | D-T3 | The threshold is cost-estimated (file bytes x history) with a target per-job wall of at most 10 s for the first object. First `.o` rule: the first job's dir TLDR check finishes within a 2 s budget and the smallest ready dir is scheduled first. | 421 | `dir_tldr_aspect_d1_scheduler_spec.spl` |
| REQ-DTA-E1 | E1 | Traits `Aspect`, `Pointcut`, `Advice`, `Placement`; classes implement them (as `LogAspect`). A pointcut predicate object compiles to the existing `PointcutSelectorV1` node array. | 422 | `dir_tldr_aspect_e1_aspect_model_spec.spl` |
| REQ-DTA-F1 | F1 | `TraversalPlugin` trait: `fn visit(dir: DirTldrView, sel: PointcutSelectorV1) -> WeavePlanDeltaV1`, pure and deterministic. Placement goes through a closed `Placement` enum (before / after_success / after_error / around / at_instruction) mapped to the existing inject_* functions. | 423 | `dir_tldr_aspect_f1_traversal_plugin_spec.spl` |
| REQ-DTA-G1 | G1 | Plugin instance key = digest(plugin code digest, normalised config with dir path and matcher removed). One shared instance; per-dir results stay keyed by `pointcut_match_key_v1`. Plugins declare which config fields are scope fields. | 424 | `dir_tldr_aspect_g1_plugin_identity_spec.spl` |
| REQ-DTA-H1 | H1 | Fail closed when the dir TLDR is stale, missing or invalid: refuse to admit the source compile, rebuild, and on failure fall back to the full visit; never use a stale result. | 425 | `dir_tldr_aspect_h1_fail_closed_gate_spec.spl` |
| REQ-DTA-H2 | H2 | Determinism: sorted members, no timestamps, guard root in key; two runs produce byte-identical woven output. | 426 | `dir_tldr_aspect_h2_determinism_spec.spl` |
| REQ-DTA-H3 | H3 | Concurrency: dir TLDR production is single flight (`CacheSingleFlightV1`), readers pin an immutable generation, publish is atomic via temp file + rename. | 427 | `dir_tldr_aspect_h3_concurrency_spec.spl` |
| REQ-DTA-H4 | H4 | Corruption: framed digest check on every read (three-payload envelope); on mismatch, quarantine and rebuild. | 428 | `dir_tldr_aspect_h4_corruption_spec.spl` |
| REQ-DTA-H5 | H5 | Plugin loading security: load only admitted plugins whose code digest is pinned in an SDN allowlist; no network; reject unsigned dynload. | 429 | `dir_tldr_aspect_h5_plugin_allowlist_spec.spl` |

Umbrella end-to-end skeleton (T1-T12): `test/03_system/app/compiler/feature/dir_tldr_aspect_spec.spl`.
