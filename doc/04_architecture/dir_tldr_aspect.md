# dir_tldr_aspect: Architecture (DRAFT)

**DRAFT: pending requirement selection** (`doc/02_requirements/feature/dir_tldr_aspect_options.md`).
This draft assumes the recommended-for-discussion set A1 B3 C1 D1 E1 F1 G1 H1-H5 and is revised after selection.

## MDSOC capsules (dimension = concern; owners are existing modules where possible)

| Capsule | Layer | Owner (existing → extension) | Responsibility |
|---|---|---|---|
| `dir_tldr.contract` | 00.common/cache_contract | `package_init_tld_v1.spl` (+fields) | Wire, validation, identity key |
| `dir_tldr.producer` | 80.driver/cache | new `dir_tldr_producer_v1.spl`, using `aop_directory_facts_from_hir_v1` and `tldr_summary_v1` | Build a dir TLDR from member file TLDRs plus join-point facts |
| `dir_tldr.gate` | 80.driver | new `dir_tldr_gate_v1.spl` | Fail-closed "check first" before any member source compile |
| `aspect.model` | 35.semantics | new `aspect_object_model_v1.spl` (traits `Aspect`, `PointcutPred`, `Advice`, `Placement`) | OOP authoring; lowers to `PointcutSelectorV1` |
| `aspect.traversal` | 35.semantics | new `traversal_plugin_v1.spl` (trait `TraversalPlugin`) | Pure `visit(DirTldrView, selector) -> WeavePlanDeltaV1` |
| `aspect.placement` | 35.semantics / 50.mir | `aspect_weave.spl`, `mir_aop_injection.spl` (unchanged weavers) | Apply the plan through the existing inject_* forms |
| `aspect.plugin_registry` | 80.driver/cache | extends `AopMatchDriverStateV1` | Instance key, normalised config, single shared instance, admission allowlist |
| `sched.dir_policy` | app/build/scheduler | `planner.spl` plus new `dir_job_policy_v1.spl`; `native_file_worker_v1.spl` | One job per dir, split threshold, smallest-first ordering |

## Data flow

```
scan dirs ─▶ sched.dir_policy ──(job = dir or dir-chunk)──▶ worker process
                                             │
                     dir_tldr.gate: load __init__.tld ─ valid? ─no─▶ dir_tldr.producer (single-flight, atomic publish)
                                             │yes (resident, read-only snapshot)
              per file: parse → HIR ─▶ aspect.plugin_registry.instance(key) ─▶ TraversalPlugin.visit(dir view, selector)
                                             │ WeavePlanDeltaV1 (keyed by pointcut_match_key_v1, dir-scoped)
                          aop_weave (HIR forward) ─▶ MIR inject_* ─▶ obj
```

Each file still runs parse→HIR→MIR→obj in one process. The dir job holds only the
read-only dir TLDR plus the plugin instances. HIR stays target-neutral, and
guard roots are part of the facts key.

## Key invariants
1. No source compile in dir D is admitted unless D's dir TLDR is valid for the current membership, guard root, ancestor aspect root, and compiler id. Otherwise the job rebuilds it. If the rebuild fails, the compile takes the legacy full-visit path.
2. Plugin *instances* are shared by `digest(code, normalised_config)`. *Results* are never shared across dirs (only G3 would relax this).
3. All new code: SDN manifests, no nil or Any outside unsafe, stage2-parseable syntax only (no new grammar). Any incompatibility gets a tagged workaround `# WA(stage2-dir-tldr): …`.

## Open questions (resolved by the selection)
A1 vs A2 wire placement; F2 synthetic module identity; D-T threshold formula; G3 proof obligation.
