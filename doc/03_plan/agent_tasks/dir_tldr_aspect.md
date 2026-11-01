# dir_tldr_aspect: Agent Task Breakdown (DRAFT)

Pending requirement selection. Lane scope shrinks or grows with the chosen options.

| Lane | Model | Scope | Depends |
|---|---|---|---|
| L0 interface freeze | Opus (best model) | trait and struct names (`Aspect`, `PointcutPred`, `Placement`, `TraversalPlugin`, `DirTldrView`, `PluginInstanceKeyV1`), spec step helpers, fail-fast placeholders | selection |
| L1 contract | Opus | `package_init_tld_v1.spl` fields, or the A2 attachment; unit specs | L0 |
| L2 producer + gate | Opus | `dir_tldr_producer_v1`, `dir_tldr_gate_v1`, single flight, atomic publish | L1 |
| L3 aspect model + traversal | Opus | `aspect_object_model_v1`, `traversal_plugin_v1`; port LogAspect | L0 |
| L4 plugin registry/reuse | Opus | instance key and allowlist in `AopMatchDriverStateV1` | L3 |
| L5 scheduler policy | Opus | `dir_job_policy_v1`, `native_file_worker_v1` integration | L2 |
| R* build/test runner | Haiku | stage2 parse check, unit and system specs, timed first-`.o`, RSS sampling; reports only, never edits | each lane |
| V review | Opus 5.5 (higher model than implementers' sidecars) | per-lane diff review, zero P0/P1; multithread findings → Opus root cause + stress spec | each lane |

- **Merge owner:** the orchestrating Opus session for `dir_tldr_aspect` (one PR per lane into `release/1.0.0`).
- **Final reviewer:** Opus 5.5 at the highest effort (or Fable when available). Reviews verify PASS before release.
- Rules: no commits in `C:/dev/simple`; worktrees under `C:/dev/wt/`; never touch phase3 or P3-RUN; kill by PID only.
