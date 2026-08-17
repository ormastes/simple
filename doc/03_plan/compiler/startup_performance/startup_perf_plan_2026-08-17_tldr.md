# TLDR — Startup Perf Implementation Plan (2026-08-17)

Five phases; each has owned files, `Results:`-line acceptance (exit 0 is
never a pass), a T0-first verification tier, and a rollback.

```text
E baseline (deps metrics)
   -> A load_policy enum replaces public mmap policy (mmap = provider
      strategy; mmap_hint/include_mmap_cache stay as decode aliases)
   -> B presence/placement/activation axes in SCI/SDN config;
      resolve_component; optimizer/loader/aspect dynload;
      auto fold static on full rebuild, dynamic stays external
   -> C CLI options as SCI data: option-route section, --x<ns>-<key>=<val>
      grammar, SimpleCliExtensionV1 wire; config edit = 0 compile, 0 link,
      core digest unchanged
   -> D profile-first optimization: loader segments, interpreter dispatch,
      wire interface_digest_of into cache keys; >=5-sample p50/p95 reports
   -> E re-measure per phase (bin/simple deps fast/normal closure metrics)
```

- Tiers: T0 probe -> T1 subtree specs -> T2 full test -> T3 bootstrap only
  for claims ABOUT rebuild (B fold, D compiler lanes). Never default to T3.
- Sabotage per phase: bad digest must fail closed, never silent fallback.
- One owner for composition codec + launch_metadata; `_CliMain` untouched
  until integration cutover.
- Full plan: `startup_perf_plan_2026-08-17.md`; agent split:
  `doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md`.
