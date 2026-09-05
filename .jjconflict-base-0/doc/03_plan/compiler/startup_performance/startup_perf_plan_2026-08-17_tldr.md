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

## Status 2026-08-18
- A DONE (`e5b58f7efc3`, `63f19a30473`). B mostly DONE via dynsmf axes
  (`a663c1145b1`, `281d8adde3b`, optimizer fail-closed `25a48297651`);
  fold-static bootstrap proof + component-descriptor contract NOT-STARTED.
- C core DONE (`131721fb924`, `0927c2e6ec7`); help/completion gen REMAINING.
- D largely DONE (lazy JIT `9840ded67e5`, interp hot path `d0dbcccb116`,
  loader/interp splits, sleep/timers, lint/parse root causes);
  `interface_digest_of` wiring + `test/05_perf/startup/` NOT-STARTED;
  seed env-cache / parser hops / ExecIR / segment loader IN-FLIGHT.
- E DONE for baseline (`src/app/deps/`, SCC 36->13, backend 45->8);
  per-phase re-measure spec REMAINING.
- Biggest remaining: self-hosted deploy as default tooling (bin/simple is
  still the Rust seed). Full table: plan doc "Status 2026-08-18".
