# TLDR — Startup Perf Parallel Agent Plan (2026-08-17)

Wave 0 contracts freeze, then Wave 1 implementation in parallel; one file
owner per WP; done-marks accepted only by a higher-model reviewer.

```text
Wave 0 (contracts, gate before any impl)
  WP-00s census -> WP-01s component contract -> WP-02s startup/plan contract
                                             -> WP-08s CLI option contract
        | contract-integrator gate |
Wave 1 (parallel)
  WP-A load_policy      WP-11s classifier    WP-12s SCI generator
  WP-13s SCI reader     WP-14s static table  WP-15s planner
  WP-19s option-route SECTION (sole owner of composition codec files)
  WP-19a-s option router  WP-19b-s extension wire  WP-19c-s help gen
  WP-55s optimizer dynload            WP-E deps metrics baseline
        -> single integration owner cuts over _CliMain / dispatch table
```

- Do-not-touch: `src/app/cli/_CliMain/*`, `dispatch/table.spl`,
  `composition/{codec,cli_registry,cli_*_wire}.spl` (WP-19s only),
  `launch_metadata.spl` (WP-A only).
- Every WP: sabotage probe required; exit-0-without-`Results:` = rejected;
  record baseline SHA + binary digest.
- Brief + handoff templates copied from research §14.10/§14.11 (in full doc).
- Review gate: implementer claims, higher-model reviewer re-runs tests +
  sabotage + diff-vs-owned-paths, and alone flips the status table.
- Full doc: `startup_perf_parallel_plan_2026-08-17.md`.
