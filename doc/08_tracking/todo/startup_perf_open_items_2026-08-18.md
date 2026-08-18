# Startup-perf campaign — genuinely-open items (2026-08-18)

Combined tracking doc for the open tail of the 2026-08-17/18 startup-perf
campaign. Plan: `doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md`.
Closed items (interface_digest wiring `1310d879046`, seed env-cache, ExecIR
tier-0.5/arena) live in the plan, not here.

## Open items

1. **Perf-harness lanes** — `test/05_perf/startup/` is seeded
   (`budgets.sdn`, `hello_fixture.spl`, `README.md`) but per-lane
   >=5-sample p50/p95 admission reports are not institutionalized.
   Unblock: none — needs a runner spec that records samples into
   `doc/10_metrics/startup/` and gates on `budgets.sdn` bands.

2. **Phase E growth-band spec** — coupling/cohesion snapshots are a single
   baseline (`doc/10_metrics/startup/coupling_cohesion_baseline_2026-08-17.md`),
   not a bracketing before/after series with an allowed growth band.
   Unblock: define band in a spec consumed by the `deps` command output.

3. **Self-hosted deploy as default `bin/simple`** — still the Rust seed;
   CLAUDE.md default-tooling rule unmet. Blocked on bootstrap succeeding:
   stage-1/stage-3 unbounded-RSS blowup (immortal alloc after parse), see
   commit `66125e94a6b` and its bug doc. Unblock: fix the immortal-alloc
   retention, re-run `bin/simple build bootstrap`, redeploy symlink.

4. **Phase B fold-on-full-rebuild proof** — constant-fold behavior proven
   only on incremental paths; needs a full-rebuild bootstrap run showing
   the fold survives, plus the component-descriptor contract as specced
   (or a plan amendment blessing the dynsmf-path shape). Unblock: a
   successful bootstrap (same blocker as item 3).

5. **Phase C option migration report** — help/completion generation and the
   hardcoded-option migration report not produced. Unblock: none —
   enumerate remaining hardcoded options in `src/app/cli` dispatch and
   emit the report under `doc/09_report/`.
