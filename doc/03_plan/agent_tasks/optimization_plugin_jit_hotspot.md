<!-- codex-design -->
# Optimization Plugin JIT Hotspot Tasks

Status: **Phase 2 implementation complete; verification in progress** (updated 2026-05-29)

## Phase 1 — Done

- Research existing optimization plugin and JIT docs.
- Add local/domain research artifacts.
- Add feature/NFR requirements.
- Add architecture/detail design.
- Extend provider schema with `JitHotspot`.
- Add built-in JIT hotspot provider helper and runtime-hotspot predicate.
- Add unit coverage for required runtime facts and safe-deopt gating.
- Update guide, architecture, and spec docs.
- Connect tiered JIT profile counts to `profile.hot_count` facts.
- Add data-only hotspot plan and invalidation helpers.
- Add unit coverage for hotspot fact extraction, eligibility, and invalidation.
- Add representative hotspot planning benchmark and first measured evidence report.
- Add a tiered JIT compile-decision consumer for eligible hotspot plans.
- Add opt-in hotspot specialization providers that can replace compile source only with semantic proof.

## Phase 1b — Predicate-Policy Merge (2026-05-29)

Merged 19 commits from predicate-policy worktree:

- Backend-gated strength reduction and predicate promotion recommendations.
- Hotspot fact derivation: strength reduction, byte scan, checksum, scalar
  cleanup, LICM, loop unroll, predication, vectorization, range, hot call inline.
- Centralized hotspot optimization plan assembly.
- MIR pass routing through backend planner.
- Escape analysis gating for var optimizer plugins.
- SSA var canon with reassignment facts.

Related bugs closed:
- `jit_hotspot_optimization_plan_interpreter_cost_2026-05-28` — Fixed
- `jit_hotspot_shared_policy_plan_cost_2026-05-28` — Fixed

## Phase 2 — Remaining

- Add native backend specialization benchmarks after a concrete JIT hotspot
  provider consumes `JitHotspotPlan`.

### Phase 2 Progress — Analysis-Derived Proof (2026-05-29)

- Added `jit_hotspot_analysis_has_semantic_proof` so the hotspot layer can
  derive the provider proof bit from analyzer facts instead of accepting only a
  caller-supplied boolean.
- Added `jit_hotspot_specialization_provider_from_analysis`, which creates a
  specialization provider only when the analysis facts include `typed_mir`,
  `safe_deopt`, `ssa.var_transform`, `escape.analyzed`, `escape.no_escape`, and
  `borrow.reassign_safe`.
- Added focused spec coverage for accepting complete analysis proof facts and
  rejecting incomplete proof facts.
- Connected profile-level analysis facts to specialization providers through
  `jit_hotspot_specialization_provider_from_profile_analysis`.
- Updated the tier-1 `record_call` consumer so stored specialized source can
  use analysis-derived proof facts when no manual proof bit was supplied.

### Phase 2 Progress — MIR Analysis Provider (2026-05-29)

- Added `var_reassign_analysis_hotspot_facts` to merge analyzer-derived
  `ssa.var_transform`, `escape.*`, and `borrow.reassign_safe` facts with base
  hotspot facts.
- Added `jit_hotspot_specialization_provider_from_var_reassign_analysis`, a
  concrete MIR var-reassignment analysis provider factory. It runs the SSA var
  transform first and only exposes a non-empty specialized source when the
  transformed MIR proves the full semantic-proof fact set.
- Split SSA transform and pseudo-phi materialization into
  `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl` so the analysis module
  stays below the 800-line maintainability gate.
- Added unit coverage in `test/unit/compiler/mir_opt/var_reassign_analysis_spec.spl`
  for proof-fact construction, provider acceptance, and unsafe-transform
  rejection.
- Updated the system spec to cover MIR analysis-backed specialization provider
  consumption and current pseudo-phi materialization behavior.

Focused evidence:

```bash
bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean --progress none
# PASS: 51 tests, 0 leftover matching test processes

bin/simple test test/unit/compiler/mir_opt/var_reassign_analysis_spec.spl --mode=interpreter --progress none
# PASS: 17 tests

bin/simple test test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl --mode=interpreter --progress none
# PASS: 9 tests

bin/simple run test/perf/compiler/jit_hotspot_plan_bench.spl --mode=interpreter
# PASS: checksum-bearing benchmark rows recorded in doc/09_report/verify/optimization_plugin_jit_hotspot_perf_evidence_2026-05-24.md

bin/simple check src/compiler --progress none
# PASS: status 0, 2 existing warnings across 2591 files

bin/simple check src/lib --progress none
# PASS: status 0, 299 existing warnings across 5790 files

bin/simple check src/app/mcp --progress none
# PASS: status 0

bin/simple check src/app/simple_lsp_mcp --progress none
# PASS: status 0

SIMPLE_LIB=src bin/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --progress none
# PASS: status 0, 3 tests

src/compiler_rust/target/debug/simple test test/unit/compiler/mir_opt/var_reassign_analysis_spec.spl --mode=interpreter --progress none
# PASS: 17 tests

src/compiler_rust/target/debug/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean --progress none
# PASS: 51 tests, 0 leftover matching test processes

src/compiler_rust/target/debug/simple test test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl --mode=interpreter --progress none
# PASS: 9 tests

src/compiler_rust/target/debug/simple run test/perf/compiler/jit_hotspot_plan_bench.spl --mode=interpreter
# PASS: checksum-bearing benchmark rows recorded in doc/09_report/verify/optimization_plugin_jit_hotspot_perf_evidence_2026-05-24.md
```

### Verification Blocker — 2026-05-29

Focused verification could not safely run on this host. Running hotspot-related
Simple tests exposed a runaway process storm:

- `bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean`
  failed with `Resource temporarily unavailable (os error 11)` after the host
  was already overloaded.
- A prior `general_patterns_backend_recommendation_spec.spl` run had spawned
  thousands of nested `bin/simple test` processes.
- Concurrent `web_baremetal_size_audit` native-build chains and
  `heavy_work_preflight_spec.spl` also recursively spawned `simple` processes.
- `.git/index.lock` was left behind by a stuck
  `scripts/check-workspace-root-guard.shs audit --staged` / `git check-ignore`
  process and had to be removed after the owning process was stopped.

Concrete bug record:
`doc/08_tracking/bug/jit_hotspot_verification_process_storm_2026-05-29.md`.

The source-level test recursion guard has bounded the hotspot spec under both
the Rust runtime and refreshed local `bin/simple` artifact with `--clean`.
The stale pre-refresh `bin/simple` artifact reproduced the process storm before
the process group was stopped; the refreshed artifact now leaves zero matching
test processes after the hotspot spec.
