# Feature: perf-opt-lang-web-db-os

## Raw Request
> after task done check api interface or arch are changed. you must not hurt it
> for perf. minimize or eliminate rt uses in app developer view. perf opt on
> language, web server, db, os on x86 and optimize all without break api or arch.
> find check lists. and compare and make sspec system tests which make benchmark
> docs. however lang should compare script, compiler separately. in db, separate
> ram only and others. improve simple interpreter/compiler first than try each app
> if it does not solve. check interpreter does it make smf in backgound idle and
> load it even it is not called and save load the cache smf rather parse again if
> script not changed.

### Clarifications (dev phase)
- **Deliverable:** Full cycle, but **detailed plan + docs FIRST**, then phased
  implementation; one umbrella goal that is only complete when every sub-goal is.
- **SMF idle/cache question:** Investigate current behavior first, then **build
  where missing** (idle background SMF compile + unchanged-script cache reuse).
- **Target:** **x86_64 first**, but make the architecture extendable for arm and
  riscv 64/32 later; benchmark sspec tests must be **reusable via arch tags**, not
  copied per arch.

## Task Type
code-quality
<!-- Primary intent = performance optimization under a hard "no public API / no
architecture change" constraint. Contains feature-shaped sub-work (benchmark
sspec harness, idle/cache SMF if missing) tracked inside the same umbrella. -->

## Refined Goal
Improve x86_64 runtime performance of the Simple interpreter/compiler, web server,
database, and SimpleOS — driven by a detailed phased plan and reusable, arch-tagged
sspec benchmark system tests that emit benchmark docs — while changing **no** public
API or architecture and reducing app-developer-visible `rt_*` usage, optimizing the
shared interpreter/compiler first and per-app targets only for gaps that shared wins
do not close.

## Phasing (high level — refined in research/spec phases)
- **P0 Plan & docs (first):** plan doc + design doc + per-domain checklists + baseline
  benchmark sspec harness + API/arch guard, all reviewed before any optimization lands.
- **P1 Shared interpreter/compiler:** land + re-measure shared wins (incl. SMF
  idle/cache investigation→build).
- **P2 Per-app (web server, db, os):** only for gaps P1 did not close.
- **P3 Umbrella close:** all sub-goals done, benchmark docs show no regression, guard green.

## Acceptance Criteria
- **AC-1 (Plan & docs first):** A phased optimization **plan** (`doc/03_plan/...`) and
  **design** (`doc/05_design/...`) doc enumerate every sub-goal, ordered phases, and
  per-phase exit criteria, and are reviewed/landed **before** any optimization code.
- **AC-2 (Checklists):** A trackable, pass/fail perf checklist exists per domain —
  language-script, language-compiler, web server, db-RAM, db-persistent, os — derived
  from `doc/07_guide/compiler/check_perf.md` and existing harnesses.
- **AC-3 (Reusable arch-tagged benchmark sspec system tests):** sspec system tests
  measure each domain and **emit benchmark docs**; each spec carries an **arch tag**
  (x86_64 now; arm/riscv 64/32 pluggable) and a mode tag, and the same spec reruns
  across arch/mode via tag selection without copy-paste.
- **AC-4 (Language: script vs compiler separated):** Language benchmarks report
  interpreter (script) and compiled (SMF / native) results as **separate**,
  independently tracked numbers — never collapsed into one figure.
- **AC-5 (DB: RAM-only vs persistent separated):** Database benchmarks report
  **RAM-only** and **persistent/backed** configurations as separate result sets.
- **AC-6 (Interpreter/compiler first):** Shared interpreter+compiler optimizations are
  landed and re-measured **before** any per-app (web/db/os) optimization; per-app work
  is undertaken only for gaps the shared wins did not close, and that ordering is recorded.
- **AC-7 (SMF idle background compile + unchanged-script cache reuse):** It is
  documented whether the interpreter (a) background-compiles SMF when idle and (b)
  reuses cached SMF for an unchanged script instead of re-parsing; where missing it is
  implemented so an unchanged script (content-hash match) loads cached SMF and idle
  background compile occurs — proven by a semantic-invalidation/cache spec (stale source
  must miss the cache). Anchors: `src/os/smf/dynsmf_session.spl`,
  `src/app/startup/dynsmf_autoload.spl`.
- **AC-8 (No API/arch break — regression guard):** After every optimization a guard
  proves the **public API surface and architecture are unchanged** (public symbol/ABI
  diff + accessor-forwarding/cache invalidation specs + arch-doc parity). Any change
  that would require an API/arch change is blocked pending separate approval.
- **AC-9 (Minimize/eliminate `rt_*` in app-developer view):** App-developer-facing code
  shows a measured reduction (or elimination) of direct `rt_*` usage vs baseline, with
  optimizations pushed behind stdlib/public APIs; **pure-Simple first**, no Rust seed /
  C runtime edits except safety-critical process/signal guards.
- **AC-10 (Cross-mode correctness + cross-language perf):** Each optimized domain passes
  correctness in interpreter / smf / native modes and is compared vs other languages via
  `scripts/check/check-cross-language-perf.shs`; benchmark docs are (re)generated.
- **AC-11 (Umbrella completion):** The goal is complete only when every phase's exit
  criteria are met, all sub-goals are done, and the benchmark docs show **no regression**
  vs the P0 baseline.

## Scope Exclusions
- No public API or architecture changes (any required change becomes a separate, approved goal).
- No Rust seed / C runtime modifications except safety-critical process/signal guards.
- arm / riscv 64/32 **execution** is out of scope now — only arch-extensibility and
  arch-tagged reusable specs; actual non-x86 benchmark runs are follow-up goals.
- x86_32 benchmark execution is out of scope in P0/P1 (extensible, not yet executed).
- No "perf via weakened correctness" — no skipped/weakened specs, no false-green parity.

## Research Synthesis (Phase 2 — Opus review of 4 parallel Sonnet agents)
Full notes: `research/01_interpreter_compiler.md`, `research/02_smf_idle_cache.md`,
`research/03_web_db.md`, `research/04_os_harness_guard.md`.

### AC-7 verdict (the user's core question)
| Capability | Status | Evidence |
|---|---|---|
| Unchanged-script SMF cache reuse (`simple run`) | **EXISTS** | `try_load_smf_cached` + `build/smf/manifest.sdn` + `validate_smf` |
| Stale-source cache miss (user scripts) | **EXISTS** | SHA-256 + dep interface-hash in `cache_validator.spl` |
| Idle background compile — watcher daemon | **EXISTS** | `WatcherDaemon.generate_smf()` on file-change |
| Idle background compile — dynSMF precompiled lane | **PARTIAL** | command queued in evidence, **process never spawned** (`dynsmf_autoload.spl`) |
| Stale-source miss — dynSMF precompiled lane | **PARTIAL** | magic-bytes (`SMF\0`) only, no content hash (`dynsmf_session.spl:163`) |
| Specs for cache-reuse / stale-miss | **MISSING** | no spec exercises `try_load_smf_cached` |
→ **BUILD:** (1) dispatch queued dynSMF background compiles via `process_spawn_async`;
(2) content-hash guard for dynSMF lane; (3) `smf_cache_reuse_spec.spl`.

### Cross-domain decisions for Architecture phase
- **Don't duplicate closed work** — interpreter micro-opts (debug_state atomics, extern
  dispatch map, mimalloc, mold, rayon, H2/H3/QUIC) are DONE. New wins are narrower:
  MIR bulk-ops (RISK: phases 2-8 unimplemented; a false bulk-copy recognizer regresses
  all 3 modes), `rt_*` wrapping sweep, string-copy minimization, db RAM/persistent
  benchmark split, web/db benchmark sspec.
- **Arch-tagging:** reuse `std.spec.decorators` `skip(architectures:[], tags:[])`; file a
  feature request for a `--filter-tag` runner filter + positive `only_on()` selector.
- **API/arch guard (AC-8):** snapshot public-symbol SDN via `symbol_analyzer.spl` +
  `metadata_symbol_surface.spl`, diff per phase; + accessor-forwarding cache-invalidation
  specs; + `doc/04_architecture/` parity checklist.
- **Doc locations:** dated runs → `doc/09_report/`; persistent tables → `doc/10_metrics/perf/`;
  API snapshots → `doc/08_tracking/api_surface/`; generated manuals → `doc/06_spec/`.
- **Quarantine** 3 pre-existing broken specs (rate_limit/request_validation/security_headers,
  refactor `cd46a9463a4`) so they don't read as AC-8 regressions; fix-or-document first.

### Risks
- MIR bulk-ops false positives (all-mode regression) — gate behind correctness specs first.
- Native-mode sspec false-greens (unresolved `rt_bdd_*`/`std.spec` no-op) — pair with
  interpreter coverage + hard `rt_exit` checks for runtime-ABI benches.
- SQLite FFI path interpreter-unavailable → DB benches need mode tags.

## Architecture (Phase 3 — Opus)
Docs: `doc/03_plan/infra/perf_umbrella/perf_opt_plan.md` (+tldr),
`doc/05_design/infra/perf_umbrella/perf_opt_design.md` (+tldr).

**Module list** (new=+, mod=~):
- `+ src/app/test/bench/bench_harness.spl` — tag+mode+closure → warm/cold/throughput/RSS
- `+ src/app/test/bench/bench_report.spl` — results → `doc/09_report/perf/` + `doc/10_metrics/perf/`
- `+ test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` (AC-4)
- `+ test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` (AC-5)
- `+ test/05_perf/web/web_server_bench_spec.spl` · `+ test/05_perf/os/os_fs_sched_bench_spec.spl`
- `+ src/app/cli/api_surface_snapshot.spl` + `+ scripts/check/check-api-arch-guard.shs` (AC-8)
- `~ src/app/startup/dynsmf_autoload.spl` · `~ src/os/smf/dynsmf_session.spl` +
  `+ test/02_integration/app/simple/smf_cache_reuse_spec.spl` (AC-7)

**Interface:** `struct BenchCase{name,arch_tags,mode,iters}` + `bench_run(case, body: fn()->())
-> BenchResult` + `bench_emit(results, report_path, table_path)`. Composition only, no inheritance.

<!-- sdn-diagram:id=perf-umbrella-state
flow { harness->docs; snapshot->guard; opt->guard; guard->{pass:land, fail:block}; dynsmf->cachespec }
-->

## Implement + Verify (Phases 4–7 — parallel Sonnet lanes, Opus review)
Spec+implement merged per-lane (TDD). Three waves, each committed before the next (advisor
anti-clobber); Lane B sole-owned the dynsmf pair.

**Wave 1** (commit `rzo ff8`): bench harness (warm+process planes) + lang script-vs-compiler
spec (9/9, fib oracle); AC-7 dynSMF dispatch + `.srchash` content-hash + 7-case invalidation
spec (7/7, 15 existing dynsmf specs still green); API/arch guard + `baseline.sdn` (303 syms,
GREEN) + quarantine of 3 pre-existing broken specs.
**Wave 2** (commit `pst ddc`): db ram/persistent/wal bench (11 live, negative-control verified);
web bench (7/7, parse→route→serialize oracle); os fs/sched bench (10 live, host-proxy, 4 KB
round-trip oracle, falsification-checked); 6-domain perf checklists (58 items).
**Wave 3** (commit `pst ddc`): `bench_emit_rows` primitive-array API (dodges the staged
cross-module struct bug); `bench_baseline_driver.spl` ran and emitted REAL interpreter baseline
numbers → `doc/09_report/perf/perf_baseline_2026-06-13.md` + `doc/10_metrics/perf/`.

**Bugs filed** (CLAUDE.md: never silently normalize): `interp_cross_module_struct_return_unit`
(P1, staged — "improve interpreter first" target), `smf_header_source_hash_offset_mismatch` (P2).

### AC verification matrix
| AC | Status | Evidence |
|----|--------|----------|
| AC-1 plan+design first | ✅ DONE | plan + design + tldrs landed before any opt code |
| AC-2 checklists | ✅ DONE | `perf_checklists.md`, 6 domains, 58 pass/fail items |
| AC-3 arch-tagged bench sspec → docs | ◻ MACHINERY DONE | 4 specs tagged via `std.spec.decorators`; emit machinery proven, but only **1 of 4 domains (lang-script)** actually emitted a doc — db/web/os doc emission STAGED |
| AC-4 lang script vs compiler separate | ◻ PARTIAL/STAGED | lang spec has the row structure, but baseline doc emitted **script rows only**; smf/native SKIP (toolchain: smf-extern-segfault, native-compile-required) → compiler side STAGED |
| AC-5 db RAM vs persistent separate | ◻ CORRECTNESS DONE | db spec proves 3 distinct modes ram/persistent/wal with count==100 oracles; separated **timing emission** STAGED |
| AC-7 SMF idle compile + cache reuse | ✅ DONE | investigated (verdict table) + built dispatch+content-hash+invalidation spec (7/7); user-script path confirmed pre-existing; **startup regression spec PASSED 2/2** |
| AC-8 no API/arch break guard | ✅ DONE (scoped) | `check-api-arch-guard.shs` symbols=GREEN + arch=GREEN — **scoped to 11 baseline modules**, which do NOT include the modified files (dynsmf, bench); AC-7's added exports are outside the guarded set and are an additive (manual) judgment, not guard-checked |
| AC-6 interpreter/compiler first | ◻ STRUCTURAL | P1 shared (AC-7) landed first + per-app benches built; per-app **optimization landing** STAGED, ordering recorded |
| AC-9 minimize `rt_*` in app view | ◻ STAGED | baseline counts captured (research); reduction sweep = P1 SG-1.2, checklist row |
| AC-10 cross-mode + cross-language | ◻ PARTIAL | interpreter baseline emitted; smf/native + full cross-language run STAGED (toolchain smf-extern-segfault, native-compile) |
| AC-11 umbrella completion | ⏳ IN PROGRESS | P0 machinery + AC-7 DONE/verified; P1 opt-landing + P2 + final no-regression diff = tracked staged sub-goals |

### Honest completion boundary (advisor-guided, corrected)
**Fully DONE/verified this session:** AC-1 (plan+design first), AC-2 (checklists), AC-7 (SMF
idle-compile + cache reuse, startup-regression-checked), AC-8 (API/arch guard GREEN, scoped to
11 baseline modules). The benchmark **machinery** is built and proven end-to-end on the
lang-script slice.

**Built but emission/comparison STAGED** (machinery exists; one slice emitted): AC-3 (only
lang-script of 4 domains emitted a doc), AC-4 (only script side emitted — smf/native blocked by
toolchain), AC-5 (3 modes proven at correctness level; separated timings not yet emitted).

**Optimization-landing STAGED** (genuinely multi-session): AC-6 per-app opts, AC-9 rt_* sweep,
AC-10 cross-language + smf/native runs, AC-11 close. Landing + re-measuring across 4 domains and
proving no-regression cannot be honestly closed in one session. All filed as **staged, not
verified** tracked sub-goals in the plan + checklists. **No false-green closure.**

### Next concrete steps to advance the staged ACs
1. Unblock AC-4/3: resolve smf-extern-segfault + native-compile so `bench_baseline_driver`
   emits smf/native rows; extend driver to db/web/os workloads → 4-domain docs.
2. Fix P1 bug `interp_cross_module_struct_return_unit` → un-`pending()` the struct-based emit.
3. P1 SG-1.2 rt_* reduction sweep (AC-9) with before/after counts.
4. Add dynsmf + bench public exports to the guard's module set (close the AC-8 scope gap).

## Phase
verify-done (P0 + AC-7); optimization sub-goals staged

## Log (continued)
- arch: Opus authored plan + design docs (+tldrs) + state arch section with SDN diagram + module list.
- implement+verify: 3 parallel Sonnet waves (7 lanes) + Wave-3 finish by orchestrator (println→print,
  baseline driver run). Guard GREEN. AC matrix above. P0+AC-7 done/verified; opts staged.

## Log
- dev: Created state file with 11 acceptance criteria (type: code-quality; perf-optimization
  umbrella with no-API/arch-break constraint). Asked 3 clarifying questions; user chose
  full cycle with plan+docs-first phasing, investigate-then-build SMF idle/cache, and
  x86_64-first with arch-extensible arch-tagged reusable sspec benchmarks.
- research: 4 parallel Sonnet agents over disjoint domains (interp/compiler, SMF idle/cache,
  web/db, os/harness/guard). Opus synthesis above. AC-7 = mostly EXISTS for user-script path;
  BUILD dynSMF dispatch + content-hash + specs. Most interpreter micro-opts already closed.
