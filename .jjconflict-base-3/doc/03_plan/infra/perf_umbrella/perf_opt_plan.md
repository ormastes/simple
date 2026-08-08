# Performance Optimization Umbrella — Phased Plan

**Goal:** Improve x86_64 runtime performance of the Simple interpreter/compiler, web
server, database, and SimpleOS — without changing any public API or architecture, and
reducing app-developer-visible `rt_*` usage — driven by reusable, arch-tagged sspec
benchmarks that emit benchmark docs. SPipe goal: `.spipe/perf-opt-lang-web-db-os/`.

**Hard invariants (every phase):** pure-Simple only (no Rust seed / C runtime edits except
safety guards); public API + architecture unchanged (AC-8 guard green); no false-green / no
weakened specs; benchmarks separate script-vs-compiler (lang) and RAM-vs-persistent (db).

## Phase Map

| P | Name | Exit criteria | Sub-goals |
|---|------|---------------|-----------|
| **P0** | Plan, docs, baseline, guard | This plan + design doc landed; per-domain checklists exist; benchmark sspec harness runs and emits docs; API/arch snapshot captured; 3 broken web specs quarantined | SG-0.1 plan/design docs · SG-0.2 checklists · SG-0.3 benchmark harness + arch tags · SG-0.4 API/arch guard snapshot · SG-0.5 baseline run + docs |
| **P1** | Shared interpreter/compiler | Shared wins landed + re-measured vs P0 baseline; AC-7 dynSMF build done with specs; script-vs-compiler numbers separated; guard green | SG-1.1 SMF dynSMF dispatch+content-hash+spec (AC-7) · SG-1.2 `rt_*` wrapping sweep (AC-9) · SG-1.3 MIR bulk-ops (gated) · SG-1.4 string-copy minimization |
| **P2** | Per-app (web/db/os) | Only gaps P1 didn't close; each domain re-measured; db RAM-vs-persistent separated; guard green | SG-2.1 web server benchmark + opts · SG-2.2 db RAM-only + persistent + WAL benches/opts · SG-2.3 SimpleOS x86_64 fs/sched benches/opts |
| **P3** | Umbrella close | All sub-goals done; benchmark docs show no regression vs P0; guard green; ship | SG-3.1 final cross-language run · SG-3.2 regression diff · SG-3.3 ship |

## Ordering rule (AC-6)
P1 lands and is re-measured **before** any P2 work. A P2 sub-goal is undertaken **only** for a
measured gap P1 did not close; the gap and the P1→P2 decision are recorded per sub-goal.

## Per-domain benchmark dimensions
- **Language:** `script` (interpreter) and `compiler` (smf, native) reported as **separate** rows.
- **DB:** `ram-only`, `persistent` (text `_persist`), `wal` (`dbfs_engine/mvcc`) reported separately.
- **Web server:** cold-start, req/s, p50/p99 latency, peak RSS.
- **OS:** fs read/write throughput, exec/spawn latency, scheduler fairness (QEMU x86_64).

## Arch extensibility (x86_64 now; arm/riscv 64/32 later)
Benchmark specs carry `tags`/`architectures` via `std.spec.decorators`. x86_64 runs now;
non-x86 arches are selected later by the same spec via tag — no copy. Open dependency:
runner `--filter-tag` + positive `only_on()` selector (feature request FR, filed in P0).

## Deliverable docs
- Dated benchmark runs → `doc/09_report/perf/`
- Persistent comparison tables → `doc/10_metrics/perf/`
- Public API/ABI snapshots → `doc/08_tracking/api_surface/`
- Generated scenario manuals → `doc/06_spec/...`

## Tracking
Each SG is a row in the state file checklist; P-gates enforced per `spipe_phases.md` Quality Gate.
