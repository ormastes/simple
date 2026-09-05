# Perf Umbrella Plan — TL;DR

Optimize x86_64 interpreter/compiler, web, db, OS **without** API/arch change; pure-Simple;
reusable arch-tagged sspec benchmarks emit docs. Full: [perf_opt_plan.md](perf_opt_plan.md).

<!-- sdn-diagram:id=perf-plan-phases
flow {
  P0[P0 plan+docs+baseline+guard] -> P1[P1 shared interp/compiler]
  P1 -> P2[P2 per-app web/db/os only for gaps]
  P2 -> P3[P3 close: no-regression + ship]
}
-->

- **P0:** plan/design docs · per-domain checklists · benchmark harness+tags · API/arch snapshot · baseline.
- **P1 (first):** dynSMF dispatch+content-hash+spec (AC-7) · `rt_*` wrapping sweep · MIR bulk-ops (gated) · string-copy.
- **P2 (only unsolved gaps):** web bench/opts · db RAM/persistent/WAL bench/opts · OS fs/sched bench/opts.
- **P3:** cross-language run · regression diff · ship.

Rules: P1 re-measured before P2 (AC-6); lang reports script vs compiler separately (AC-4);
db reports ram-only vs persistent separately (AC-5); guard green every phase (AC-8).
