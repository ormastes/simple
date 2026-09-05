# Coupling closure snapshot — 2026-08-18

Produced by `scripts/check/check-coupling-snapshot.shs --write` (Phase E
per-phase bracketing re-measure). Graph metrics from
`check-coupling-budget.shs --metrics` (closure of src/compiler + src/app
over `use` imports, std/lib nodes included); fast/normal closures from
`bin/simple deps fast|normal src/app/cli/main.spl`.
Machine-readable: `key value` lines below; band = +2% modules/edges,
0% largest_scc, vs the previous coupling_closure_snapshot_*.md.

modules 5641
edges 12436
cycles 64
files_in_cycles 246
largest_scc 13
backend_largest_scc 5
fast_closure 1193
normal_root_closure 1193

previous_snapshot: unset (first snapshot)
Results: 5641 modules, 12436 edges
