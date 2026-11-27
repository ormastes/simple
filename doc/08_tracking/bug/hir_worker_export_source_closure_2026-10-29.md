# HIR worker closure omits explicit export origins

Status: scanner omission repaired; full runner build confirmation pending.

Attempt 5's `test_runner_build` failed after 54 seconds, status 1, peak
3,158,448 KiB. Its three workers completed 55, 58 and 164 modules. The
coordinator recorded 277 PASS and 27 BLOCKED rows, with no observed worker
crash or HIR fatal diagnostic; the remaining inventory could not be claimed.
The failure is independent of the CLI's stale VmFlags constructor crashes.
Evidence is under
`/tmp/simple-release-1.0.0-phase2-combined-build-attempt5-20261029/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification`,
especially `logs/test_runner_build.log` and `summary.env`.

The worker's dependency scanner recognized only `use`, `export use` and
`pub use`, while frozen-surface readiness also follows explicit export-origin
edges. The real `src/lib/io_runtime.spl` facade uses `export ... from ...`
throughout. Phase 1 includes those origins; worker closure planning omitted
them. A worker can therefore seed a facade yet leave its required origins as
placeholders, and correctly refuse its claim at the readiness gate.

The repair adds `export names from M`, `from M import names`, and `import M`
to the worker scanner. Bare export sources normalize to `.sibling`, matching
the parser and phase-1 scanner; comments are removed before that decision.
The existing grouped-use behavior and readiness algorithm are preserved.
Scanner and readiness functions move to a pure module with their old public
exports retained by the worker owner. No BLOCKED row is converted to PASS,
no module is excluded, and inventory completeness stays mandatory.

## Executed regression

`test/01_unit/compiler/driver/worker_surface_export_graph_probe.spl` uses the
production scanner and readiness solver with an entry/facade/bridge/leaf
component, including an explicit bare export origin. It also checks that an
unrelated module stays excluded, missing dependencies remain unready, cycles
remain ready when fully built, and existing grouped-use forms still work.
The module-spelling-to-node mapping is synthetic; this does not qualify the
production filesystem resolver or establish the entire runner closure fixed.

Pinned pure-Simple producer
`e3a7e65cdad2aea37939056f5f115053733e342a89f0507eaec3ede9212233d6`
built the native probe with unchanged producer/runtime/tool/source snapshots.
Its single execution exited 0 with `PASS worker-surface-export-graph component
missing cycle forms`. Build peak RSS was 2,863,216 KiB; artifact SHA256
`6fa8c3dbb10767831d2b77f0f7b12228a8ed0a68df46b02115eb662b4ff59e7a`.
Evidence: `/tmp/simple-worker-export-graph-probe-20261029`.

Astra reviewed the exact implementation with no P0/P1/P2 findings. The
expanded SSpec has not executed. Full compiler/core/MCP checks and a rebuilt
runner remain outstanding; this is scoped native diagnostic evidence.
