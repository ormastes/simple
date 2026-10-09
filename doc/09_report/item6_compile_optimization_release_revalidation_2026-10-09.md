# Item 6 release-lane revalidation — 2026-10-09

STATUS: BLOCKED. Item 6 is not complete and has no runtime or performance PASS.

## Scope and ownership

Target: `release/1.0`. Inspected remote release revision:
`df266ee64b5a6b8590b0f62b2624455d5e4a6236`.
Owned branch: `work/item6-release-evidence-20261009`.
Owned worktree: `C:/dev/simple-item6-compile-evidence-20261009`.
Fresh session: `01a1209b-addb-7611-a782-83c21be2f8a6`.

The canonical full execution plan is
`doc/03_plan/compiler/perf/item6_compile_optimization_2026-10-03.md` on the
release line. Its stages A–H retain the entire seven-plan Item 6 scope. The
persistent package/module index plan is a component. The broader compiler and
interpreter performance program is related architecture, not a replacement for
the selected Item 6 authority. No new requirements or relaxed budgets are selected.

Earlier release work was merged in PRs #2299, #2305 and #2310. The local
read-only Codex registry contains no separate matching Item 6 title, initial
request, branch or worktree record; the only matching record is this session.
The research-owner ID retained by the component plan was also not found locally.
These are local-registry findings, not proof that historical sessions never
existed. No historical rollout was resumed.

The shared `C:/dev/simple` checkout is dirty across compiler, runtime,
bootstrap, tests and documentation. None of that work was imported or reverted.
Observed Simple PIDs 29616 and 34540 belong to TRACE32 tool servers using the
Rust bootstrap seed; neither was interrupted. Process IDs are point-in-time
observations, not ongoing ownership claims. No other build was restarted.

## Source revalidation against stages A–H

| Stage | Current source finding | Remaining acceptance evidence |
|---|---|---|
| A: authority and research | Full release plan, local/domain research and acceptance matrix exist | Reconcile this dated appendix with retained requirements; source inspection is not execution |
| B: identity binding | Builder binds producer, variant and frozen SCV provenance; route checks expected bindings | Execute independent stale/mixed binding mutations on admitted runtime |
| C: publication and corruption | GC takes `CURRENT.lock`; reader transaction and persistence admission specs exist | Execute race, crash, restoration and corrupt-storage tests; narrow owner tests do not prove full compiler recovery |
| D: semantic invalidation | Driver calls `package_index_route_admitted_current_v1`; transition-derived classification exists | Snapshot-derived root identity still prevents private-edit early cutoff through the real publisher |
| E: reusable artifacts | Archive, generated-input, metadata, remote and daemon owner adapters exist | Execute forgery/input/config/target/compiler mutations and fresh-versus-hit behavior/diagnostic parity |
| F: route adoption | Production source-loading driver uses admitted routing; compiled acceptance wrapper exists | Prove CLI/check/bootstrap/daemon/MCP/LSP boundaries, source reads and zero hidden scans |
| G: measurements | Selected PSI/cache/performance NFRs remain authority | Clean, warm, no-op and single-module-edit cohorts, stage timers and RSS are unavailable here |
| H: qualification | Release work has merged historically | Admitted runtime, applicable bootstrap/core/MCP/LSP checks and shared-fix main-port evidence remain required |

Production owners inspected:

- `src/compiler/80.driver/cache/package_module_index.spl`
- `src/compiler/80.driver/cache/package_module_index_builder.spl`
- `src/compiler/80.driver/cache/package_index_route.spl`
- `src/compiler/80.driver/cache/cold_full_index_producer_v1.spl`
- `src/compiler/80.driver/driver_source_pipeline_loading.spl`
- `src/app/test/package_index_acceptance.spl` and its owner adapters

The old statement that the package-index checker is absent is historical. It
now exists at `scripts/check/check-persistent-smf-package-index.shs` and executes
a compiled artifact. Owner scope is explicit. Default scope reports incomplete
compiler observations rather than manufacturing canonical scenario success.
The existing 44-scenario matrix remains unqualified by this audit.

## Persistent architecture blocker

The October 3 acceptance audit's snapshot-derived root-generation gap still
exists. `cold_full_index_publish_from_driver_v1` constructs
`PackageModuleIndexBuildAuthorityV1` with `snapshot.tree_id` as the root seed
and separately as the SCV tree binding. The builder hashes root seed with
variant. The admitted transition route requires equal previous/current
`root_generation`; otherwise it propagates changes conservatively.

Thus a private source edit that changes the snapshot tree cannot demonstrate
consumer early cutoff through publisher-produced graphs. This is a retained
performance/architecture gap, not evidence of incorrect executable behavior.
Do not remove the compatibility guard, force constant roots in fixtures, or
replace the root with an unauthenticated workspace label/path.

Continue the existing authority-design task: distinguish stable authenticated
package-graph ownership from mutable snapshot provenance; define migration and
relocation/isolation semantics; apply consistently to publication, route,
archives and transition comparison. The regression must use actual frozen
publisher-produced snapshots with independent private/public edits, retain the
private consumer, invalidate the public consumers, reject another project,
and compare relocated copies. It must not inject equal graph roots.

## Actual bounded evidence

No `bin/release` self-hosted deployment was found in the shared Windows checkout.
Two existing binaries were queried once with `--version` using a 20-second
subprocess timeout:

| Binary | Actual result |
|---|---|
| `C:/dev/simple/bin/simple.exe` | Exit 0, `v1.0.0-beta.11`, explicit Rust-bootstrap-seed warning |
| `C:/dev/simple/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe` | Exit 0, `v1.0.0-rc.1`, explicit Rust-bootstrap-seed warning |

The first binary's SHA256 is
`e2a42543d62f794a8df8389de70c4200ff95675b5c48b60f0103b1f47a77e78c`.
Neither binary was used for compile/test/check qualification. The second is a
mutable bootstrap artifact, not a retained candidate; its version probe does
not establish admission or ownership.

One warm-performance receipt gate was run in the shared checkout:
`sh scripts/check/check-demand-driven-smf-compile-performance.shs --scenario warm-package-decision`.
It exited 1: admitted performance/native receipt missing or invalid at
`build/test-artifacts/demand-driven-smf/performance/warm-package-decision.receipt.env`.
This is related-program evidence only, not a substitute for the PSI budgets.

One canonical package-index gate was run in the isolated release worktree:
`sh scripts/check/check-persistent-smf-package-index.shs --scenario missing-index-denied`.
It exited 2: compiled acceptance owner unavailable at
`build/test-tools/package_index_acceptance`.
This is a harness availability blocker, not a behavioral RED result.

No clean/warm/no-op/edit samples, stage times, RSS, native equivalence or
bootstrap/core/MCP/LSP PASS are claimed. No unchanged green check was repeated.

## Bounded continuation plan

1. Obtain an admitted pure-Simple runtime from its owning bootstrap lane, with
   immutable digest, source/toolchain provenance and deployment receipt. Do not
   restart that lane or substitute its seed. Build the acceptance artifact once
   with that admitted compiler in this isolated lane.
2. Execute existing production-owner specs and the 44 canonical scenarios.
   Retain actual operation/read counters and artifacts. Unsupported scenarios
   remain BLOCKED; owner-scope success cannot qualify default system scope.
3. Resolve the stable graph-authority task above before claiming private-edit
   reuse. Any new authority choices outside selected contracts require user
   selection; existing safety guards remain in force meanwhile.
4. Pin source, toolchain, target/config, fixture sizes and immutable baseline/
   candidate binaries. Collect paired clean/warm/no-op/single-module-edit
   cohorts and parse/type/lowering/codegen/link timing plus peak/steady RSS.
   Apply retained NFR budgets and optimize-skill joint time/memory comparison;
   missing measurements never become PASS.
5. Mutate imports, generated inputs, config, target, compiler and public
   interfaces separately. Test corrupt-cache recovery and cached/uncached
   executable output, exit status and diagnostics equivalence.
6. Run affected bootstrap/core runtime and MCP/LSP qualification, compiler/lib/
   MCP/LSP checks and interpreter stdio integration. Native/package smokes apply
   when their source or publication path changes. Record exact identities and
   commands; do not certify other hosts from this Windows inspection.
7. Review and merge scoped work through a release-target PR. Shared source fixes
   require the retained main forward-port protocol. This release-lane evidence
   checkpoint changes no shared source and creates no release candidate, tag
   or publication.

Run each unchanged acceptance criterion once; at most three relevant fix/verify
cycles per defect. Stop with concrete blockers when runtime authority or
measurements cannot be supplied. Updating this report does not close Item 6.
