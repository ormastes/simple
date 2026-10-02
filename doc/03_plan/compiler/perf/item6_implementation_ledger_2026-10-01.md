# Item 6 persistent package/module index implementation ledger

This lane starts from `018ed390eb7131a56f7e4d5d10f96a724765a325`
(`work/grouped-native-release-20261001`) in the separate
`D:/wk-item6-impl-20261001` worktree. The frozen grouped-build source and both
bootstrap attempts are outside this lane.

The authoritative scope is
`persistent_package_module_index_compile_optimization_plan_2026-09-02.md`
and `doc/02_requirements/nfr/explicit_dependency_closure_compilation.md`.
Static source presence is not an execution or performance PASS. No admitted
self-hosted compiler from this source is available yet.

| Area | Source state at base | Remaining production gate |
| --- | --- | --- |
| SCV core | Snapshot/inventory core exists | Event-maintained full inventory and all-entrypoint admission proof |
| Closure freeze | Frozen source and V2/V3 index routing exist | Remove remaining recursive closure discovery from admitted warm commands |
| Index generation | Full-inventory V2 publisher is called by bootstrap index builder | Ordinary CLI cold publication and exact graph/variant/runtime receipt cutover |
| TLDR/SMF | Typed HIR/MIR receipts and runtime/std SMF publication exist | Complete generated-source/provider/initializer output and loader parity |
| Invalidation | Content-vs-semantic flags and reverse edges exist | Consumer-family specificity, SCC atomicity, event-derived changes |
| Scheduler | SCC consumer exists | Reachable SCC production path and deterministic bounded parallel commits |
| Action/archive | CAS archive and typed receipt readback exist | Exact generation binding for all production archives and recovery |
| Events | Git/SCV bridge and membership pointer exist | No per-request untracked listing, overflow/replay/concurrent-writer proof |
| Entrypoints | CLI commands call source admission | Remove binding-only warm fallback and remaining scans after complete graph producer |
| Proof | Focused old probes exist | Current-source native cold/warm parity and time/RSS cohorts |

The follow-up cache-recovery slice makes index generation reclamation take the
same `CURRENT.lock` as publication. It prevents GC from deleting a newly
staged immutable generation before the publisher moves `CURRENT`. It does not
yet cover crash injection, malformed staging retirement, or bounded GC scan
time; those remain recovery acceptance gates.

The CLI final-artifact receipt invalidation slice (`3551e65e2bf`) binds a
warm receipt to the admitted package-index digest and compatibility markers.
It rechecks the bounded, no-follow `CURRENT` pointer at prepare, restore, and
promotion, refuses partial markers, and forces the real worker for explicit
cold initialization or rebuild-pending requests. The focused unit fixture
tests unchanged generation, changed generation, pointer movement, missing
admission marker, and cold-rebuild refusal. Source review, staged diff, and
direct-env checks passed; the Simple unit spec and native cold/warm run remain
**unexecuted** because no qualified runtime is available. This does not
publish a V3 graph, remove the entry-closure scan, prove concurrent index
switching across the whole worker, or establish a performance gain.

## SPipe TDD sequence

The system test must use these five steps against one admitted compiler and
frozen fixture; a synthetic shell response is not completion evidence:

1. `Prepare pinned build inputs`: freeze SCV source, target/backend/producer,
   graph generation, and clean output/cache roots.
2. `Build cold and warm`: invoke the same production CLI twice, require real
   artifact and typed receipt readback, count source/metadata opens and scans.
3. `Change a semantic dependency`: apply one private-body edit and one public
   ABI/provider edit as separate frozen generations.
4. `Verify invalidation and equivalent output`: compare exact dirty SCC sets,
   retained archives, cold/warm normalized output hashes and diagnostics.
5. `Measure stage time and peak memory`: capture process-cold paired timings,
   daemon 20-request RSS growth, source opens, and peak RSS with a named admitted
   serial baseline. Missing baseline or compiler is an unexecuted gate.

The current first red unit case covers a production defect within step 3:
`package_module_index_invalidate_v1` used to reject a declared two-package
cycle before its SCC consumer could schedule it, and a content-only edit did
not include its peer. The implementation must retain the old non-cycle order,
reject inconsistent SCC declarations, and keep unrelated reverse dependents
clean on private-body changes. This does not establish full Item 6 PASS.
