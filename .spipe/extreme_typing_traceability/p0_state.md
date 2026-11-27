# P0 implementation candidate

Base: release `a42fa36c7ca`, branch `work/trace-query-p0-20261101`.
Scope: bounded production `simple trace list/show features|requirements|bugs`
through worktree preview or exact Git/index snapshot -> declaration extractor
-> common graph. No fixture-only command, no second graph/type authority.

## Exact acceptance scope

- P0-A: live CLI dispatch and registry agree; original traceability-check stays
  unchanged except correcting stale registry help from text/json to SDN.
- P0-B: default worktree preview or explicit `--snapshot=index|git:REV`, selected
  `--path` files and registered `--declaration` paths feed the real provider/build seam. Errors
  preserve snapshot selection and never become an empty successful graph.
- P0-C: features/requirements list and kind-checked show, sorted canonical IDs,
  bounded limit 1..200, optional ID-prefix filter and cursor bound to snapshot,
  generation, operation, kind, filter, selected ID, limit and local visibility
  context. Existing one-hop query behavior remains unchanged.
- P0-D: deterministic table/SDN shows subject, page versus graph completeness,
  provenance and unverified/admission-ineligible status. No source mutation,
  network refresh, evidence qualification or arbitrary file output.
- P0-E: groups and automatic legacy DB ingestion are explicitly unavailable; malformed,
  duplicate/unknown options, stale cursor and wrong-kind/missing IDs fail.

AC-TRC-041 remains UNRUN until runtime admission and execution. The new
worktree owner freezes each selected file's bytes once and compares no-follow
presence, size and modification metadata before/after/end. This detects
observable races, not same-size changes within coarse timestamp resolution or
hostile ancestor races. Output explicitly says non-atomic sequential preview,
unverified and admission-ineligible. The old structural capture remains unchanged.
Git index reuses existing write-tree
freezing (may add immutable Git objects, does not edit index/source/worktree).
Default registry scope is the existing canonical traceability declaration;
authored locators supply bounded closure. Repeated --declaration replaces that
default without changing source. Explicit Bug nodes are queryable, but automatic
legacy bug/feature DB ingestion, groups and P2 BFS remain outside this slice.

## Owned source boundary

`src/lib/common/traceability/query_nodes_v1.spl` owns pure typed-node paging over
existing TraceGraph/TraceQueryResult records. `src/app/traceability` owns strict
query options, shared production snapshot-build seam and table/SDN presentation.
The live CLI calls that entry directly/lazily; no raw-source wrapper is added.
Relevant CLI registration/help/catalog files are included. Focused unit/system
specs use real production functions; execution remains blocked below.

## Evidence and stop conditions

No admitted Stage4 runtime was found by the parent/Luna inventory. No compiler,
tests, docgen, maintain scores or smoke execution is authorized against an
unproven binary. Source candidate and real negative specs may be authored and
reviewed; no PASS, full P0 completion, merge or release claim follows.
At most three distinct meaningful fix/review cycles. Preserve unrelated
`.spipe/release_phase3_20261101/state.md`. No commit before parent review.

Implementation candidate authored; static review cycle 1 corrected frozen
commit/tree provenance and missing-target exit status. Focused unit/system
specs include real CLI subprocesses and production capture, but none executed.
No generated manual, SPipe score, coverage percentage or verification PASS.

Cycle 1 also checked that a tree object cannot masquerade as a frozen commit,
and corrected default-scope test oracles: authored claims have no independent
authority under preview policy, so the canonical scope remains incomplete with
TRACE-AUTHORITY-CONFLICT and exit 1. No self-authorization was added. Static
SPipe assertions use typed matchers; source/whitespace/environment review is
not runtime evidence.

CLI fidelity review retains singular show kinds (plural aliases) and both
--name=value and --name value forms, with shared duplicate/empty validation.

Cycle 2 final source update adds real index CLI coverage and independent Git
process oracles for expected commit/tree OIDs. The execution harness must own
the tested index; these meaningful scenarios remain UNRUN with all runtime,
docgen, maintain, coverage and required core/MCP checks blocked on admission.
The index fixture is a harness-owned alternate GIT_INDEX_FILE with a tree
different from HEAD, so the expected tree check cannot pass vacuously if the
implementation substitutes HEAD.

Cycle 3 closed the final source findings: both SDN option forms preserve
structured parse errors, and the alternate index changes the selected feature
title so the scenario asserts staged content as well as its independent tree.
Astra's final source review found no unresolved P0/P1/P2 findings. Luna's
bounded static inspection and the working/staged environment guards passed;
none of these results establish compilation or execution.

The three source fix/review cycles are exhausted. Preserve this candidate for
admitted-runtime verification rather than starting another unchanged review.
Draft delivery is permitted as unfinished work; merging remains blocked on
the required executable, generated-manual and core/MCP evidence. The separate
E1 owner audit and prior release state are not included in this P0 candidate.

Cycle 3 (final bounded fix): malformed requests honor both SDN flag forms;
unit and real CLI negative scenarios cover separate --format sdn. The
alternate-index fixture now changes the selected canonical declaration title
without touching HEAD/worktree. The index scenario checks that independent
staged title as well as Git tree identity. No further fix cycle is planned;
runtime admission and all execution/docgen gates remain blocked and UNRUN.
