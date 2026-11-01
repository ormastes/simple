# Extreme typing and traceability: acceptance plan

Status: test DESIGN only, 2026-11-01. All new scenarios below are NOT RUN.
No generated manuals, screenshots, executable pass specs or production
qualification are asserted. Use the source-matched self-hosted runtime; an
unavailable runtime is a reported blocker, never a reason to use the Rust seed.

## Preserve baseline traceability

The canonical [AC-TRC-001..040 table](../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md)
remains authoritative and retains its requirement associations. Existing test
sources/manuals do not by themselves establish execution. New scenarios extend
that inventory with AC-TRC-041..054 and AC-EAPI-001..010.

| Baseline acceptance IDs | Apply to extension |
|---|---|
| AC-TRC-001..009 | Versioned SDN, aliases, declarations, ambiguity and invalidation; add group/type facts without weakening these cases. |
| AC-TRC-010..020 | Staged/Git candidate correctness, bounded offline admission and trusted exact-subject execution; do not confuse readable snapshots with admitted builds. |
| AC-TRC-021..028 | Definitions versus observations, incomplete/stale/forged evidence, retained attempts and migration/incremental equivalence. |
| AC-TRC-029..032 | Deterministic reports, stable identity and malicious offline HTML. |
| AC-TRC-033..040 | Shared selection, historical source, resync/focus/truncation, measured budgets, feature completion and visibility-safe export. |

## New traceability scenarios

| ID / requirement | Fixture and observable oracle |
|---|---|
| AC-TRC-041 / REQ-TRC-021 | Same IDs with differing worktree/index/Git content: list/show returns the requested captured subject; missing kind/entity and malformed revision fail explicitly; help matches actual parser. |
| AC-TRC-042 / REQ-TRC-022 | Nested authored groups, directory rename, duplicate IDs, cross-file contains cycle and v1 import: stable identity/memberships or specific validation error; provenance retained, no silent links lost. |
| AC-TRC-043 / REQ-TRC-023 | Directed cyclic/high-fan-out graph: BFS depth 1/8, page 1/200, invalid 0/9/201, shortest path and reverse impact agree with a small independent oracle; budgets report frontier, never complete success. |
| AC-TRC-044 / REQ-TRC-023 | Change each cursor-bound field individually, including page size/filter/visibility; reject stale cursor. Node pages with cross-page edges reconstruct the exact full edge set through independent edge enumeration. |
| AC-TRC-045 / REQ-TRC-024 | Bug linked to a reproducer and immutable explicit fix: show affects/reproduced_by/fixed_by distinctly. Touched files or passing unrelated test cannot mark bug fixed. |
| AC-TRC-046 / REQ-TRC-025 | Same subject/query through CLI, LSP, MCP, Slop, Caret, Markdown and HTML: compare canonical IDs/edges/reasons/counts/qualification; formatting alone may differ. Cancellation/unsaved-buffer subject does not contaminate saved snapshot. |
| AC-TRC-047 / REQ-TRC-026 | Direct call, trait dispatch target set, unresolved dynamic call, import/override and macro/AOP expansion: compiler facts retain exact/bounded_set/heuristic/unknown plus origin; static edge never appears as observed execution. |
| AC-TRC-048 / REQ-TRC-027 | Shared symbol in two features/layers plus unresolved symbol: membership cells and totals use sets/unions; directed dependency matrix stays separate; unknown and filtered cells remain visible and accurately labeled. |
| AC-TRC-049 / REQ-TRC-028 | Existing Slop selection across tree/code/API/matrix, historical source, keyboard focus and bad refresh: same entity, correct snapshot, last-valid stale state and real captures. |
| AC-TRC-050 / REQ-TRC-029 | Rename/squash/backport and moving PR head: immutable commit facts stay stable; explicit fixes differ from touches; stale/offline/unauthorized PR data never becomes empty clean status. |
| AC-TRC-051 / REQ-TRC-030 | Two registered agents with base/head/staged/dirty semantic changes and session restart: per-subject diff/signature/evidence invalidation correct; generation mismatch rejected; overlap not labeled conflict; no lifecycle/worktree mutations. |
| AC-TRC-052 / REQ-TRC-031 | Repeated same-subject Markdown/HTML export is byte-identical with explicit safe output; injected markup/URLs/scripts are escaped or rejected; no network call, prompts, credentials, private source or absolute paths. |
| AC-TRC-053 / REQ-TRC-031 | Path traversal, symlink escape, output collision, failed write and unauthorized node/count leakage: reject before publish; previous output preserved; complete-graph edge round-trip remains correct. |
| AC-TRC-054 / REQ-TRC-032 | Compiler changes a canonical type/visibility/policy: API trace updates from new digest, stale facts labeled; modifying trace metadata cannot alter the compiler verdict. |

AC-TRC-043 additionally requires truncated path search to return unknown rather
than "no path". AC-TRC-044 includes two callers sharing the same named policy
with different allowed scopes/authorization epochs: cursor reuse is rejected,
and private roots/intermediates/edge counts/frontiers/diagnostics reveal no
unauthorized material.

## Extreme typing scenarios

| ID / selected requirement | Fixture and observable oracle |
|---|---|
| AC-EAPI-001 / REQ-EAPI-001,004 | Cover explicit/default/filename/module visibility and `__init__`/alias reexports, methods, constructors/getters, fields, enum payloads, traits/associated types, globals, aliases/defaults/callbacks: only effectively external paths checked; private locals/representation accepted. |
| AC-EAPI-002 / REQ-EAPI-002 | Every canonical builtin integer/float/bool/text/char/platform scalar appears directly and under transparent alias/container/tuple/union/Option/Result/callback nesting. Public surface denied despite alias spelling, pure-math shape or `@allow`; nominal private storage is accepted. |
| AC-EAPI-003 / REQ-EAPI-002,006 | Safe recursive nominal model, invalid alias SCC, bounded generic safe/unsafe substitution, phantom/public generic argument, opaque public raw accessor/conversion and inherited member: correct fixed-point verdict or Unknown; no false Safe from a revisit. |
| AC-EAPI-004 / REQ-EAPI-003 | Same forbidden API under moderate/strict/robust/critical/verified: advisory/warn/deny/deny/deny; project pin cannot downgrade; legacy warning-phase cannot waive named rule; unrelated robust warnings retain prior behavior. |
| AC-EAPI-005 / REQ-EAPI-004 | Macro/AOP/default constructor/getter, derived equality/comparison/operator returning bool/text and postmono specialization introduce an export: recheck rejects it before publishing any artifact/symbol. Private intrinsic helper remains legal. |
| AC-EAPI-006 / REQ-EAPI-005 | Native, interpreter, REPL, dynload, JIT and SMF load forbidden surface with an initializer writing a sentinel: denial leaves sentinel absent; REPL last-valid bindings/state preserved; no registered callback or output artifact escapes. |
| AC-EAPI-007 / REQ-EAPI-006 | Unresolved type/bound, exhausted budget, changed generated surface and cache from weaker policy: Unknown/denial and targeted invalidation; same complete semantic inputs can reuse verdict without artificial clock expiry. |
| AC-EAPI-008 / REQ-EAPI-007 | Existing newunit declaration and typed-literal form, out-of-range literal, two nominal types sharing storage, text/char/bool domain construction and private FFI: real parse/type/lower/run behavior; generated raw constructor/getter and foreign reexport cannot bypass public Simple rule. |
| AC-EAPI-009 / REQ-EAPI-008 | API commands and trace explain the same canonical export-to-leaf path; migration plan identifies callers and usable nominal construction while leaving source unchanged. |
| AC-EAPI-010 / REQ-EAPI-009 | Proof bound to another IR/transform/compiler, missing manual review or unsupported proof target: blocked qualification. Matching durable artifacts may satisfy only their explicitly supported obligation; test pass alone never means proof. |

## Execution placement, manuals and performance

Create/extend real specs under
`test/03_system/app/traceability/feature/` and
`test/03_system/app/compiler/feature/`; unit fixtures belong to the owning
compiler/common traceability packages. Mirror generated manuals under the
corresponding `doc/06_spec/03_system/...` paths only after execution. Existing
world-units specs are regression inputs; their historical RED notes are not
current run evidence. No `.spl` belongs in `doc/06_spec`.

Use meaningful `step` flows and real production adapters, built-in matchers
(`to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`,
`to_be_greater_than`, `to_be_less_than`). An incomplete helper fails explicitly.
Capture command output/protocol/artifact identity for non-UI cases; TUI captures
go under build/test-artifacts and GUI images under doc/06_spec/image. The final
reviewer reads generated manuals and checks actual visible navigation.

Retain selected baseline NFRs: warm commit p95 <=500 ms and p99 <=1 s for <=25
files/2 MiB; push <=2 s; full hook <=10 s; report <=2 s per 1000 observations;
Slop <=150 ms for <=200 nodes; at least 30 samples with p50/p95/p99 per host.
New CodeGraph/API/overlay budgets are [pending NFR choices](../../02_requirements/nfr/extreme_typing_traceability_options.md).
Measure cold/warm startup, representative requests, peak RSS and high fan-out
with source/binary/fixture/policy identities. No invented measurements.

Run each acceptance criterion once per unchanged implementation. Stop on
convergence, honor the six-cycle limit and report blockers. Release requires
real verification PASS; this design-only plan cannot provide it.
