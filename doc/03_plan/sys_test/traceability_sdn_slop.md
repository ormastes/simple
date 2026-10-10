# Traceability, evidence, gates and Slop acceptance test plan

Authority: final report section 22; suffixes below refer to REQ-TRC-*.
Status legend: authored = executable assertions exist but NOT RUN;
planned = implementation/spec/evidence still required. Neither means passing.
All cases remain required at their original scope. Fixture-only tests cannot
substitute for production integration, deployed tools, remote gates or UI.

| AC-TRC | Scope and actual oracle | REQ suffixes | State |
|---|---|---|---|
| 001 | Codec round-trip Unicode, commas, ordered rows, absent/empty and integer boundaries | 001,018 | Scalar/strict and typed summary component stages recorded; full families/reference closure/CLI open |
| 002 | Schema/duplicates/enums rejected; real CLI rejects legacy flags and parses SDN | 001,007 | Strict and typed summary rejection components exercised; full families/production CLI unqualified |
| 003 | Actual extraction creates conventional unit edge without authored DB change | 004 | Planned |
| 004 | Shared explicit test has two targets, one canonical identity | 005,016 | Planned |
| 005 | Second candidate invalidates cached uniqueness and reports ambiguity | 006,017 | Planned |
| 006 | Targeted override scope and stale replacement rejection | 005,006,019 | Planned |
| 007 | Quoted/example REQ ID creates no accepted-by edge | 002,013 | Planned |
| 008 | Missing declaration addition invalidates negative lookup | 007,017 | Planned |
| 009 | Duplicate/delete/rename updates unchanged incoming references | 006,017 | Planned |
| 010 | Actual index/worktree inversion in both directions | 008 | Planned |
| 011 | Alternate index/worktree, spaces/Unicode paths and case collision subjects | 008,009 | Planned |
| 012 | One bad ref rejects full multi-ref push; child cannot consume rows | 009 | Planned |
| 013 | Create/delete/non-fast-forward/protected tag results explicit | 009,011 | Planned |
| 014 | Actual Git/jj/SJ publication reaches same exact-candidate validator | 008,009 | Planned |
| 015 | Missing runtime/cache, timeout/read/schema error never clean | 010 | Planned |
| 016 | Both real dispatcher routes execute mandatory trace gate | 010,011 | Planned |
| 017 | Candidate no-op checker cannot bypass independently trusted gate | 011 | Planned |
| 018 | Candidate weakening policy/baseline/manifest cannot admit itself | 011,019 | Planned |
| 019 | Required job actually runs no-relevant-change evaluation | 010,011 | Planned |
| 020 | PR/merge/merge-group/post-main event binds correct SHA | 011 | Planned |
| 021 | Actual passing acceptance-only run emits SDN/Markdown; lower kinds NOT RUN | 012,013 | Planned |
| 022 | Planned-but-zero cases, missing shards, cancellation/crash incomplete | 012,013 | Planned |
| 023 | Changed inputs/config/expectation/build lane invalidate receipt; proven equivalence reusable | 013,018 | Planned |
| 024 | Forged status/digest cannot confer verified eligibility | 011,013 | Planned |
| 025 | All retries retained; expected failure/unexpected pass distinct | 013 | Planned |
| 026 | Legacy import keeps history without inventing provenance | 001,018 | Planned |
| 027 | Interrupted migration/concurrent update keeps one owner/no link loss | 018 | Planned |
| 028 | Randomized edits/rules/aliases/deletions: normalized incremental equals full | 017 | Planned |
| 029 | Repeated structural output byte-identical; run timestamps isolated | 014 | Planned |
| 030 | Generated output identity has no self-referential tree-hash loop | 014 | Planned |
| 031 | Real feature page exposes requirements/AC/kinds/targets/irregular origins | 002,003,004,005,006,007,014 | Planned |
| 032 | Offline HTML works; malicious source/Markdown remains inert | 020 | Planned |
| 033 | Shared node selection in every tree branch has identical detail identity | 015,016 | Planned |
| 034 | Historical evidence opens pinned historical bytes | 015,020 | Planned |
| 035 | Wrong/lost delta resyncs; invalid input shows explicit last-valid state | 015,020 | Planned |
| 036 | Actual keyboard-only tree/pane/source flow preserves focus | 015 | Planned |
| 037 | Hidden counts explicit; display truncation cannot affect qualification | 013,015 | Planned |
| 038 | Real warm/cold/fan-out latency/RSS receipts meet selected budgets | 010,017 | Planned |
| 039 | Done requires all obligations/authorization; edits invalidate current qualification | 002,013,019 | Planned |
| 040 | Export visibility enforced; arbitrary filesystem paths inaccessible | 020 | Planned |

First executable contract:
`test/03_system/app/traceability/feature/traceability_sdn_spec.spl`.
Helper ownership: that spec's local `run_trace_cli`, `decode_trace_result`, and
`expect_trace_usage_error`; freeze these names before further spec work. Real
CLI result family is `simple.trace.qualification` version 1. Seed warnings,
missing binary, nonzero infrastructure status and nonparseable/contaminated
stdout fail assertions; no optional-runtime skips or fallback execution.

Qualification harness must bind `SIMPLE_TRACE_TEST_BINARY` to an admitted
general-tool executable and source/producer receipts before execution. Merely
setting this environment variable is not proof of admission. Subprocesses use
argument vectors and bounded timeouts without a shell. Test fixture directory
is tracked and immutable; later stateful fixtures use exclusively owned scopes.
The user-authorized Phase2-derived development lane may supply that producer's
full-CLI or standalone command artifact while recording its actual stage,
construction qualification and `SIMPLE_TRACE_TEST_ENTRY_KIND`. Standalone
results cover the production command only; full-CLI dispatch remains a separate
open obligation. Use canonical fresh producer/source/entry-bound output/cache
scopes, and retain their construction and invocation records alongside results.
It must also set `SIMPLE_TRACE_TEST_ROOT` to the exact current working directory;
the helper checks the cwd and fixture exist instead of accepting nonexistent paths.
Canonical stdout byte equality supplements the shared permissive SDN parser.

Shared-value component contract:
`test/01_unit/app/traceability/traceability_sdn_values_spec.spl`. Its four real
encoder/parser scenarios do not prove typed trace-family validation or the
report's multi-table graph document round-trip. The common encoder documents
top-level-only Table support; a separate trace document adapter must emit valid
named sections. Cover multiple named tables plus schema/snapshot blocks before
calling AC001 complete. No current source inspection is claimed as executable
RED/GREEN. All 40 acceptance cases remain open.

Generate mirrored manual through admitted SPipe docgen; review narrative and
captures with Astra; run `sspec-maintain scan` and resolve blockers. Current
manual state: NOT GENERATED; current execution state: NOT RUN.

## 2026-10-11 strict component evidence update

Shared strict decoding has a real legacy RED8/8 and an initial strict GREEN16/0.
Astra review found compatibility/oracle gaps; a separate regression RED3/3
preceded final grouped correction GREEN10/0. The 16-case source snapshot and
final 10-case source bundle are retained separately. None of these counts is
complete AC001/AC002 evidence. See the strict TDD report and SDN diagnostic.

The final regressions observe exact child payloads, null/empty variants, decoded
key identity, row/section ownership, cumulative key/header node counts and late
UTF-8 locations. All outcomes use computed flags and built-in matchers; the
native fail-only runner defect remains an explicit qualification limitation.
Astra final component source and plan/design/evidence reviews pass, P0=0/P1=0.
No unchanged green tests were rerun. Typed family/multi-table/reference closure
contracts precede production CLI acceptance next; all forty cases retain their
original required scopes and downstream integration evidence.

## Typed summary codec component evidence (2026-10-11)

The qualification-summary specs have actual missing-layer RED10/10 then initial
typed GREEN15/0. Review-derived output/order tests produced RED6/1 then final
GREEN11/0. They assert exact typed payloads and failure code/path, source availability,
interrupted evaluation with completed capture, deterministic retained diagnostics,
invalid middle members and resource limits. Earlier and final source snapshots
are retained separately, not combined as final-source coverage. Full qualification
records/remaining families and real production CLI still need acceptance evidence.
The complete forty-case matrix is unchanged.

## CLI capture private increment — 2026-10-11

Full20REQ/40AC and WP0–WP7 remain authoritative. The production SDN command
SSpec passed7/0 at its initial native source stage. Capture controls remain6/1
after the three-cycle cap; Unicode/NUL acceptance is unresolved. CLI/capture
work stays private and must not be counted as release-qualified or full AC002/015
completion. Follow doc/09_report/traceability_cli_tdd_2026-10-11.md and the
tracked native Unicode capture bug before resuming a fresh bounded investigation.
