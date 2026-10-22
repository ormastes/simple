> Merge candidate status (2026-10-11): **UNRUN**. This resolution combines local
> `ddff8671e8348a89ab2eed285311a3ffc1809358` and remote
> `3aa33b9f8de7897fcf4e83c42bc3c44d28782cef`. All counts and PASS statements below
> retain their historical component/source-stage scope. They are not execution,
> semantic verification, or admission evidence for this combined source.

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

## Fixture transport / actual provider evidence update

The prior6/1 positive control was malformed: nil-coalescing Result does not
extract a text payload. The corrected helper explicitly matches Ok and asserts
len1/bytes[0]. No original capped suite was rerun or retroactively validated.
New native fixture regression3/0 and actual provider legacy6/5 -> current6/0
qualify concrete worktree-provider properties. See the CLI TDD report for
source-stage boundaries, owned inputs and P2 oracle limitations. Direct Unicode
selection is proven; find transport of that filename remains open. All20REQ/40AC
remain required; no full runtime or protected admission PASS is claimed.

## Typed graph component evidence — 2026-10-11

The selected20REQ/40AC scope is unchanged. Corrected strict-valid missing-family
baseline3/3 became initial graph3/0. Broader native acceptance14/10 exposed shared
escaping-size mismatch; Astra exposed allocation order before output limits.
Grouped fixes enforce exact size-only preflight before indexes/rows/keys and
explicit escape-byte comparisons. Final modern system SSpec14/0 inspects actual
typed payloads, reference closure, roles, parameter identity, cycle policy,
deterministic output and resource boundaries. Astra reconciled11source/16artifact
hashes and final log: scopedPASS P0=0/P1=0, fullverificationWARN.

These component examples contribute evidence; they do not mark any whole AC done.
All other families/dispatcher, extractors/resolver, snapshot/hook/admission,
execution/DB, projections/Slop/extensions, coverage/runtime/NFR/manual evidence
remain required. See doc/09_report/traceability_graph_codec_tdd_2026-10-11.md.

## Document/declarations component evidence — 2026-10-11

The full40-case matrix is unchanged. Strict-valid dispatcher baseline4/4 became
initial typed4/0; broader final-source native acceptance12/0 covers the three
supported family payloads, four declaration tables, retained conflicts, exception
calendar facts, exact budgets and independently bounded constructed-value APIs.
Because common owners changed, graph14/0, qualification15/0 and budget/order11/0
were renewed once at this source stage. Report and authored manual distinguish
component evidence from whole AC001/002 completion and generated evidence.
See doc/09_report/traceability_document_declarations_tdd_2026-10-11.md.

Review-derived raw-boundary repair adds verified dictionary cardinality before
keys and source-less cumulative key/header/string byte limits. Earlier12/0
acceptance and regressions remain pre-repair evidence; final raw controls5/0,
acceptance13/0 and affected graph14/0, qualification15/0, budget/order11/0
match the changed source. No whole AC, broad runtime or admission PASS follows.

## Targeted operation contract increment — 2026-10-11

Full20REQ/40AC/WP0–WP7 are unchanged. Root owns implementation/merge; sidecarsN/A;
Astra is final reviewer. Declarations major2 supplies explicit add/replace/suppress
without reinterpreting major1. Desired replacement and exact original tuple are
separate, and provenance/applicability references remain untrusted data. Native
strict-valid baseline3/3 -> initial typed3/0 and broader12/0 are distinct stages.
Actual policy authorization/stale-rule resolution AC006 remains required.
See doc/05_design/infra/traceability_link_operations_v2.md and its TDD report.

The unpublished work branch was rebased onto releasee2d56c2 with all89 prior
owned product files byte-identical (AstraPASS P0=0/P1=0). New canonical Stage2
qualification stopped before compilation at its10GB disk-space guard. Logs are
retained; no admission was emitted. Continue implementation independently while
build storage is unavailable; broad runtime and protected admission remain open.

Final operation component native acceptance14/0, affected major1 declarations13/0
and qualification15/0 match the new dispatcher stage. Empty63-node shape and
exact aggregate text boundaries are covered. This remains component evidence,
not real resolver AC006 or whole20/40 completion. Source/oracle AstraPASS P0=0/P1=0;
final evidence review PASS (10source/36artifacts reconciled).

## Conventional association kernel increment — 2026-10-11

Full20REQ/40AC/WP0–WP7 remain unchanged. Root owns implementation and merge;
sidecarsN/A; Astra is final reviewer. New pure-Simple convention owners validate
bounded supplied graph/policy facts and resolve exact registered unit, integration,
component and manual associations. They preserve corroborating origins, roles,
parameter identities, explicit exclusions and positive/negative membership.
Generator-manifest bindings are required before manual candidate recognition;
source-kind/group indexes and every node/group traversal are charged. Structural
association confers no requirement satisfaction, execution proof or eligibility.

Construction RED is an actual missing-module failure with zero executed examples.
Initial native6/0 was followed by Astra causal RED8/2 and grouped cycle2 GREEN26/0.
Astra final component/source/oracle/evidence review PASS P0=0/P1=0; no unchanged
green tests were rerun after convergence. See the conventions design, executable
modern SSpec, its host-extracted manual and TDD report. Ambiguous-input permutation
coverage validates diagnostics/lookups, not claim or generator/exclusion ordering.

Next WP2 work: actual graph extraction/byte binding, complete policy ownership,
explicit operation precedence/authority/stale rules and CLI integration. WP3
incremental/full equivalence must consume both positive and negative dependencies.
All execution evidence, qualifications, Slop surfaces and remaining plan gates
continue separately. Coverage/NFR/full core/MCP/LSP checks and admitted SPipe
manual generation remain open; no full AC/REQ done mark or runtime admission.
