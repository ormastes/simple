# Typed trace qualification-summary TDD

STATUS: WARN — local codec increment; full traceability and runtime qualification open.

Owned worktree: `/home/yoon/dev/simple-traceability-product-20261011`, branch
`work/traceability-product-20261011`, source base
`39a4cfbf06564a66cb7467dfa48976a5d0946aff`. The scoped changes are being prepared
for release-targeted integration; no protected integration or publication is claimed.

## Actual results

| Capsule | Result | Scope |
|---|---|---|
| qualification-codec red | 10 examples, 10 failures | Strict syntax accepts semantically invalid summary fixtures; missing typed layer |
| qualification-codec green1 | 15 examples, 0 failures | Initial typed source stage, retained separately |
| qualification-budget-order red | 6 examples, 1 failures | Same-budget encoder/decoder mismatch; other added controls pass |
| qualification-budget-order green | 11 examples, 0 failures | Final grouped review/resource corrections |

The final capsule constructed 53 modules with zero failures and no stub fallback.
Rust use was bootstrap construction only; the executed artifact is native
pure-Simple Phase2. SSpec process exit 0 occurred even for RED; semantic summaries
and computed built-in assertions supply verdicts. Unchanged green specs were not
rerun, and earlier-source results are not relabeled as one final-source run.

## Change and review

Typed records and limits are shared under `std.common.traceability`. Strict
parsing precedes exact schema/type/enum/reference validation. Encoding validates
typed input, preserves selectors/repeated diagnostics, sorts diagnostic records
deterministically and emits common canonical SDN plus one LF. It checks effective
input/output cap before materialization using a safe lower bound, then checks
exact output size. Raw semantic/value bridges are private. Shared strict limits
validation was exposed without changing its predicate.

Astra's design review separated completed snapshot capture from incomplete
evaluation and claimed statuses from authority. Its first source review found
two P1 output-budget defects; grouped corrections address both. Final component
source and documentation review: PASS, P0=0/P1=0, with one P2 wording limitation.
The budget case tests selector and diagnostic caps through encoding and aggregate
text caps through decoding; its title does not establish bidirectional coverage
of each budget. No source or test was changed after the final run. Exact final
source bundle SHA256:
`4e5f7d5329946305231a59a2401bb839c01c9388be431993784980a7fafa04c0`.

The [detail design](../05_design/infra/traceability_qualification_v1.md) defines
summary v1 evolution to an explicit major 2 full qualification contract/importer,
availability semantics, diagnostic ordering and producer-vs-data authority.
Actual binary/log/source and immutable constructor digests are recorded in the
companion SDN diagnostic and retained private probe snapshots.

## Limits of this result

These fixtures validate a summary codec, not a real production CLI evaluation.
The CLI still uses legacy JSON/text and is next to migrate. Full qualification
obligation/evidence/refusal records, remaining families/table/reference closure,
extraction, snapshots, runner trust, projections and Slop remain open. The native
fail-only defect, general-tool qualification, broad compiler/lib/MCP/LSP checks,
coverage, generated manuals, NFR measurements and protected admission remain
unqualified. All 20 REQ-TRC / 40 AC-TRC / WP0–WP7 remain required.
