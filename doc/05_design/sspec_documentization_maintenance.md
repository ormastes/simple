<!-- codex-design -->
# Detail Design: SSpec Documentization Maintenance

Status: Selected design
Date: 2026-08-03

## Public data structures

`SspecDocumentizationFinding` fields:

- `rule_id`, `dimension`, `severity`, `confidence`;
- `path`, `line`, `column`;
- `evidence`, `rationale`, `remediation`;
- `fingerprint`, `baseline_state`;
- `score_deduction`, `blocker`, `safe_fix_id`.

`SspecDocumentizationScore` fields:

- seven named component integers;
- `raw_aggregate`, `effective_aggregate`;
- `blocker_count`, `release_ready`.

`SspecDocumentizationReport` fields:

- schema/rule/tool versions;
- source/manual paths and SHA-256 identities;
- cache disposition;
- score, active findings, resolved fingerprints;
- analyzed scenario/assertion/step/capture/requirement counts.

`SspecMaintenanceOptions` fields include format, score/severity policy, cache
and baseline paths, no-cache, rule filter, interactive/apply, output directory,
and scorecard inclusion.

`ReferenceSpecScaffoldOptions` fields include input/output paths, overwrite,
preview/stdout, requirement prefix policy, and source-identity inclusion.

## Source facts

One line pass records:

- module/header docstring and metadata links;
- describe/context/it boundaries and scenario names;
- scenario body line range, steps, assertions, helpers, captures, pending/skip;
- requirement IDs and source lines;
- magic expected literals and source-text-only patterns;
- manual/folding/troubleshooting markers supported by the current parser.

The mirrored manual pass records headings, primary-flow sections, step text,
evidence blocks, trace links, troubleshooting/verification, source identity,
and score appendix presence. It never treats a source token as proof that the
manual rendered it.

## Initial stable rules

| ID | Dimension | Detection | Deduction |
|---|---|---|---:|
| SSDOC-NAR-001 | narrative | missing feature/module purpose | 20 |
| SSDOC-NAR-002 | narrative | generic placeholder narrative | 20 |
| SSDOC-BEH-001 | structure | scenario has no visible `step` | 10 each, cap 40 |
| SSDOC-BEH-002 | structure | test-speak/non-outcome scenario name | 5 each, cap 30 |
| SSDOC-ORA-001 | oracle | no real assertion/pending placeholder | blocker, 50 |
| SSDOC-ORA-002 | oracle | source-text/arithmetic pseudo-system oracle | 25 |
| SSDOC-TRC-001 | traceability | no requirement ID | 20 |
| SSDOC-TRC-002 | traceability | dangling requirement metadata/link | blocker, 40 |
| SSDOC-EVD-001 | evidence | user/operator scenario has no capture/evidence | 10 each, cap 30 |
| SSDOC-COV-001 | coverage | no negative/boundary/recovery/unsupported case | 20 |
| SSDOC-MNT-001 | maintainability | flat scenarios without section/folding | 15 |
| SSDOC-MNT-002 | maintainability | missing/stale mirrored manual | 25/blocker if gated |
| SSDOC-MNT-003 | maintainability | invalid bare `@step` form | 10 + safe fix |
| SSDOC-MNT-004 | maintainability | internal tags leak into manual | 10 |
| SSDOC-MNT-005 | maintainability | missing verification/troubleshooting guidance | 10 |

Rule help is a stable table used by human/JSON/SARIF renderers and guides.

## Scoring

For each component: `max(0, 100 - capped deductions)`. The weighted sum uses
integer math and divides by 100. Any blocker caps effective aggregate at 49 and
sets `release_ready=false`. Policy exit is nonzero when either:

- effective aggregate is below `--min-score`; or
- an active finding meets/exceeds `--deny-severity`.

Default scan is advisory and exits zero after successful analysis.

## Renderers

Human output includes summary, score table, blocker banner, ordered findings,
safe-fix availability, cache state, and policy verdict.

JSON contains one versioned object and no presentation noise. SARIF-compatible
output uses `runs[0].tool.driver.rules`, `results`, physical locations,
fingerprints, baseline state, and fixes when safe replacements exist.

## Cache record

Cache storage uses a versioned deterministic line codec under
`.simple/cache/sspec-maintain/`. Identity, score, severity, and payload lengths
precede the human/JSON/SARIF serializations produced from one report model.
Invalid/truncated/version-mismatched records are misses, never partial reports.
Cache write is atomic.

## Baseline

`--baseline <file>` reads a sorted unique fingerprint list. Matching active
findings become `unchanged`; nonmatching active findings remain `new`;
baseline-only values populate `resolved_fingerprints`. A baseline write/update
operation is not implicit in scan.

## Improvement flow

Safe initial changes:

- convert a standalone invalid `@step "Label"` line to `# @step: Label`;
- normalize an exact legacy `use std.spipe` import to canonical
  `use std.spec.*`; the alias module explicitly re-exports the same surface.

Generic narrative insertion is never safe. Preview renders replacements and
before/after hashes. Explicit `--apply` selects the reviewed certain fixes.

Before source replacement, reject stale bytes, validate the proposed content
through the canonical SPipe parser in an isolated file, and remove that file.
Then save a rollback artifact containing path, before/after hash, rule IDs, and
the complete original source before the atomic mode-preserving write. On
failure, report diagnostics and return nonzero with the source unchanged.

## Reviewed suppressions

`--suppressions` parses `RULE_ID|owner|reason|optional-fingerprint`. Unknown
rules and incomplete records are usage errors. Matching non-blockers retain the
finding plus owner/reason metadata but are excluded from score/policy; blockers
are rejected. The suppression content participates in cache identity.

## Reference Markdown extraction

Supported inputs:

- headings containing `REQ-*` or selected configurable ID prefix;
- normative lines containing `shall`, `must`, or an explicit acceptance marker;
- Precondition/Action/Expected/Examples subsections and Markdown tables;
- source line and SHA-256.

The output contains:

- header provenance and scope;
- canonical import;
- one describe group per source feature/rule;
- one outcome-named scenario when an explicit outcome exists, otherwise a
  traceable review-pending name;
- ordered `step` calls derived only from explicit precondition/action labels;
- explicit fail-fast assertion for any unresolved expected result;
- capture TODO comment when the source explicitly names visual/protocol/log
  evidence;
- source-to-scenario mapping summary.

Overwrite requires `--apply --overwrite`; otherwise scaffold previews/stdout or
fails if the output exists.

## Documentize flow

1. Run canonical `run_spipe_docgen` with explicit output and `--no-index`.
2. Re-read the generated mirror.
3. Replace prior delimited maintenance provenance/scorecard sections.
4. Re-analyze the source plus observed generated mirror once.
5. Write deterministic provenance/history and the optional scorecard.

The appendix delimiters make repeated documentize idempotent.

## Error handling

All reusable operations return `Result<T, text>`. CLI usage errors return 2;
I/O/parse/apply/generation errors return 3; successful advisory scan returns 0;
policy failure returns 1. Machine modes serialize errors in their selected
schema and do not emit human banners.

## Performance and diagnostics

Rule evaluation is O(lines + findings); path ordering is O(files²) only if the
runtime lacks a comparator sort, so the implementation must use the existing
stable path sort helper or record/fix a measured regression. String assembly
uses arrays plus `join`, never loop concatenation for large reports.

Diagnostics are level-gated and routed away from machine stdout. Retained perf
fixtures cover warm single-pair analysis and 1,000 source/manual pairs,
including elapsed time and Linux peak RSS.

## Documentation synchronization

Update:

- `doc/07_guide/infra/sspec_documentization_maintenance.md`;
- SSpec scenario manual and anti-pattern guides;
- lint/refactoring/testing guides;
- Codex sp_dev/refactor/system-test/verify skills;
- Claude SPipe/spec/refactor/test/verify surfaces and template;
- matching Gemini refactor/verify guidance;
- MCP/CLI surface descriptions;
- `doc/00_llm_process/llm_wiki.md`;
- mirrored system manual.

`.agents/skills/verify` is affected by verification policy; other `.agents`
skills are `N/A` unless their text names SSpec/manual checks.
