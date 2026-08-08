<!-- codex-design -->
# Architecture: SSpec Documentization Maintenance

Status: Selected design
Date: 2026-08-03

## Context

Simple has one canonical scenario-manual engine (`spipe-docgen`), stable SSpec
correctness lint rules, a machine-edit substrate (EasyFix), and mature
maintenance-command patterns (`lint`, `duplicate-check`). It also has several
overlapping legacy doc generators and no deterministic measure of whether an
SSpec produces professional living documentation.

## Decision

Add `simple sspec-maintain` as a thin CLI over a cohesive pure-Simple feature
capsule. Reuse canonical owners rather than fork them:

```sdn
sspec_maintain = capsule(
  adapters = [cli, mcp_surface],
  application = [scan, improve, scaffold, documentize],
  domain = [source_model, rules, score, report, baseline, cache],
  existing_owners = [spipe_docgen, spipe_lint, easy_fix, app_io]
)
```

Dependency direction is strictly inward:

```text
CLI / MCP metadata
       |
       v
sspec_maintain application facade
       |
       +--> analyzer -> rules -> score -> report renderers
       +--> cache/baseline
       +--> improve adapter -> EasyFix
       +--> scaffold parser/generator
       +--> documentize adapter -> SPipe docgen
       |
       v
app.io + common crypto/json utilities
```

No analyzer/domain module imports CLI dispatch or MCP. No existing owner imports
`sspec_maintain`.

## Virtual capsule boundary

The feature capsule owns documentization policy, not SSpec execution or Markdown
generation. Its public surface is:

- `analyze_sspec_text(...) -> SspecDocumentizationReport`;
- `scan_sspec_path(...) -> Result<SspecDocumentizationReport, text>`;
- `render_documentization_human/json/sarif(report)`;
- `collect_sspec_improvements(...) -> [EasyFix]`;
- `preview_or_apply_sspec_improvements(...)`;
- `scaffold_reference_spec(...) -> ReferenceSpecScaffoldResult`;
- `documentize_sspec(...) -> Result<SspecDocumentizeResult, text>`.

The CLI owns option parsing, stdout/stderr routing, and exit policy. The capsule
owns deterministic analysis and edit/scaffold results.

## Modules

| Module | Responsibility |
|---|---|
| `src/app/sspec_maintain/model.spl` | Stable report, score, options, scaffold/apply result types |
| `source_facts.spl` | Single-pass structural facts from SSpec and mirrored manual text |
| `rules.spl` | Stable `SSDOC-*` findings; no rendering or I/O |
| `score.spl` | Seven components, weights, deductions, blocker cap |
| `report.spl` | Human/JSON/SARIF-compatible serializers and exit-policy helpers |
| `cache.spl` | Content-addressed multi-format report cache and baseline fingerprints |
| `suppression.spl` | Reviewed owner/reason suppression codec and blocker guard |
| `lifecycle.spl` | Repository-backed lifecycle-link resolution |
| `improve.spl` | EasyFix collection, preview, confirmation, atomic apply, rollback record |
| `scaffold.spl` | Markdown requirement extraction and fail-fast modern SSpec generation |
| `documentize.spl` | Canonical SPipe docgen adapter and scorecard appendix |
| `main.spl` | Thin command parser/dispatcher |

If a module approaches 800 lines, split by concern rather than numbered files.

## Existing-owner integration

### SPipe

File scans call `parse_spipe_file` to retain canonical parse/metadata validation
and then derive maintenance facts from the returned source. `documentize` calls
`run_spipe_docgen`, derives the same mirror path, and appends only the optional
maintenance appendix. Default `spipe-docgen` remains unchanged.

### Lint

The analyzer does not reimplement `SPIPE001..007`. The CLI may ask the existing
linter for those diagnostics and map them into the oracle-strength/blocker
summary while preserving original IDs. `SSDOC-*` is reserved for manual and
traceability quality.

### EasyFix

`improve` produces standard `EasyFix`/`Replacement` values. It uses
`FixApplicator` conflict detection and the existing atomic file owner. Preview
is the maintenance default even though legacy `simple fix` applies by default.

### Legacy generators

`spec-gen`, `app/doc/spec_gen`, and `feature-doc` are not imported. Help and
guides label their actual responsibilities and recommend `spipe-docgen` plus
`sspec-maintain`. Removal remains a separate migration.

## Score architecture

Each component begins at 100. Stable rule deductions are capped at 100 per
component. The aggregate is a documented weighted integer average:

| Component | Weight |
|---|---:|
| Narrative clarity | 15 |
| Behavioral structure | 15 |
| Oracle strength | 20 |
| Requirement traceability | 15 |
| Evidence completeness | 15 |
| Behavioral coverage | 10 |
| Maintainability | 10 |

Blockers set `release_ready=false` and cap the aggregate at 49, but preserve the
uncapped component evidence. The report always exposes weights, deductions,
blockers, and both raw and effective aggregate values.

## Finding identity and baseline

Fingerprint input is:

`schema_version | rule_version | normalized_path | rule_id | normalized evidence identity`

Line numbers are excluded when a stable scenario/metadata identity is present,
so unrelated movement does not create a new finding. Baseline files contain one
fingerprint per line. Active matches are `unchanged`; new findings are `new`;
baseline-only fingerprints are emitted in the report's resolved list rather
than as active violations.

## Cache and invalidation

The cache key is SHA-256 over:

- normalized source path and source content;
- normalized mirror path and manual content or explicit absence;
- analyzer schema/rule version;
- score weights and relevant configuration;
- tool version.

One source/manual pair is parsed once per miss. A per-pair content-addressed
cache record stores
all deterministic serializations from one report plus the score/severity policy
summary needed on a hit. Directory scans therefore reuse unchanged pairs when a
sibling changes. Create/edit/move/rename/delete/manual refresh naturally change
identity or content. Rule/config/tool changes change the key.
`--no-cache` bypasses lookup/write and must serialize identically except for the
explicit cache disposition field.

Directory scans enumerate once, normalize and sort paths, and analyze only
`*_spec.spl`. They do not invoke subprocesses per file.

`documentize` stages canonical SPipe output under a path-and-content identity in
`build/sspec-maintain/documentize/`, reads it back, removes the staging tree,
and only then writes the requested manual. The adapter never asks docgen to
write its intermediate output over a repository manual.

## Apply safety

The write path is:

```text
read + hash -> collect safe fixes -> apply in memory -> preview
            -> confirm/apply -> verify source hash unchanged
            -> isolated canonical reparse -> write rollback artifact
            -> atomic mode-preserving write
```

Only deterministic edits receive `Certain`/`Safe`. Narrative, requirements,
oracles, and expected values are non-applicable suggestions. The smallest
post-edit gate is exactly one canonical reparse of each changed in-memory result
through an isolated file before replacement. Overlap, stale source identity,
reparse failure, or rollback-write failure aborts without a partial source
write; a later directory write failure restores earlier changed sources and
retains rollback artifacts if restoration itself fails.

## Scaffold trust boundary

Markdown extraction preserves source path/hash, headings, explicit requirement
IDs, and source line. It does not infer an oracle. Every extracted normative
item becomes a reviewable scenario shell containing an explicit failing TODO
until setup/action/expected outcome are executable. This makes generated output
useful without making it false evidence.

## Professional manual boundary

The canonical generator remains responsible for the manual body. The
maintenance appendix contributes only observed facts:

- score components and deductions;
- active/resolved findings and safe-fix availability;
- source/manual identities, rule/tool versions, cache state;
- unsupported or ambiguous gaps explicitly found by rules.

It never synthesizes stakeholder prose.

## CLI/MCP startup and hot paths

The CLI is file-delegated like `spipe-docgen`; startup imports the maintenance
capsule only when invoked. MCP exposes read-only `simple_sspec_scan` and
conservative write-capable `simple_sspec_maintain` classifications over the
same CLI owner. Normal MCP startup does not scan the repository or warm the
cache.

Maintenance analysis is not a request-handler hot path. IDE/MCP changed-file
calls use the content cache and never run docgen, subprocess verification, or a
full-tree scan unless explicitly requested.

## Observability

Debug/perf logging records parse, mirror, rule, score, cache, render, apply, and
verification timings plus counts. Machine serializers receive no log text.
Human output states cache hit/miss/bypass and policy decisions.

## Compatibility

- Existing SSpec syntax and `SPIPE001..007` remain unchanged.
- Existing `spipe-docgen` command/output is unchanged by default.
- New scorecard appendix is opt-in through `sspec-maintain documentize`.
- Legacy generators remain callable and are documented accurately.

## Rejected alternatives

- Extending lint: conflates advisory living-doc quality and correctness.
- Extending docgen with edits/scaffolding: mixes generation and mutation.
- LLM-first scoring: nondeterministic and unsafe as a CI gate.
- New runtime/FFI owner: unnecessary; existing pure-Simple facades suffice.
