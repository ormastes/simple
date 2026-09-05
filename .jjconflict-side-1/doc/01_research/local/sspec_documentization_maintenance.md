<!-- codex-research -->
# Local Research: SSpec Documentization Maintenance

Date: 2026-08-03

## Scope

Inventory the current SSpec/SPipe generation path, quality analysis, scoring,
maintenance commands, auto-change infrastructure, reference-spec scaffolding,
and process documentation relevant to a professional documentization tool.

## Current canonical SSpec documentation flow

`simple spipe-docgen` is the canonical scenario-manual generator.

- CLI registration and delegation:
  `src/app/cli/dispatch/table.spl`,
  `src/app/io/_CliCommands/run_commands.spl`.
- MCP exposure:
  `src/app/cli/surface_alignment.spl`,
  `src/app/mcp/tool_table_cli_tiers.spl`, and
  `src/app/mcp/main_dispatch.spl`.
- Implementation:
  `src/app/spipe_docgen/spipe_docgen/{main,parser,generator,common}.spl`.
- Top-level `src/app/spipe_docgen/*.spl` files are compatibility exports; new
  behavior belongs in the nested implementation modules.

The parser already extracts documentation blocks, metadata, scenario bodies,
manual visibility, `step(...)` calls, helper-derived step labels, include/prev
relationships, capture policies, expected results, and warnings. The generator
already emits mirrored paths, summary metadata, authored or automatic overview,
evidence/captures, scenarios, folded executable source, counts, and related-doc
references.

Current validation is not a professional quality model:

- `validate_spec` in `parser.spl` checks whether docs/scenarios exist, a raw
  line threshold, presence of broad Overview/Description and Syntax/Examples
  headings, and requirement/plan/design/research link existence.
- Scenario-only files are credited with an estimated ten doc lines per scenario.
- `calculate_coverage` in `generator.spl` maps only documentation line count to
  0/20/40/60/80/90/100.
- Status becomes Minimal/Partial/Complete from line count.

These heuristics reward volume and can give no explanation of narrative
clarity, step quality, oracle strength, traceability, evidence, or manual
structure.

## Existing SSpec correctness lint

The compiler lint already owns stable correctness rules `SPIPE001` through
`SPIPE007` in
`src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl` with
registry/config in `lint_checks.spl` and `config_and_model.spl`.

Covered behavior includes:

- tautological literal assertions;
- placeholder pass helpers and placeholder match arms;
- print-and-return fake skips;
- empty examples or examples with no real assertion/sanctioned skip;
- boolean-wrapper assertion guidance with machine-applicable EasyFix edits.

Focused coverage lives in
`test/02_integration/app/spipe_quality_lint_spec.spl`; user guidance lives in
`doc/07_guide/app/lint.md`.

The documentization analyzer should consume or reference these results, not
duplicate them under new IDs. A separate stable namespace should cover manual
quality rules.

## Maintenance-command precedents

`simple duplicate-check` is the closest command-shape precedent:

- scoped input and several analysis modes;
- text/JSON/SDN output;
- explicit thresholds and nonzero exit policy;
- exclusions and caching;
- deterministic renderers.

Implementation starts at
`src/compiler/90.tools/duplicate_check/{main,formatter}.spl`.

The documentation coverage tool under `src/app/doc_coverage/` has reusable
threshold and JSON/CSV/Markdown reporting patterns, but its API-documentation
model should not become a coupling dependency for SSpec.

## Existing auto-change infrastructure

EasyFix is suitable and should be reused:

- `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl` defines `EasyFix`,
  `Replacement`, `FixConfidence`, `FixReport`, and in-memory `FixApplicator`.
- `src/compiler/90.tools/fix/main.spl` provides atomic/dry-run application,
  interactive selection, and `collect_fixes_from_source`.
- `src/app/io/cli_lint_commands.spl` implements the public `simple fix` path.

Safety caveat: public `simple fix` applies by default and uses `--dry-run` for
preview. Interactive support exists in the compiler tool but is not wired to
the public CLI. SSpec documentization should reuse replacements, confidence,
conflict checks, and atomic writes while using a safer contract:

- preview is the default;
- `--apply` is explicit;
- `--interactive` confirms selected edits;
- non-mechanical narrative/oracle findings never receive an automatic edit.

The existing EasyFix rule `spipe_missing_docstrings` inserts generic prose such
as “Description of this ... block.” That edit improves shape but not knowledge
and should not count as professional documentation. It should become a
suggestion or an explicitly marked fail-fast placeholder, not trusted prose.

## Existing score and anti-pattern sources

`doc/09_report/misc/test/spec_doc_quality.md` records a historical 25-point
manual rubric (Title, Metadata, Overview, Syntax, Test Structure). It was
sampled rather than implemented deterministically and omits modern
traceability, scenario steps, captures, outcomes, troubleshooting, and oracle
quality. It is useful historical input, not the new score contract.

`doc/07_guide/infra/sspec_antipatterns.md` provides twelve stronger rule
candidates:

1. test-speak scenario names;
2. assert-only bodies with no visible step;
3. placeholder docstrings;
4. unexplained magic values;
5. no captures for user-facing specs;
6. fake system narratives;
7. flat scenario dumps without sections/folding;
8. repeated setup instead of named helpers;
9. no troubleshooting/verification information;
10. stale or copied metadata;
11. internal tags leaking into manuals;
12. no step vocabulary.

`doc/07_guide/infra/sspec_scenario_manual.md` defines the implemented manual
shape, visibility, include/prev, capture, environment, and MCP patterns.

## Existing selected modernization requirements

`doc/02_requirements/feature/sspec_scenario_manual.md` already selects six
features: TUI grid capture/diff, protocol capture, audience and troubleshooting
metadata, keymap capture, and structured requirement traceability.
`doc/03_plan/sspec_modernization_plan.md` adds capture registry/golden and
anti-pattern lint plans.

The new lane should not redefine these contracts. It should score their
presence when implemented, expose gaps honestly while planned, and use them as
inputs to a more complete professional manual.

The current documentation sometimes presents planned annotations such as
`@manual_section`, `@troubleshooting`, and structured `@req` as if already
available. Updated guidance must distinguish implemented syntax from selected
or planned capability.

## Reference specification to SSpec

Two bootstrap/seed-era converters exist:

- `src/compiler_rust/lib/std/src/tooling/migrate_spec_to_spl.spl` parses
  Markdown and supports dry-run/all generation.
- `src/compiler_rust/lib/std/src/tooling/scaffold_feature.spl` parses feature
  Markdown and emits a scaffold/stdout.

They are not registered in the current pure-Simple CLI. Their focused tests
under `test/01_unit/app/tooling/` are placeholder arithmetic checks, and emitted
TODO comments do not establish a modern fail-fast SSpec contract. The new tool
may port parsing/schema ideas into owned pure-Simple modules; it must not use
the Rust seed as product tooling.

Active research/options also exist under the slug
`spec_to_sspec_dynlib_migration`. Those documents have no selected final
requirements. A generic reference-spec workflow must coordinate with or remain
clearly separate from that dynlib-specific lane; neither lane may auto-select
the other's pending options.

## Competing documentation generators

The repository currently exposes confusing overlapping surfaces:

- `simple spipe-docgen`: canonical scenario/manual generator;
- `simple spec-gen` in `src/app/spec_gen/main.spl`: extracts docstrings and
  describe/context/it bullets into Markdown;
- `src/app/doc/spec_gen/`: another older parser/Markdown generator;
- `feature-doc`: specialized feature/app manual generation.

MCP text describes `simple_spec_gen` as generating a spec file from source,
while the actual CLI generates Markdown. Adding a fourth ambiguous generator
would worsen the problem. Make SPipe docgen plus one maintenance front end
canonical, document compatibility, and deprecate/consolidate legacy surfaces in
a separate reviewed migration rather than silently changing output.

## Skill and guide drift

- `.codex/skills/refactor/SKILL.md` covers file size, duplication, coupling,
  Big-O, and tests but no SSpec documentization maintenance.
- `.codex/skills/system_test/SKILL.md` requires manual review and zero stubs but
  has no deterministic documentization check.
- `.codex/skills/sp_dev/SKILL.md` similarly relies on subjective manual reread.
- `.claude/agents/spipe/refactor.md` runs lint and duplicate-check but no
  scenario-manual analyzer.
- `.claude/templates/spipe_template.spl` and
  `.claude/agents/spipe/spec.md` still teach bare `@step "..."`, while the
  canonical SPipe skill states that syntax does not parse. Working forms are
  `step("...")` and comment metadata such as `# @step:`.

Required synchronized targets include the Codex refactor/system-test/sp_dev
skills, Claude SPipe/refactor/spec/test guidance and template, matching Gemini
commands, `doc/00_llm_process/llm_wiki.md`, the authoring/refactoring guides,
and a generated manual for the tool's own system specification.

## Recommended reuse boundary

Create a dedicated maintenance front end with these owner boundaries:

- reuse SPipe parser/metadata/scenario extraction and generated-manual path
  logic;
- reuse EasyFix replacement/confidence/conflict/atomic-write primitives;
- reference existing SPIPE lint findings without copying their logic;
- adopt duplicate-check-style scope, output, threshold, and exit policy;
- port only useful reference-parser ideas from bootstrap code;
- keep `spipe-docgen` as the generator invoked to compare the source and mirror;
- emit stable documentization-rule IDs, multidimensional score evidence, text
  and pure JSON, and explicit suggestion/fix classifications.

Mechanical edits may normalize implemented metadata/comment forms or repair a
known invalid bare `@step` form when behavior is preserved. They may not invent
purpose, user outcomes, requirement mapping, or expected values. Generated
scaffolds use explicit `fail("TODO: replace generated placeholder with an
executable assertion")` and remain stubs until completed.

## Open decisions

- Whether the user prefers a dedicated maintenance command, an extension to
  `simple lint`, or new modes on `spipe-docgen`.
- Whether the first release includes generic reference-spec scaffolding or only
  the analyzer/docgen foundation.
- Required performance/CI thresholds and whether SARIF is emitted directly or
  a simpler stable JSON schema is used first.
- Compatibility/deprecation timing for `simple spec-gen` and older generators.
