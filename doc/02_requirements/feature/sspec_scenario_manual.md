# Feature Request: SSpec Scenario-Manual Docgen Gaps

Goal: `bin/simple test` generates a scenario-based **user manual** from `_spec.spl` files.
Audit date: 2026-07-05. Pipeline: `src/app/spipe_docgen/` → `doc/06_spec/`.

## Already implemented (no request needed)

| Desired | Status | Evidence |
|---|---|---|
| `"""..."""` docstring emitted verbatim as md | EXISTS | `spipe_docgen/generator.spl:733` |
| Helper call name → prose (`_`→space, actor capitalization) | EXISTS | `spipe_docgen/parser.spl:1267` `manual_step_label_from_source` |
| `step("...")` / quoted-name calls placed as text | EXISTS | `spipe_docgen/parser.spl:1260` `step_helper_label_from_source` |
| GUI screenshot capture + image compare | EXISTS | `src/app/wm_compare/` (`compare_exact`, golden PPM gate) |
| Embedding captures into generated md | EXISTS | `generator.spl:366` `append_embedded_media_group`, `:383` `append_tui_text_capture_group` |

## FR-1: Literal TUI text-grid capture as the default snapshot mode

Current TUI "capture" is a semantic node snapshot (`win_text_simple_ui_snapshot`,
`ui_test/sgtti.spl`), not the rendered character grid a user actually sees.

- Capture the rendered terminal cell grid (chars + optional style) into a `.txt` golden.
- Default capture mode = TUI text-grid; GUI screenshot is opt-in per spec.
- Auto-attach the capture to the generated `doc/06_spec` md (embedding hook already exists via `metadata.tui_captures`).

## FR-2: TUI diff-checking tool with component-scoped assertions

Exists: SGTTI parity checks (visible/focused/enabled/selected per node id) — semantic only.
Missing: a diff tool over captured text grids that

- diffs current vs golden capture and renders a readable char-level diff,
- restricts the check to **specified components/regions** (by node id or rect), ignoring the rest (clock, spinner, etc.),
- on failure prints the region diff; on doc generation embeds the capture (and diff, if any) in the scenario md.

## FR-3: Protocol capture in specs — JSON + binary, rendered and asserted

Missing entirely (only a CBOR debug hexdump at `src/lib/common/cbor/utilities.spl:76`).

- `protocol_capture(name)` records request/response traffic inside a scenario.
- JSON traffic: pretty-printed, golden-compared structurally (field-order-insensitive, maskable fields like timestamps/ids).
- Binary traffic: rendered as a formatted table (offset | hex | field name | decoded value) using a declared frame layout; golden-compared byte-wise with masks.
- Captures embedded into the generated scenario md as fenced json blocks / tables, same display policy as screenshots (`embed_all`/`embed_tui`).

## FR-4: Audience mode + manual annotations

Docgen output today is one QA-flavored doc. A user manual needs filtering and
regrouping of the same run data.

- `--audience=user` — group scenarios by `@manual_section("...")` heading order;
  emit docstrings + step strings + captures; strip golden badges, mask notes,
  source attributions, Given/Then prefixes; move run results to an appendix;
  drop scenarios not tagged `@user_facing` (protocol/binary specs go to the
  `--audience=qa` doc only).
- `--audience=qa` (default, current behavior) — everything visible.
- `@troubleshooting(symptom: "...", fix: "...")` on a scenario emits a row in a
  generated Troubleshooting table.
- Same spec, same run → both docs; no duplicate authoring.

## FR-5: Keymap-dump capture helper

A manual needs a keyboard-reference table that cannot drift. Add a capture
helper (e.g. `capture_keymap()`) that asserts the app's active keymap against a
golden and emits it as a md table into the generated doc.

## FR-6: Structured traceability — requirement ↔ sspec ↔ generated doc, auto-updated

Today requirement IDs are free text (grep conventions: `# @req REQ-*`, IDs
inside `it "..."` strings; checker `scripts/check/cert/check-req-traceability.shs`
is on-demand and its matrix is gitignored). Nothing updates links automatically
per test run.

- First-class `@req(id, ...)` scenario annotation (e.g. `@req("REQ-CFG-001", ...)`),
  parsed by the spec framework (not grep) — same mechanism as `@manual_section` in FR-4.
- `test_db.sdn` gains a structured req-id column (today the ID is embedded in the
  description string, e.g. `"... (REQ-F5-001)"`).
- Every `bin/simple test` run regenerates a traceability matrix
  (`doc/08_tracking/trace/req_trace.md` + `.sdn`):
  requirement → covering scenarios → last result → generated-doc section.
  Same auto-update mechanism as `feature.md`.
- Generated docs get bidirectional links: each manual/spec scenario section lists
  its requirement IDs; the matrix links back to the doc anchor. Links never hand-edited.

## Typed evidence requirements (Modern SSpec completion)

Source: `doc/01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md`
(§3 architecture, §9 tool plan, §10 acceptance gates) and
`doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md`.

### FR-7: Typed evidence manifest and provenance

Every captured artifact must carry a typed manifest recording schema version,
selector, oracle mode, source path, and content hash, rather than an opaque
blob a scenario merely embeds. The manifest schema
`EVIDENCE_MANIFEST_SCHEMA = "simple.sspec.evidence.v1"` and the
`EvidenceManifest`/`EvidenceSelector`/`OracleMode`/`ManualBlock` records are
landed in `src/lib/common/spec/evidence/model.spl`. Fail-closed acceptance:
a manifest with a missing or unrecognized schema version, an unresolved
selector, or a stale source hash must fail the run rather than fall back to
displaying the raw artifact. Without this rule, a captured screenshot or
protocol dump can silently drift from the code path it claims to evidence and
the generated manual keeps reporting the scenario green.

### FR-8: Action trace and bounded settling

Interactive scenarios must record an ordered action trace (click/type/press,
target resolution before and after each step) and settle on an explicit
bounded condition instead of a fixed sleep before capturing state. Acceptance
is fail-closed: a capture taken without a preceding action-trace entry, or a
capture that used an unbounded/fixed-delay wait instead of a declared
settling predicate, must be rejected (`SSDOC-UI-102`). Without bounded
settling, flaky timing produces both false failures that get "fixed" by
lengthening the sleep and false passes where the capture races the real UI
update, so the golden silently stops proving anything about the interaction.

### FR-9: Structural textual comparator

Textual evidence (JSON, protocol text, config dumps) needs a structural
comparator supporting exact/subset/ordered/multiset/pattern/ignore/
correlation checks and duplicate-field multiplicity, not the line-level
trim-and-exact-equal comparison currently available. `compare_evidence` in
`src/lib/common/spec/evidence/evidence_comparator.spl` implements the
fail-closed gates the comparator must apply, exercised by
`test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl`.
Acceptance: closed-mode extra fields, an unresolved pattern selector, or an
ignored value lacking a stated reason (`SSDOC-EVD-103`) must fail the
comparison. The line-diff-only comparator at
`src/compiler_rust/lib/std/src/spec/snapshot/comparison.spl:98-127` (a Myers
diff over `Delete`/`Insert` line ops) treats field reordering or masked
fields as a hard failure or, if pre-normalized, no failure at all — either
way the check stops representing the field it was written to protect.

### FR-10: Binary layout / production-type binding

A binary-evidence table (offset | hex | field name | decoded value) must be
generated from, and its comparator bound to, the same layout declaration the
production encoder/decoder uses — not a documentation-only layout maintained
by hand. Acceptance is fail-closed: byte endianness or bit numbering left
unspecified, or a table whose layout hash doesn't match the production type's
current layout (`SSDOC-BIN-101`/`SSDOC-BIN-102`), must fail rather than
render a plausible-looking but stale table. Without this binding, the binary
table can pass every run while the wire format has actually changed
underneath it, because nothing ties the doc's field list back to the real
struct layout.

### FR-11: Generated-example integrity

Every example claimed to be machine-generated (from a schema, a captured
trace, or a production type) must carry a runnable source reference and
reproducible hash chain: spec SHA-256, evidence manifest schema/version,
provider/parser/comparator IDs and versions, run ID, and golden/artifact
hashes. Acceptance is fail-closed: a generated example with no runnable
source (`SSDOC-EVD-105`) or a stale source/profile/provider hash
(`SSDOC-EVD-106`) must fail scan/verify. Without an integrity receipt, a
hand-edited "generated" example can diverge from its claimed source
indefinitely while still rendering into the manual as if it were freshly
derived truth.

### FR-12: Domain evidence profiles

Each evidence domain (interactive TUI/GUI, text protocol, binary protocol)
needs a declared profile that fixes its selector vocabulary, comparison
mode, and capture requirements, so untyped free-form evidence is rejected
where a profile exists (`SSDOC-EVD-101`) and a TUI golden without a
width/terminal profile is rejected (`SSDOC-TUI-101`). Acceptance is
fail-closed per profile: an evidence node presented against an unknown or
absent profile must fail rather than pass through as ungoverned freeform
text. Without profiles, every domain reinvents its own ad hoc comparison
rules and a reviewer cannot tell whether a given check is asserting anything
meaningful for that domain.

### FR-13: spec-to-spipe semantic evidence integration

Evidence nodes produced by the spec-to-spipe/spec-to-sspec pipeline must
carry stable IDs and source spans, survive a deterministic round trip through
generation, and cover 100% of source disposition (every parsed construct maps
to a generated node or an explicit skip reason). Acceptance is fail-closed: a
generated SSpec/manifest/manual/ledger set that disagrees with each other, or
contains a tautological generated assertion, or leaves an oracle unresolved,
must fail generation (`SSDOC-EVD-104`, §10 spec-to-spipe gate). Without this
integration, the generated manual and the generated spec can drift apart
silently because nothing checks that they were produced from the same typed
evidence graph.

### FR-14: Backward-compatible evidence facade

Existing capture APIs (`Capture` trait implementations, `wm_compare` exact
image gates, `ScenarioEvidenceArtifact`) must keep working unchanged through
a compatibility adapter layered in front of the typed evidence model, so
migrating a spec to typed evidence is opt-in per scenario, not a
flag-day rewrite. Acceptance is fail-closed on the adapter boundary itself:
an adapted legacy capture that cannot be mapped to a valid `EvidenceManifest`
must fail loudly rather than pass through as untyped evidence with no
selector. Without a facade, every legacy spec must be rewritten atomically
before the typed model can land, which is exactly the kind of big-bang
migration that stalls and leaves the codebase on two incompatible evidence
models indefinitely.

**Status: LANDED** 2026-08-08 — `src/lib/common/spec/evidence/legacy_facade.spl`
converts `ScenarioEvidenceArtifact`/`ScenarioCheckerEvidence` into
`CanonicalEvidence`/`ComparisonResult`/`ManualBlock` without modifying the
frozen old API, reusing `scenario_evidence_manual_summary` so old and new
captures render through the same `manual_render.render_block`. Redaction is
preserved losslessly through the conversion. 6 examples
(`test/01_unit/lib/common/spec/evidence/legacy_facade_spec.spl`), with a
sabotage/revert proof on the redaction rule. Verified via the Rust bootstrap
seed (`build/redeploy_runtime/simple`) as sanctioned temporary-repair
evidence — the self-hosted binary was unavailable during landing because a
concurrent session's Stage-3 bootstrap had removed it mid-build. Self-hosted
re-verification is still owed once redeployed.

### Verified repository facts (2026-08-08)

- `ScenarioEvidenceArtifact` is metadata-only — `kind`, `title`, `mime`,
  `path`, `body`, `scenario_id`, `step_id`, `redacted`
  (`src/lib/common/spec/scenario_evidence.spl:44-52`) — it carries no typed
  selector, no oracle mode, and no provenance hash, so it cannot by itself
  satisfy FR-7.
- The current snapshot comparator only trims and exact-compares text, with a
  line-level Myers diff producing `Delete`/`Insert` ops
  (`src/compiler_rust/lib/std/src/spec/snapshot/comparison.spl:37`, `:98-127`);
  it has no structural, subset, or multiset comparison mode, which is the gap
  FR-9 closes.
- The prior design put `render_md()` directly on the runtime `Capture` trait
  (`doc/05_design/sspec_capture_extension.md:35-42`), which cannot work when
  the capture and the docgen renderer run in different processes (docgen
  reads generated artifacts after the fact) — the typed evidence model in
  `src/lib/common/spec/evidence/model.spl` replaces this with data records
  (`ManualBlock`) that a separate renderer consumes.
- `check-req-traceability.shs` reads the structured DB instead of grepping;
  `--strict` (orphan requirement / dangling REQ ref / stale doc link) joins
  `bin/simple build check`.
- Migration: existing free-text `REQ-*` in descriptions keeps working (parsed as
  fallback) so current specs don't break.

## Known mismatch: template teaches unparseable `@step` decorator

Found during the 2026-07-05 port of `test/system/llm_dashboard_tui_spec.spl`:
`.claude/templates/spipe_template.spl` models `@step "label"` decorators on
helper fns, but the syntax does not parse in the current compiler and no real
spec in the repo uses it. Working pattern: plain named helper fns + explicit
`step("...")` calls. Either implement `@step` decorator parsing (fold into the
FR-4/FR-6 annotation work — same parser surface) or remove it from the template.
Do not let new specs copy the broken form.

## Authoring convention (prerequisite, not code)

The generator assembles; it never invents prose. Specs must be written
manual-first: docstrings in user voice, `step("...")` strings as imperatives
("Press `a` to focus the input bar"), `@manual_section` on every user-facing
scenario. A terse spec still generates a correct skeleton — screens and steps —
but no explanations. Document this in the spipe skill/template.

## Generatability proof

`doc/07_guide/app/spipe/scenario_manual_example.md` is the target output. With
FR-1..FR-5 implemented, every element of it maps to a spec source:

| Manual element | Source | Needs |
|---|---|---|
| Screens | TUI grid captures | FR-1 |
| Region-checked assertions | component-scoped diff | FR-2 |
| Protocol JSON / binary tables (qa doc) | protocol capture | FR-3 |
| Sections, troubleshooting, clean user voice | annotations + audience filter | FR-4 |
| Keyboard reference table | keymap capture | FR-5 |
| Steps, explanations, appendix | step strings, docstrings, run results | exists |
| Requirement links + auto-updated matrix | `@req` annotations, per-run trace DB | FR-6 |
