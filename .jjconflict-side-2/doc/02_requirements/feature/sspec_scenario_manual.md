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
