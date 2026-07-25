# Plan: Modern SSpec — Scenario Manual & Capture Modernization

Status: plan · 2026-07-05 · Domain: app / spipe · Owner: spipe lane
Requirements: `doc/02_requirements/feature/sspec_scenario_manual.md` (FR-1..FR-6)
Design: `doc/05_design/sspec_capture_extension.md`
Target outputs: `doc/07_guide/app/spipe/scenario_manual_example.md` +
`doc/07_guide/app/spipe/manual_examples/{gui_web,baremetal_network,statistics}_manual_example.md`
Scope: PLAN ONLY. No implementation in this document.

## Goal

Turn today's QA-flavored `_spec.spl` → `doc/06_spec` docgen into a system that
(a) emits an audience-filtered **user manual** from the same run, (b) captures
what a user actually sees (TUI grid, GUI image, protocol frames, bit tables,
statistics) against reviewed goldens through one extendable `Capture` trait, and
(c) keeps requirement ↔ spec ↔ doc links auto-updated per test run. Success = the
four example manuals regenerate byte-identical from real ported specs.

## Dependency order

Phase 1 (docgen/runner only) is independent of capture and ships first. Phase 2
lays the capture core; Phases 3–4 add built-in kinds on top of it; Phase 5
finishes user-facing kinds and drives the migration wave. 1 ∥ 2 can run in
parallel (disjoint files). 3 depends on 2. 4 depends on 2+3. 5 depends on 1+4.

---

## Phase 1 — Audience mode, annotations, traceability (FR-4, FR-6)

Goal: `--audience=user|qa` filtering, `@manual_section`/`@troubleshooting`/
`@user_facing` annotations, first-class `@req(...)`, structured `req_id` column
in `test_db`, per-run `doc/08_tracking/trace/req_trace.md`, checker reads the DB.
No capture infra. Size: **L**. Parallelizable internally: annotation-parsing vs
trace-DB work are disjoint.

Files to touch:
- `src/app/spipe_docgen/spipe_docgen/parser.spl` — parse `@manual_section`,
  `@troubleshooting`, `@user_facing`, `@req` into `FeatureMetadata` (extend the
  `@`-metadata path near `is_capture_metadata_line`/`extract_metadata`).
- `src/app/spipe_docgen/spipe_docgen/common.spl` — add fields to
  `FeatureMetadata`/`SspecDoc` (`manual_section`, `troubleshooting_rows`,
  `user_facing`, `req_ids`).
- `src/app/spipe_docgen/spipe_docgen/generator.spl` — `--audience` gate:
  User path groups by `@manual_section` order, strips golden badges / Given-Then
  / source attributions, collapses run results into Appendix A, drops
  non-`@user_facing`; emit Troubleshooting table; add Keyboard/REQ anchors.
- `src/app/spipe_docgen/spipe_docgen/main.spl` — `--audience` CLI flag (default qa).
- `src/lib/nogc_sync_mut/spec/decorators.spl` — `@req` / annotation helpers so the
  framework records IDs structurally (not grep), same mechanism as skip/ignore.
- `src/lib/nogc_sync_mut/test_runner/test_db_types.spl` — add `req_id` to `TestRecord`.
- `src/lib/nogc_sync_mut/test_runner/test_db_serializer.spl` — add `req_id` to the
  `tests |...|` column header + row writer.
- `src/lib/nogc_sync_mut/test_runner/test_db_parser.spl` — parse `req_id` (fallback:
  regex-scrape `REQ-*` from `description_str` when column absent — migration safety).
- `src/lib/nogc_sync_mut/test_runner/doc_generator.spl` — add `generate_req_trace_md`
  wired into `generate_all_docs` (same per-run pattern as `feature.md`).
- `scripts/check/cert/check-req-traceability.shs` — read `test_db.sdn` req_id column
  instead of grepping; add `--strict` (orphan req / dangling ref / stale link) hook
  into `bin/simple build check`.

New files:
- `src/lib/nogc_sync_mut/test_runner/req_trace.spl` — trace-matrix builder (req →
  scenarios → last result → doc anchor), emits `req_trace.md` + `.sdn`.

Spec tests (under `test/`):
- `test/03_system/tools/spipe/sspec_audience_mode_spec.spl` — user vs qa output.
- `test/03_system/tools/spipe/sspec_annotations_spec.spl` — annotation parse + troubleshooting table.
- `test/03_system/tools/spipe/req_trace_spec.spl` — DB column + matrix regen + fallback parse.

Acceptance:
- Given a fixture spec with `@manual_section`/`@user_facing`/`@req`,
  `--audience=user` and `--audience=qa` both regenerate byte-identical to committed
  fixtures; qa contains golden badges, user does not.
- `bin/simple test` writes `req_id` into `test_db.sdn` and regenerates
  `doc/08_tracking/trace/req_trace.md` with each req linked to covering scenarios.
- Free-text `(REQ-F5-001)` in a legacy description still lands in the matrix (fallback).
- `check-req-traceability.shs --strict` passes on clean tree, fails on injected orphan.

---

## Phase 2 — Capture core: trait, registry, sidecars, goldens, policies (design §1–4)

Goal: the `Capture` trait, spec-runtime `CaptureRegistry`, sidecar
`<name>.capture.sdn`, golden storage layout, `ComparePolicy`, first-run auto-write +
`pending-review` gate. No concrete kinds beyond a trivial test kind. Size: **L**.
Depends on nothing in Phase 1 → runs in parallel.

New files:
- `src/lib/nogc_sync_mut/spec/capture/mod.spl` — `Capture` trait, `CaptureResult`,
  `Audience`, `ComparePolicy` enums.
- `src/lib/nogc_sync_mut/spec/capture/registry.spl` — `CaptureRegistry`,
  `capture_registry()`, `register`, `make`; built-in registration at framework init.
- `src/lib/nogc_sync_mut/spec/capture/golden.spl` — path
  `<spec_dir>/goldens/<spec_stem>/<name>.<ext>`, load/write, sidecar emit, pending-review
  tag, `--update-golden` / `--accept-golden` flows.
- `src/lib/nogc_sync_mut/spec/capture/scenario_api.spl` — `capture(kind, name, policy)`
  scenario helper that resolves via registry, records, compares, writes sidecar.

Files to touch:
- `src/lib/nogc_sync_mut/spec/mod.spl` / `__init__.spl` — export capture surface.
- `src/lib/nogc_sync_mut/test_runner/main.spl` — `--update-golden` / `--accept-golden`
  flags; pending-review fails `build check`.
- `src/app/spipe_docgen/spipe_docgen/generator.spl` — read `*.capture.sdn` sidecars;
  §2 generic fallback block for unknown kinds (text-ish fenced inline; else link + pass line).

Spec tests:
- `test/03_system/tools/spipe/capture_registry_spec.spl` — register/make + unknown-kind fallback.
- `test/03_system/tools/spipe/capture_golden_flow_spec.spl` — first-run auto-write →
  pending-review → accept flips to reviewed with run id.

Acceptance:
- A dummy test kind registers, captures, and round-trips a golden.
- Missing golden auto-writes and does NOT count as pass; `build check` red until accepted.
- `spipe_docgen` renders a sidecar it has no plugin for via the generic fallback (never errors).

---

## Phase 3 — Built-in kinds: tui_grid, component diff, bit_table, statistics (FR-1, FR-2)

Goal: `tui_grid` char-grid capture (default TUI mode), component-scoped diff
(`Scoped`/`Masked` regions), `bit_table` with `bits8|bits16|bits32` views,
`statistics` (mean/stddev/percentile vs golden with `Tolerance`). Size: **L**.
Depends on Phase 2. Internally parallel: tui vs bit_table vs statistics disjoint.

New files (each `impl Capture`):
- `src/lib/nogc_sync_mut/spec/capture/kinds/tui_grid.spl` — `.txt` grid, region-scoped
  char diff, `render_md` (User=grid only; Qa=grid+`<details>` diff).
- `src/lib/nogc_sync_mut/spec/capture/kinds/bit_table.spl` — `.bin` serialize;
  `render_md` emits bits8/16/32 aligned tables (offset|hex|field|value).
- `src/lib/nogc_sync_mut/spec/capture/kinds/statistics.spl` — `.stat`/`.sdn` tuple
  `(mean,stddev,p95,N)`; tolerance verdict table.

Files to touch:
- `src/lib/nogc_sync_mut/spec/capture/registry.spl` — register the three built-ins.
- `src/app/spipe_docgen/spipe_docgen/generator.spl` — route their extensions into
  `append_tui_text_capture_group` / a new bit/stat table group.

Spec tests:
- `test/03_system/tools/spipe/tui_grid_capture_spec.spl` — grid capture + scoped diff ignores clock.
- `test/03_system/tools/spipe/bit_table_view_spec.spl` — one word rendered bits8/16/32.
- `test/03_system/tools/spipe/statistics_capture_spec.spl` — tolerance pass + regression fail.

Acceptance:
- `statistics_manual_example.md` regenerates **byte-identical** from a ported stats spec
  (Scenario 2 shows the ❌ regression gate).
- `baremetal_network_manual_example.md` bit tables regenerate byte-identical from a
  ported bit_table spec; the three-granularity switch table matches.
- Scoped tui diff passes when only excluded region (clock) differs.

---

## Phase 4 — protocol_json / protocol_binary + gui_image integration (FR-3)

Goal: `protocol_json` (pretty, field-order-insensitive, `Masked` fields),
`protocol_binary` (offset|hex|field|value via declared frame layout, byte-wise
masked compare), and `gui_image` wired to existing `wm_compare`. Protocol kinds are
qa-only (`render_md(User)==""`). Size: **M**. Depends on Phase 2+3.

New files:
- `src/lib/nogc_sync_mut/spec/capture/kinds/protocol_json.spl`
- `src/lib/nogc_sync_mut/spec/capture/kinds/protocol_binary.spl`
- `src/lib/nogc_sync_mut/spec/capture/kinds/gui_image.spl` — thin adapter over `src/app/wm_compare/`.

Files to touch:
- `src/lib/nogc_sync_mut/spec/capture/registry.spl` — register the three.
- `src/app/spipe_docgen/spipe_docgen/generator.spl` — json fenced block + binary table group;
  reuse `append_embedded_media_group` for gui_image.

Spec tests:
- `test/03_system/tools/spipe/protocol_json_capture_spec.spl` — field-order-insensitive + masked ids.
- `test/03_system/tools/spipe/protocol_binary_capture_spec.spl` — masked byte compare + table.
- `test/03_system/tools/spipe/gui_image_capture_spec.spl` — wm_compare golden gate + match %.

Acceptance:
- `gui_web_manual_example.md` regenerates byte-identical (image screens + TUI-fallback
  agreement + verification appendix match %) from a ported gui/web spec.
- protocol json/binary appear in the qa doc only; absent from the user doc.

---

## Phase 5 — keymap capture, migration wave, anti-pattern lint (FR-5)

Goal: `capture_keymap()` (golden-checked keyboard table), migrate the flagship spec
so `scenario_manual_example.md` reproduces, and a lint rule flagging anti-patterns.
Size: **M**. Depends on Phase 1+4.

New files:
- `src/lib/nogc_sync_mut/spec/capture/kinds/keymap.spl` — active keymap vs golden → md table.
- `test/03_system/app/todo/todo_tui_spec.spl` (+`goldens/`) — the ported flagship spec that
  regenerates `scenario_manual_example.md`.

Files to touch:
- `src/app/spipe_docgen/spipe_docgen/generator.spl` — Keyboard Reference section from keymap capture.
- `src/lib/nogc_sync_mut/spec/decorators.spl` or docgen validate path — lint rule flagging
  over-long `it` names, zero-docstring scenarios, zero-`step` scenarios.
- `.claude/skills`/`.claude/templates/spipe_template.spl` + spipe skill — document
  manual-first authoring convention (prerequisite in FR §"Authoring convention").

Spec tests:
- `test/03_system/tools/spipe/keymap_capture_spec.spl`
- `test/03_system/tools/spipe/sspec_lint_antipattern_spec.spl`

Acceptance:
- `scenario_manual_example.md` regenerates byte-identical from `todo_tui_spec.spl` via
  `--audience=user`; the qa doc `todo_sync_protocol_spec.md` from the same run.
- Lint flags a seeded anti-pattern spec and passes clean specs.

---

## Risks & mitigations

| Risk | Mitigation |
|---|---|
| New `@`-annotations burden the parser in seed vs self-hosted compiler (annotations parsed by docgen text-scan, but `@req`/decorators touch the spec framework the seed must bootstrap) | Keep annotations as line-prefixed metadata parsed by `spipe_docgen` text scan + `decorators.spl` helper fns — no new grammar/keywords. Bootstrap-verify with `bin/simple build bootstrap` at end of Phase 1. If a helper form forces a seed workaround, file a concrete bug per code-style rule, don't normalize it. |
| Sidecar `.capture.sdn` format churn ripples across every golden dir | Freeze the sidecar schema in Phase 2 (`kind,name,audience_tags,passed,summary`) with a `version` field; docgen tolerates unknown fields; add a schema spec test that fails on breaking change. |
| Golden churn floods CI / silent acceptance | `pending-review` gate: new/updated goldens fail `build check` until explicit `--accept-golden`; goldens committed so each flip is a reviewable diff (design §4). No auto-accept. |
| docgen perf on large spec trees (sidecar globbing per spec) | Read sidecars once per spec dir during the existing single-pass generate; reuse per-run regeneration like `feature.md` (no re-parse of goldens). Measure warm docgen time on full `test/` tree at Phase 4; if regressed, fix inline or file a perf bug per rules. |
| Protocol/image goldens are binary — large blobs in git | Store `.bin`/`.png` goldens small and scoped; masks keep them stable; pre-push guard already blocks >100MB blobs. |

## Traceability (FR → phase → planned spec) — this plan is the trace root

| REQ ID | FR | Phase | Planned spec file |
|---|---|---|---|
| REQ-SSPEC-MODERN-001 | FR-1 TUI text-grid default capture | 3 | `test/03_system/tools/spipe/tui_grid_capture_spec.spl` |
| REQ-SSPEC-MODERN-002 | FR-2 component-scoped TUI diff | 3 | `test/03_system/tools/spipe/tui_grid_capture_spec.spl` (scoped case) |
| REQ-SSPEC-MODERN-003 | FR-3 protocol json+binary capture | 4 | `protocol_json_capture_spec.spl`, `protocol_binary_capture_spec.spl` |
| REQ-SSPEC-MODERN-004 | FR-4 audience mode + annotations | 1 | `sspec_audience_mode_spec.spl`, `sspec_annotations_spec.spl` |
| REQ-SSPEC-MODERN-005 | FR-5 keymap capture | 5 | `keymap_capture_spec.spl` |
| REQ-SSPEC-MODERN-006 | FR-6 structured traceability | 1 | `req_trace_spec.spl` |
| REQ-SSPEC-MODERN-007 | Capture core (trait/registry/golden) | 2 | `capture_registry_spec.spl`, `capture_golden_flow_spec.spl` |
| REQ-SSPEC-MODERN-008 | bit_table 8/16/32 views | 3 | `bit_table_view_spec.spl` |
| REQ-SSPEC-MODERN-009 | statistics tolerance capture | 3 | `statistics_capture_spec.spl` |
| REQ-SSPEC-MODERN-010 | anti-pattern lint | 5 | `sspec_lint_antipattern_spec.spl` |

## Definition of done for the modernization

Each of the four example manuals must be reproducible **byte-identical** from a real
committed spec + reviewed goldens, generated by the runner+docgen (no hand edits):

- [ ] `scenario_manual_example.md` (todo) ← `todo_tui_spec.spl` `--audience=user` — Phase 5.
- [ ] `gui_web_manual_example.md` (notes) ← ported gui/web spec `--audience=user` — Phase 4.
- [ ] `baremetal_network_manual_example.md` (nvme) ← ported bit_table spec — Phase 3.
- [ ] `statistics_manual_example.md` (compiler perf) ← ported statistics spec — Phase 3.
- [ ] Every user-facing scenario carries `@manual_section` + `@req`; `req_trace.md`
      regenerates per run and links each REQ-SSPEC-MODERN-00x to a covering scenario.
- [ ] All goldens `reviewed` (no `pending-review`); `bin/simple build check` +
      `check-req-traceability.shs --strict` green; `bin/simple build bootstrap` clean.
- [ ] spipe skill/template document the manual-first authoring convention.
