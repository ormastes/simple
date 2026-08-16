# typed_ui_interface_office — SPipe state

phase: implement — WAVE 1 COMPLETE (A/B/C/D/E landed on branch typed-ui-interface-plan)
updated: 2026-08-16

## Wave 1 results
- A e0ee925343e: ADR-001 (doc/04_architecture/ui/testing/adr/) + office feature
  ledger (doc/08_tracking/office_feature_ledger.md). Only sheets has real hosts.
- B: ui_identity.spl (UiNodeKey etc.), duplicate detection + strict mode in
  widget_store_ops.spl, find_widget_strict (never first-match), kind-aware
  text_value in access_snapshot.spl. 18/18 + 21/21 green; 3 pre-existing
  ui_access_dispatch failures verified pre-existing via stash A/B.
- C 54abcd5ea87: config/ui_builder_descriptors.sdn (31 builders),
  src/app/ui_manifest (gen/check CLI), generated
  config/ui-locks/app.office.calc.ui.sdn (10 nodes). 11/11 green.
- D 8bdf981c33a: src/lib/common/spec/ui_target.spl + ui_target_resolver.spl,
  UIE1001/1002/1003/1004, exactly-one-or-error. 11/11 + 13/13 green.
- E 56c0324a706: src/lib/common/spec/evidence/ui_step_render.spl (UI-step
  manual blocks + annotated terminal frames). 4/4 green.

## Reconciliation items for wave 2+
- Calc's REAL ids: formula_input, cell_grid, btn_save, sheet_tabs, formula_bar,
  cell_ref_label, grid_scroll, nav, root, status — arch doc assumed sheet_grid/
  confirm_edit; use the generated manifest as truth.
- UIE1003 (unsupported action) code was coined by Agent D — add to ADR.
- Duplicate `root` id (sheets_app vs another file) — first real UIE1002 case.
- bin/simple lint broken tree-wide (with_fix internal error) — file a bug or
  confirm one exists before wave 2 relies on lint.
- Manifest scanner is literal-first-arg text scan; cell_{CellRef} pattern and
  scope paths deferred.
- Interpolation gotcha: "{Name}" inside string literals interpolates — build
  pattern literals by concatenation.

## Docs (source of truth)
- research (fact-checked): doc/01_research/ui/testing/typed_ui_interface_office_research_2026-08-16.md
- architecture: doc/04_architecture/ui/testing/typed_ui_interface_arch.md
- parallel plan: doc/03_plan/ui/testing/typed_ui_interface_parallel_plan.md
- guide: doc/07_guide/ui/testing/typed_ui_interface_guide.md

## Summary
UI ID graph becomes a compiled, versioned application interface: manifest +
lock + generated SSpec symbols → one semantic tree per app → compiled
UiActionPlan over headless/TUI/GUI/Web/HTTP-remote drivers → evidence →
generated manuals. Calc is the reference vertical. New web-host lane (Agent N)
makes Office runnable from a browser against a remote server (VS Code-style),
built on src/app/ui.web (host_adapter_contract.spl, ws, session tokens, origin
guard, TLS) + src/app/ui.vscode backend + enterprise http_core. Co-work with
simple_enterprise_suite: shared http_core/session/auth; enterprise_store_app
is the first non-Office manifest adopter after Calc v1.

## Key verified facts (do not re-derive)
- Flat process-global _widget_registry with silent same-id replace:
  src/lib/common/ui/widget_store_ops.spl:20,54-78,204-206
- SGTTI first-match, no ambiguity error: src/lib/nogc_sync_mut/ui_test/sgtti.spl:252-255
- Calc dual semantic tree + hand JSON: src/app/office/sheets/access_controller.spl:129-134,190-282
- .sui = Rust seed only, 3 example files, zero production use — DEFERRED from
  the plan (src/compiler_rust/parser/src/sui_parser.rs:86-88;
  compiler/src/web_compiler.rs:269)
- Default theme IS fluid_light with liquid alias (config/themes/theme.sdn:1,18);
  aetheric_dark only the no-registry fallback (theme_package.spl:97)
- ui.web does NOT use http_core today (own async_server.spl + tls_serve_loop.spl);
  Agent N task 1 = migrate it onto http_core or record two-stack decision
- Only Calc has an HTTP access host (snapshot polling, no ws):
  src/app/office/sheets/access_server.spl
- Slides element IDs index-derived (unstable): slides_app.spl:155

## Next tasks (wave order; ownership in plan doc §Agent ownership)
1. Agent A: ADR + Office feature ledger + public widget-ID inventory (phase 0)
2. Agent B: UiNodeKey + scoped session WidgetStore + strict lookup +
   accessible-name extraction fix (phase 1) — blocks everything else
3. Agents C/D/E: manifest compiler, SSpec target resolver + UIE diagnostics,
   evidence/manual projection (phase 2-4, parallel after A schemas freeze)
4. Agents F/G/N: TUI/GUI drivers + web-host transport (ws snapshot-diff +
   input on http_core; office serve; retire Calc polling server)
5. Agent H: Calc Typed UI Contract v1 (milestone; arch doc §First milestone)

## Constraints
- Never first-match ID resolution; never silent duplicate overwrite.
- Keep surface#widget wire encoding; scope_path additive.
- Web lane converges on http_core (migrating ui.web's existing stack) —
  never add a third HTTP stack. UI locks live in config/ui-locks/ (never
  build/ — .gitignore swallows it).
- Liquid theme lane must not block Calc v1.
- No Office format-compat claims without corpus round-trip evidence.
