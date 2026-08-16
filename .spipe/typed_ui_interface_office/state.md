# typed_ui_interface_office — SPipe state

phase: plan (docs landed; implementation NOT started — do it in other sessions)
updated: 2026-08-16

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
