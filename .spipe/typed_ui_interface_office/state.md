# typed_ui_interface_office — SPipe state

phase: implement — WAVES 1-2 COMPLETE & GREEN; WAVE 3 ABANDONED MID-FLIGHT (WIP committed, UNVERIFIED)
updated: 2026-08-17

## STOP STATE 2026-08-17 — read before resuming
Account hit its monthly spend limit and the host was saturated (load 343/32
cores, 0GB free, ~245 stray `simple` + ~138 `rustc` processes); all sessions on
the box were directed to stop for a restart under a new login. All three wave-3
agents (H/R/N2) were killed by session limits mid-task.

Committed but NOT VERIFIED — no spec run completed on either:
- f010d22a937 (Agent R): shared UIE1001 suggester `src/lib/common/ui/id_suggest.spl`,
  union-tier ambiguity in sgtti, gui_driver re-exported to 3 more lanes.
  R died right before proving its new collision fixture actually catches the
  old tier-local bug — DO THAT FIRST when resuming.
- 3f0768ec472 (Agent N2): `src/app/ui.web/ui_session.spl` per-session
  transport/auth/revision state, ws session protocol, header-count cap (S1).
  Recorded blocker: true per-session widget identity is impossible while
  `_widget_registry` (src/lib/common/ui/widget_store_ops.spl:20) is
  process-global — Agent B added scoped TYPES but never migrated the registry.
- Agent H (the Calc milestone) produced NO source changes — died before editing
  src/app/office/sheets. Wave 3's milestone is entirely unstarted.

Excluded from commits deliberately: `scratch/h/` (H's baseline scratch) and
`test/01_unit/app/ui_web/tmp_probe_spec.spl` (throwaway probe). Delete or
finish them; do not ship the probe.

RESUME ORDER: (1) verify/repair the two WIP commits and get their specs green,
(2) the registry migration that unblocks session isolation, (3) Agent H's Calc
single-semantic-view milestone from scratch.

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

## Upstream sync 2026-08-17 (fetch only — NOT rebased; agents had uncommitted work)
origin/main is 99 commits ahead of our base `2c714ce38aa`. Collision surface is
almost nil: of everything this plan owns (common/ui, */ui_test, ui.web,
ui.vscode, office, common/spec), upstream touched exactly ONE file.

- `src/lib/common/net/http_core.spl` +159 lines: now the CANONICAL home for
  request limits (`HttpLimits`, `http_limits_default`, `check_request_line`,
  `check_header_count/size`, `check_body_size`, `http_parse_error_status/
  message`) and static-path security (`is_safe_static_path`, `contains_
  null_byte/traversal/backslash`, `normalize_path`, `validate_static_path`).
  The tier copies `std.<tier>.http.{limits,path_security}` now DELEGATE here.
  → Strengthens Agent N's converge-on-http_core verdict; gives exact API names.
  → CORRECTION (verified 2026-08-17): an earlier note here claimed "REBASE
    REQUIRED, our base copy predates them". That was WRONG. `git diff
    HEAD..origin-ssh/main -- src/lib/common/net/http_core.spl` is EMPTY and our
    copy already defines HttpLimits/check_header_count/validate_static_path.
    Cause of the error: origin's history was rewritten (see "land: 39 stranded
    local commits, 3-way merged onto current origin/main"), so the merge-base is
    far older than our base and the three-dot `HEAD...FETCH_HEAD` diff
    attributed to upstream what our tree already had. Use TWO-dot
    `HEAD..origin/main` for "what do they have that we lack" against a rewritten
    history. Nothing was blocked-until-rebase; S1-S4 are callable today.
- Zero upstream changes to widget/access/sgtti/evidence/office/ui.web files.
  Wave-1 and wave-2 work will rebase cleanly on those paths.

### Cross-lane: another session's Tiny UI/Web/WM architecture
`doc/04_architecture/tiny_ui_web_wm.md` (upstream, 2026-08-14, "proposed")
defines Tiny TUI/Web/GUI → TinyPane → TinyDrawStream → Tiny 2D → Tiny WM, and
names `doc/04_architecture/ui/shared_ui_contract.md` as the NORMATIVE shared
widget/event semantics, plus `os/shared_wm_stack.md`. Its frozen V1 interfaces
(TinyModuleV1, TinyPane, TinyEvent, TinyDrawStreamV1, TinyWmPortV1, …) are
Wave-0 contract-owner surfaces.
Reconciliation stance: the typed UI interface is the IDENTITY + TEST contract
layer; Tiny is a RENDER/WM stack. They meet at shared_ui_contract.md — our
manifest/ActionPlan work must not fork widget/event semantics away from it, and
Tiny panes/surfaces are a future driver target (a TinyWm driver adapter), not a
competing semantic authority. Before wave 3 the arch doc must cite
shared_ui_contract.md as normative upstream and state this split explicitly.
ACTION: read shared_ui_contract.md and shared_wm_stack.md at rebase time and
verify our UiAccessNode/UIEvent assumptions still match them.

## Wave 2 results (F/G/N — all green, committed)
- F 4d355e2da21: src/lib/common/spec/terminal_frame.spl (ANSI interpreter:
  cursor, erase, SGR, alt-screen, EAW wide chars, combining-mark attach) +
  src/lib/nogc_sync_mut/ui_test/tui_driver.spl. 14/14 + 8/8.
  LIMIT: real TUI renderer is app-layer (app.ui.render.tui_widgets) and library
  code cannot import app modules — capture(ansi_output) interprets ANSI text
  handed in by app glue; driver does not call the renderer itself.
  Deferred: OSC, DECSTBM scroll regions, cursor save/restore, IME, PTY, UAX#29.
- G c13c3dbbeab: sgtti resolve_strict + SgttiGeometry + gui_driver.spl; legacy
  first-match left untouched (doc-commented). 6/6 + 5/5. 4 lane variants:
  nogc_sync_mut implements, 2 async lanes re-export, gc_sync_mut is a star
  facade (no edit needed); no nogc_async_mut_noalloc lane exists.
  Geometry is REAL (x/y/width/height props, DrawIR-sourced snapshots only);
  absent props → has_geometry:false, never fabricated.
- N 88d03ed0402: ui.web request framing + path safety migrated onto http_core;
  doc/04_architecture/ui/web/ui_web_http_core_migration.md. 7/7 + 5/5.
  VERDICT: staged, entry layer now. S1 limits / S2 structured parse errors /
  S3 static-path validation / S4 body-cap deferred — big-bang would drag in WS
  upgrade + TLS accept loop that http_core does not model (that is how a third
  stack is born). S3 has a real POLICY divergence: is_safe_static_path rejects
  any ".." substring, so it would newly 403 /static/app..js — needs its own
  change + spec, not a silent refactor.
  Found+fixed a real defect: code comment claimed backslash rejection but
  path_is_safe never checked it; now composes contains_backslash properly.
  ui.web had NO header-count cap at all — S1 closes that.

## MUST-FIX before/with wave 3 (cross-lane inconsistencies)
1. UIE1001 "did you mean" has TWO algorithms: D's resolver uses Levenshtein
   ≤2; G's sgtti uses substring containment in node order. Same diagnostic,
   different answers. Unify on one shared helper.
2. G's ambiguity detection is TIER-LOCAL: canonical-id matches checked first,
   widget-id matches only if that set is empty — so a widget id colliding with
   a different node's canonical id is NOT reported ambiguous. Violates the
   arch doc's exactly-one-or-error rule.
3. gui_driver.spl exists only in the nogc_sync_mut lane; no re-export elsewhere.
4. TEST RUNNER: bin/simple test <spec> is killed at 60s by kill_simple_monitor
   (rc=143, looks like a hang). Use SIMPLE_TIMEOUT_SECONDS=0 (or 900). Cost is
   stdlib load, not spec bodies. Confirmed independently by F, G and N.

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
