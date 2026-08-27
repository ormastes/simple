# Typed UI Interface — Parallel-Agent Plan (2026-08-16)

Architecture: `doc/04_architecture/ui/testing/typed_ui_interface_arch.md`.
Research + fact-check:
`doc/01_research/ui/testing/typed_ui_interface_office_research_2026-08-16.md`.
SPipe state: `.spipe/typed_ui_interface_office/state.md`.
Implementation happens in OTHER sessions; this plan is the coordination
contract.

## Phases

0 contract freeze + Office feature ledger (no behavior change; classify every
  Office capability implemented/partial/declared/blocked; inventory public
  widget IDs used by tests)
1 identity safety (UiNodeKey, scoped session store, strict lookup,
  accessible-name fix, source locations; compat facade keeps apps running)
2 UI interface compiler (builder descriptors + .spl extraction, manifests +
  locks (`config/ui-locks/`) + generated symbols + patterns; `.sui` DEFERRED —
  3 example files, zero production use, seed-only parser)
3 SSpec ActionPlan + unified drivers (headless/TUI in-proc/TUI PTY/GUI/Web/
  HTTP-remote; tui|gui|web|both execution; read-after-write settling)
4 evidence + manual projection (annotated frames, overlays, show screen,
  troubleshooting from failure codes)
5 Calc reference vertical slice (one semantic view; delete dual tree + hand
  JSON; Calc P0 increments; web-host preview over ws transport)
6 shared Office kernel + ThemeService (+ Liquid tokens; foundation may start
  parallel with 5, app migration follows Calc contracts)
7 Writer migration → 8 Slides/Draw (stable document IDs) → 9 formats/Base/
  Math/companions → 10 contract & cleanup (delete global store, first-match,
  duplicate trees, string-containment checks; freeze UI interface v1)

## Dependency waves

```
A contract+ledger
├─ B identity ── C ui-compiler ── D sspec-IR ── E evidence/manual   (wave 1)
├─ F tui-driver ── G gui/web-driver ── N web-host                  (wave 2, needs B..E schemas)
└─ H calc reference                                                 (wave 3, needs F/G/N)
   ├─ I kernel  J writer  K slides/draw                             (wave 4)
   └─ L formats/base/math ── M integration QA/cleanup               (wave 5)
Theme lane runs beside waves 1–3; office-wide adoption waits for wave 4.
```

## Agent ownership (frozen files — no cross-edits)

| Agent | Owns | Deliverable |
|---|---|---|
| A architecture | ADRs, feature ledger, contract fixtures | frozen schemas, compat policy |
| B ui-identity | `src/lib/common/ui/widget*.spl`, `widget_store*`, access_types/snapshot, identity tests | UiNodeKey, scoped store, strict lookup, name-extraction fix |
| C ui-compiler | interface generator (pure Simple), builder-descriptor SDN, `config/ui-locks/` | .spl extraction, manifests, locks, source maps (`.sui` AST deferred — would touch seed `sui_parser.rs`/`compiler/src/web_compiler.rs` only if `.sui` gains a production consumer) |
| D sspec-compiler | spec parser, UI target resolver, ActionPlan types | compile-time symbols, UIE1001/1002/1004 diagnostics |
| E evidence/manual | `src/lib/common/spec/evidence/**` | annotated before/action/after manuals, show screen |
| F tui-testing | terminal parser, TUI driver, PTY adapter | TerminalFrame, real-input actions |
| G gui/web-testing | SGTTI (`src/lib/*/ui_test/sgtti.spl`), compositor/DrawIR driver, browser adapter | hit-test actions, screenshots, overlays, parity |
| **N web-host** | `src/app/ui.web/**`, `src/app/ui.vscode/**`, `src/app/ui.tui_web/**`, office serve entry | FIRST: migrate ui.web's own server stack (`async_server.spl`, `tls_serve_loop.spl`) onto http_core (or record an explicit two-stack decision); then HostInterface v2, ws snapshot-diff+input transport, remote `office serve` w/ session tokens+origin+TLS, vscode-style workbench shell |
| H calc | `src/app/office/sheets/**` (incl. retiring `access_server.spl`/`calc_access_session_host.spl` against N's transport contract), Calc system specs | one Calc session/tree, P0 verticals, web-host preview |
| I office-kernel | DocumentSession, command bus, undo, recovery, ThemeService | shared lifecycle + theme authority |
| J writer | `src/app/office/word/**` | migration + manual suite |
| K slides/draw | `src/app/office/slides/**`; Draw is a NEW app dir (`src/app/office/draw/` does not exist yet) | stable document IDs, canvas actions |
| L formats | ODF/OOXML/package/corpus | compat matrix, loss reports |
| M integration QA | gates, perf, fuzz, cleanup | merge validation, dead-code removal |

Conflict policy: hub exports/`__init__` files changed only by integration
owner; feature agents never edit frozen foundation schemas; schema change =
ADR update + foundation-owner approval. Agent N shares http_core with the
enterprise suite lane — coordinate through `src/lib/common/net/http_core.spl`
owner (enterprise); N consumes, never forks.

## Enterprise-suite co-work

- Shared substrate target: http_core (limits/smuggling/path-safety). NOTE:
  ui.web does not use http_core today (own async_server + TLS loop); Agent N's
  first deliverable is that migration (or an explicit recorded two-stack
  decision). Session tokens, origin guard, file/DB backends shared either way.
- Enterprise store app (`src/app/enterprise_store_app/`) is the pilot
  non-Office adopter of the UI manifest + ActionPlan testing after Calc v1 —
  its web UI gains a manifest, generated symbols, and manual-ready specs like
  Office apps.
- Enterprise's blocked native-ACID / SimpleOS `rt_sqlite_*` items stay in
  `.spipe/simple_enterprise_suite/state.md`; not this plan's scope.

## Per-agent required outputs

implementation, unit tests, negative/compile-failure tests, system SSpec,
generated manual, feature-ledger update, migration note, perf/size impact,
known limitations. Code without an executable/manual scenario ≠ complete.

## Review + merge

High-risk (compiler, identity store, format, recovery, transport auth):
implementer → independent cross-lane reviewer → integration owner → focused
gate → cross-surface gate. Merge in contract order: A → B/C/D/E → F/G/N → H →
I/theme → J/K → L → M. Isolated worktrees per lane; no long-lived branches
inventing IDs or helpers.

## Acceptance gates

See arch doc §Acceptance gates. Web-remote additions: auth required, origin
enforced, two remote sessions never share widget identity, reconnect resumes
revision-correlated state.

## First milestone

Calc Typed UI Contract v1 (arch doc §First milestone), including the web-host
preview: the same compiled ActionPlan drives Calc via TUI, GUI, and the ws
remote transport, and the polling access server is retired.
