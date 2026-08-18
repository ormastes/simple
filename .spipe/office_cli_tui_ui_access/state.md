# Feature: Office CLI TUI UI Access

## Raw Request

> add system test which using ui. however, cli support adding on those office tool/ide. like other simple tui tool support for debugging and communication with llm. add it and do system test with sspec test in cli and tui with screen capture. check modern sspec test writing for manual.
>
> do add mullitply and avg() func call actually works.

## Task Type

feature

## Refined Goal

Provide first-class Simple CLI launch and semantic UI-access support for the IDE Office Calc TUI, including real multiplication and `AVG(...)` evaluation, with a modern SSpec operator manual and retained TUI capture evidence.

## Acceptance Criteria

- AC-1: The deployed Simple CLI routes documented IDE feature-check commands and an Office Calc TUI launch command without treating command names or `--feature-check` as source files or unknown options.
- AC-2: A launched Calc TUI registers a canonical UI-access surface that supports windows, snapshot/surface, find, act, and history operations for human debugging and LLM communication.
- AC-3: UI-access actions enter spreadsheet values and formulas using multiplication and `AVG(...)`; the real formula evaluator produces independently asserted calculated values.
- AC-4: A modern executable SSpec system scenario launches Calc through the CLI, discovers the live surface, performs semantic actions, verifies post-action state and history, and captures the rendered TUI.
- AC-5: The generated mirrored `doc/06_spec` manual uses user-voice overview text, imperative `step(...)` flow, `@req` traceability, typed TUI evidence, folded edge/error scenarios, troubleshooting metadata, and reports `0 stubs`.
- AC-6: The normal production IDE/Office entrypoint does not import SGTTI or test/debug-only UI capture modules; test/debug access remains opt-in and removable from the production entry closure.
- AC-7: CLI help, the IDE Office guide, architecture/detail design, test plan, generated manual, and relevant command/skill documentation describe the final launch and UI-access contract consistently.
- AC-8: Focused CLI, formula, UI-access, SSpec, capture, generated-manual, runtime-facade, numbered-artifact, and generated-spec layout gates pass once without placeholder assertions or stubs.

## Scope Exclusions

- Microsoft Excel automation and proprietary Excel rendering parity.
- GUI pixel parity beyond the requested Calc TUI capture.
- New parallel UI-access protocols when the existing `simple.access/v1` contract can be extended.
- Release, version bump, commit, tag, or push.

## Cooperative Review

- Research sidecars: CLI routing/peer-tool patterns; Calc/formula/TUI ownership; modern SSpec/UI evidence patterns.
- Merge owner: `/root`.
- Final reviewer: `/root` using the highest-capability active model.
- Shared interface candidates: `simple office calc --tui`, `simple ide --feature-check --tui|--gui`, and `simple ui windows|snapshot|surface|find|act|history`.
- Manual `step(...)` flow: `Launch Calc through the Simple CLI`; `Find the active spreadsheet surface`; `Enter multiplication and AVG formulas`; `Verify calculated values through UI access`; `Capture the rendered Calc TUI`.
- Setup/checker helpers: `launch_calc_tui_for_ui_access`, `expect_calc_formula_results`, `capture_calc_tui_evidence`.
- Any pre-implementation helper placeholder must fail explicitly with `fail(...)`; silent no-op helpers are forbidden.
- Generated-manual review owner: `/root`.

## Phase

BLOCKED — corrective-implementation-and-evidence, awaiting a self-hosted binary

## Blocker status (re-verified 2026-08-18)

**The blocker is STILL LIVE.** This lane cannot reach AC-1/2/4/8 without a
self-hosted `simple` that can run `test`, `run`, `office`, and `ui`.

Do NOT read "the compiler was rebuilt today" as "this blocker cleared."
`bin/simple` was redeployed THREE times on 2026-08-17 (12:58, 20:10, 20:28) and
**all three produced the RUST SEED**. Evidence, re-checked independently today:

- `readlink -f bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
  **59,621,024 bytes**, mtime `2026-08-17 20:28`. The pure-Simple artifact is
  ~3.46 MB; a 59.6 MB binary is the seed by size alone.
- It prints the seed warning on startup.
- `lint` works on it — and per `.claude/rules/commands.md` **only the seed can
  lint** (`bootstrap/stage3/simple lint` is `unknown command`, exit 1). A
  working `lint` is therefore positive proof of a seed, not of progress.
- `bootstrap/stage3/simple` is stale: 3,464,072 bytes, mtime **Aug 11 22:10**.

Consequence for this lane's evidence rules, unchanged: the deployed-process
gate must record the artifact path, size, digest, and mtime, and must REJECT
every seed marker. Any run on the current `bin/simple` is inadmissible as
AC evidence.

## Sibling lane status (verified by content 2026-08-18)

`ide-office-plugin-suite` and `ide_md_counter_office_hardening` are both
genuinely CLOSED, and the `libreoffice-suite` umbrella has continued to land
office features (circular refs `8ed78bb0bf7`, dependency-order recalc
`12e908dd279`, fill series `6ae2baad0ec`, named ranges `5d26fefc65c`). None of
that clears this lane's blocker — those are source landings verified by content,
whereas this lane requires a live deployed run.

## Log

- dev: Created state file with 8 acceptance criteria (type: feature).
- research: Completed local and domain research across deployed CLI dispatch,
  IDE feature-check, Calc TUI/formulas, semantic UI access, PTY capture, and
  modern SSpec/manual patterns.
- research: Confirmed multiplication works through the real evaluator and
  `AVG(...)` requires a pure `AVG -> AVERAGE` compatibility alias.
- requirements: Wrote selectable feature options F1/F2/F3 and NFR profiles
  N1/N2/N3; implementation is paused for the required user selection.
- requirements: User selected F1 and N1 and explicitly requested parallel
  subagents. Final feature/NFR documents now contain the selected contract;
  unchosen option documents were deleted as required.
- audit (2026-08-08): Prior completion evidence was rejected. The normal Calc
  route rendered a separate used-range TUI, the live server published only five
  cells, the supplied workbook was dropped by the access-service route, and
  the SSpec only read stale receipts. Corrective implementation must retain
  AC-1 through AC-8 and prove them through a deployed self-hosted binary.
- implementation (2026-08-08): Corrective source work routes Office/IDE
  directly to owners, preserves Calc input paths for UI access, publishes the
  complete visible 20x30 UI tree, fixes the normal TUI frame, and normalizes
  AVG before common formula lookup. Live-process verification remains active.
- docs (2026-08-08): Architecture, detail design, agent plan, and system-test
  plan were corrected to remove false completion claims and to retain the
  deployed PTY/run-ID/self-hosted acceptance criteria.
- runtime audit (2026-08-08): No valid current self-hosted Office runtime is
  available. `bin/simple` resolves to a seed despite its release path; the only
  self-hosted candidate is stale and fails Office launch. Final AC-1/2/4/8
  evidence must record the deployed artifact path, digest, mtime, real-command
  stderr, and rejection of all seed markers.
- wiki (2026-08-08): Updated the IDE/Office and LLM operation guides to state
  the opt-in loopback service command and prohibit stale/in-process evidence.
- system-test corrective implementation (2026-08-08): Replaced the
  controller/receipt gate with a unique-run deployed-process gate. It launches
  IDE, Calc PTY, loopback Calc access, and public `simple ui` operations;
  provenance is observed from an Office command rather than inferred from a
  pathname. The SSpec invokes that gate and reads only its fresh run directory.
  The prior generated manual is explicitly marked stale pending self-hosted
  docgen.
- N1 audit (2026-08-08): The corrected gate is not yet N1-complete. Pending
  work is one shared terminal/access session, production (non-test) service
  ownership, observed artifact provenance, warm p95 and RSS-delta receipts,
  >64 history eviction, protocol/viewport assertions, malformed-formula and
  terminal-restoration evidence, focused audit/docgen execution, and manual
  regeneration. These remain blockers for AC-2/4/5/6/8 and goal completion.
- deployment (2026-08-08): A smallest-path redeploy is essential for final
  acceptance, but is deferred while unrelated agents have uncommitted changes
  throughout `src/compiler` and `src/lib`; building now would produce a mixed
  artifact and violate shared-worktree preservation. Resume only after those
  owners publish/clean their work, using the documented incremental deploy and
  its native-cache reuse receipt.
- host integration (2026-08-08): Added a single-owner `CalcSessionHost` for
  `office calc FILE --tui --ui-access-port P`. It owns controller/session,
  services timed loopback requests, and receives terminal bytes through a
  channel. The system gate captures and drives that same PTY child. Source
  checks are diagnostic only because every available runtime is a seed.
- shared layout (2026-08-08): Added `common.ui.spreadsheet_grid` as the single
  Calc viewport contract. The TUI, UI-access tree, and Office web producer now
  share row-major labels and metrics; the access tree is a common semantic
  grid consumed by `common.ui.layout`. ANSI/CSS painting remains local.
- host hardening (2026-08-08): Normal `office calc --tui` and the opt-in
  access command now use the same `CalcSessionHost`. The host emits real ANSI
  redraws, has bounded per-connection I/O, rejects unavailable raw mode, keeps
  the recalculated workbook/session synchronized, and replaces the semantic
  grid only when scrolling changes its visible identities. Malformed formula
  commits fail before mutating the cell.
- manual-first correction (2026-08-11): The executable SSpec now invokes the
  unique-run deployed gate through one cached setup helper, presents the live
  discovery/formula/capture flow as the visible operator scenario, and folds
  fail-closed command/action plus N1 evidence scenarios. Plans, detail design,
  guide, and Office skill now describe the single `all --run-id` contract.
  The generated manual remains intentionally stale until a current self-hosted
  runtime executes the spec and regenerates it with zero stubs.
- parallel corrective lanes (2026-08-11): `office_spipe_docs_audit`,
  `office_spipe_gate_audit`, and `office_spipe_impl_audit` independently
  reviewed and corrected manual structure, deployed evidence, and production
  transport ownership. The gate now binds runtime hash/mtime, validates every
  protocol envelope, proves malformed-formula no-mutation, terminal restore,
  child exit, port closure, exact frame geometry, and live 48/7 results.
- focused verification (2026-08-11): access-controller 11/11, standalone Calc
  CLI 5/5, file-formats 10/10, and session-host isolation 2/2 passed. The old
  deployed runner could not parse the current shared-grid spec; its tautology
  failure branches were replaced with explicit `fail(...)` and remain pending
  the current Stage 4 runner.
- Stage 4 build blocker (2026-08-11): Three bounded build/fix cycles used
  `/tmp/simple-stage3-aarch64-apple-darwin/simple` (SHA-256
  `f34f81f6bf1fc81cc5bcb10f8d3d037615113b97e3145198641e6ea991a6f5e6`).
  The first exposed a missing `MdBlockResult` declaration, now fixed. The
  retained third log `/tmp/office-stage4/build.log` fails closed on ambiguous
  `RiscvTargetAbi.to_text` resolution in the two `LlvmTargetConfig` builders;
  explicit `RiscvTargetContract` annotations are now applied but, per the
  three-cycle guard, are not rebuilt in this turn. Resume with the same
  Stage 3 binary, stable `/tmp/office-stage4/cache`, and output
  `/tmp/office-stage4/out/simple`; only a fresh artifact may run the gate and
  regenerate the manual. Owner and final reviewer remain `/root`.
- post-sync static correction (2026-08-11): The normal Calc host now loads
  sheets through the narrow `sheet_io` owner rather than importing the broad
  interactive/GUI closure, and every explicit invalid access-port value is
  rejected instead of silently falling back to terminal-only mode. The SPipe
  setup is a real inline scenario expanded by `@prev`, so the generated manual
  can show one shared fresh evidence campaign without rerunning the gate.
- typed rejection propagation (2026-08-11): The common UI test protocol keeps
  its void-injector compatibility entrypoint and adds a typed action-result
  seam. Calc maps `CalcAccessActionResult` through that seam, preserves
  `malformed_formula` in the public CLI error, records the correlated rejection,
  and leaves the live session unchanged. The checker now consumes JSON errors
  from stdout or stderr and requires a schema-qualified `source_unavailable`
  response after shutdown. These source changes are diff-clean but remain
  pending validation by the fresh Stage 4 artifact and deployed system gate.
- artifact re-audit (2026-08-11): No qualifying Stage 4/full self-hosted CLI
  exists under `/tmp`. `/tmp/office-stage4/out/simple` is absent; both pure
  Stage 3 compiler artifacts reject `test`, `run`, `office`, and `ui`, while
  the remaining candidate identifies as the Rust bootstrap seed. The focused
  typed-result and controller tests therefore could not start (`unknown
  command 'test'`) and are not counted as execution evidence.
- manual verification registration (2026-08-11): Added the Office CLI/Calc
  SSpec/manual pair to the shared UI SSpec evidence audit. It intentionally
  remains red while the generated manual carries its stale banner; after the
  one green deployed SSpec run, docgen must replace that manual, report zero
  stubs, and make the shared pair audit pass without rerunning the Office gate.
- blocker re-verification (2026-08-18): Re-checked the 2026-08-08/08-11 runtime
  audits against today's tree. Their conclusion holds unchanged — see the
  "Blocker status" section above for the current artifact identity. Three
  redeploys on 2026-08-17 all produced the Rust seed; `bootstrap/stage3/simple`
  is still the Aug 11 artifact. Nothing in this lane advanced; no AC moved.
  Documentation-only pass: no spec was run, no source was touched.
