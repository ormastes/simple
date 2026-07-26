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

design-and-implementation

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
