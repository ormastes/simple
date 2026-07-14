# Feature: UI CLI LLM Access

## Raw Request
Add a shared T32-style CLI access grammar for Simple GUI/TUI, TRACE32 GUI, and
host WM windows so an LLM can list, inspect, find, act, and review history.

## Task Type
feature

## Refined Goal
Ship one safe, deterministic, pure-Simple CLI access workflow shared by UI,
TRACE32, and WM adapters, with live evidence and an operator-quality manual.

## Acceptance Criteria
- AC-1: `simple ui`, `simple t32`, and `simple play` expose the selected shared operations through compiled pure-Simple entrypoints.
- AC-2: Human and JSON window lists agree on every normalized REQ-UCLA-005 field and deterministic ordering.
- AC-3: Every action validates bounded input and current target identity/state, uses the owning adapter, observes once, and records correlated request/result history.
- AC-4: T32 session and action inputs cannot reach a shell command boundary unquoted or unvalidated.
- AC-5: WM text input is atomically target-scoped or fails before typing; geometry and focused-surface metadata are preserved when available.
- AC-6: UI post-dispatch timeout failures retain the request ID and warn the operator to inspect history before retrying.
- AC-7: Production UI backend launchers execute cached compiled artifacts and contain no Rust-seed fallback or raw source execution.
- AC-8: Focused SSpec/manual/evidence gates prove live GUI, TUI-web, WM, and T32 flows and fail closed on missing artifacts or PASS markers.
- AC-9: The operator guide, generated/manual spec, agent plan, and changed workflow references are current and contain no executable specs under `doc/06_spec`.
- AC-10: Highest-capability merged review accepts architecture, implementation, evidence, exclusions, and done claim.

## Scope Exclusions
Renderer replacement, arbitrary host descendant accessibility, remote access,
release/versioning, and Rust-seed use outside bootstrap.

## Cooperative Review
- Sidecars: Spark T32 trust-boundary/parity; Spark WM target/metadata; Spark UI compiled-backend/correlation.
- Merge owner: root Codex agent.
- Final reviewer: highest-capability Codex agent.
- Shared interfaces: `AccessCommandDescriptor`, `AccessRequest`, `AccessResult`, `AccessError`, `UiAccessSnapshot`, `WinTextSnapshot`.
- Manual steps: Start UI access; List active windows; Inspect TUI rendering; Inspect GUI rendering; Find an interactive target; Act on the target; Review access history.
- Helpers: `setup_ui_cli_access`, `_check_gate`; placeholders must use `fail(...)`.
- Generated-manual review owner: root Codex agent.

## Phase
static-accepted-runtime-blocked

## Log
- dev: Refreshed state from selected requirements and the higher-capability rejection (type: feature).
- implement: Repaired T32 argv execution/parity, WM exact-window input/metadata, and UI correlation/compiled-backend routing.
- refactor: Refreshed `doc/05_design/ui_cli_llm_access.md`, `doc/07_guide/app/ui/ui_access.md`, `doc/07_guide/app/ui/ui_cli_llm_access.md`, the agent plan, executable SSpec, and mirrored manual; no broader workflow skill/command files required changes.
- verify: Working/staged direct-runtime guards pass and `doc/06_spec` contains zero executable specs; pure-Simple runtime and live T32 evidence remain pending.
- runtime-decision: UI backend discovery needs the current deployed executable path. Existing owner facade checked: `app.io.cli_ops._cli_current_exe_path`; chosen path: export/reuse that pure-Simple facade from `app.ui.backend_loader`; rejected shortcuts: new `rt_*` access, cwd-relative `bin/simple`, raw `.spl` execution, and every Rust-seed fallback.
- post-repair: Installed UI routes resolve the compiled sibling for POSIX, Windows drive, UNC, and bare-PATH launches; GUI and TUI-web live scripts drive production routes; WM leaves focus empty when absent and uses PID + AXWindowNumber for macOS actions.
- review: Higher-capability static review accepted code, docs, architecture, and static evidence contracts with no P1/P2 findings.
- blocker: Overall PASS remains unavailable until a fresh permitted session runs the pure-Simple live/runtime gate and captures T32 GUI evidence; this session's runtime retry cap is exhausted and Rust remains bootstrap-only.
- docs: Refreshed `doc/05_design/ui_cli_llm_access.md`, `doc/07_guide/app/ui/ui_cli_llm_access.md`, and `.claude/skills/spipe.md` with compiled-artifact proof, fresh-session retry, blocked-handoff, and Rust-seed-only rules; removed a stale committed conflict block from the touched SPipe skill.
