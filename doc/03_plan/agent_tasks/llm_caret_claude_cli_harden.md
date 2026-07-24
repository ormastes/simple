# LLM Caret Claude CLI Harden - Agent Tasks

Date: 2026-07-05
Updated: 2026-07-07 (retargeted from trace-checker to shipped-path robustness)

## Reset (2026-07-07)

The prior tasks scoped "harden" to a traceability/mapping checker
(`check-llm-caret-claude-cli-trace.shs`) that verifies file/LOC/symbol-name
presence in a report. That is a **documentation-coverage** gate, not robustness.
Real hardening targets the **shipped path** (`src/app/llm_caret/*.spl`, ~3,086
LOC that actually runs), not the `claude_full/` island (unreferenced, no
`fn main`). Design: `doc/05_design/llm_caret_claude_cli_harden.md`.

## Quality Gate (every task)

Interpreter-mode file-load "PASS" is **insufficient** (`.claude/rules/testing.md`:
the runner may not execute `it` blocks). Each acceptance test below must run in
an `it`-executing mode against the fault it is meant to survive, with the true
assertion-level result recorded. Assert on behavior (spawn spy, attempt counter,
transcript scan), not struct fields.

## Tasks (P0 first)

1. **Retry/backoff/timeout** (P0).
   - Scope: `with_retry` around `dispatch_send`; per-attempt timeout on every
     `rt_http_request`/`rt_process_run`; retryable-vs-terminal error type.
   - Files: `provider.spl`, `claude_api.spl`, `claude_cli.spl`, `openai_api.spl`.
   - Acceptance: it-block — 429-then-200 recovers (assert attempts);
     persistent-500 returns terminal error; hung subprocess killed at timeout.
   - Exit: no transient failure surfaces raw; no unbounded subprocess wait.

2. **Secret redaction** (P0).
   - Scope: redaction pass before any logging/JSONL persist of request/response
     bodies (strip `Authorization`, `sk-`/API-key patterns).
   - Files: `provider.spl`, `chat.spl`.
   - Acceptance: it-block — a persisted transcript contains no raw API key.
   - Exit: secrets never reach transcripts/logs.

3. **Injection defense** (P0).
   - Scope: tag/wrap untrusted tool output (WebFetch, file content) before it
     re-enters message history.
   - Files: WebFetch/file-read executors, `chat.spl`.
   - Acceptance: it-block — fetched content is wrapped/tagged in history.
   - Exit: tool output cannot silently steer the loop.

4. **Permission gating** (P0).
   - Scope: single `permission_gate(mode,tool,input)` every tool call traverses
     before execution (allow/ask/deny).
   - Files: dispatch/gate module; wire `bridge/bridgePermissionCallbacks.spl`
     structs; hook into `provider.spl`.
   - Acceptance: it-block — denied Bash does NOT spawn (spawn spy); allowed does;
     nothing executes ungated.
   - Exit: no ungated tool execution.

5. **Crash resilience** (P1).
   - Scope: per-turn JSONL persist + subprocess timeout + top-level error
     boundary with recovery marker.
   - Files: `chat.spl`, `provider.spl`, `claude_cli.spl`.
   - Acceptance: it-block — simulated mid-turn kill; `--resume` recovers
     completed turns.
   - Exit: a crash loses at most the in-flight turn.

6. **Observability** (P1).
   - Scope: structured JSON-lines events around `dispatch_send` (latency, error
     class, retry decisions, token/cost).
   - Files: new logging helper; `provider.spl`.
   - Acceptance: it-block — one dispatch emits an event with all fields.
   - Exit: NFR-LLM-CARET-FULL-004 met.

## Legacy Trace Gate (retained, docs-coverage only)

Keep `scripts/check/check-llm-caret-claude-cli-trace.shs` and
`test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl` as a
documentation-coverage signal only. They must NOT be cited as evidence that any
task above is complete — remove any LOC>=source (size-parity) condition from the
checker so it stops rewarding comment padding.

## Lanes

- P0 tasks (1-4): highest-capability implementer + security review before close.
- P1 tasks (5-6): standard implementer + merge review.
- Final reviewer verifies each acceptance it-block actually executed (not
  file-load PASS) before release.

## 2026-07-24 CLI-to-TUI Hardening Checkpoint

This section is the authoritative continuation plan for the current hardening
session. The broader tasks above remain requirements; this checkpoint records
what is saved, what is proved, and what is still missing. Do not interpret a
source/manual or traceability PASS as executable behavior evidence.

### Saved changes

| Commit | GitHub state | Scope |
|---|---|---|
| `139f60c83ffb` | Pushed to `origin/main` | Claude stream validation, TUI input/session hardening, and focused tests |
| `6dd31ca4ca7b` | Pushed to `origin/main` | Cached production wrapper, complete focused maps, hidden environment-key checks, and synchronized manuals |
| `89b5e9e403b0` | Local commit; intentionally not pushed | UTF-8 raw-key decoder, pure raw-line control reducer, 15 unit scenarios, one component system scenario, manuals, and trace rows |

The last commit is based on the current `main` parent but remains unbookmarked
because the requested push condition is not satisfied: the MCP transport
responds, while Simple LSP navigation returns empty results and diagnostics
reports the deployed runtime's process-spawn deadlock. Fetch completed with no
remote changes. Five unrelated GPU/evidence conflicts remain in the shared
working-copy descendant; they are not part of any Caret commit and must not be
resolved, reverted, or included by this lane.

### Current verified evidence

| Gate | Current result | Authority/limit |
|---|---|---|
| Direct Caret trace | PASS: 24/24 files, 7,160/7,160 LOC, 479/479 declarations | Static mapping only |
| Unit manual parity | PASS: 79/79 TUI scenario bodies match source | Zero executed scenarios |
| Component manual parity | PASS: 9/9 TUI/hidden scenario bodies match source | Zero executed scenarios |
| Focused modern SSpec scan | PASS: canonical `should` examples and matchers; no placeholder pass | Static source scan |
| Direct environment guard | PASS in working and staged modes | Changed Caret paths only |
| Numbered-artifact guard | PASS in working and staged modes | Changed Caret paths only |
| Generated-spec layout | PASS: zero `.spl` specs under `doc/06_spec` | Layout only |
| Claude CLI declaration reachability | PASS: no unreferenced declaration in `claude_cli.spl` | Source-level reachability |
| Direct `simple check` | FAIL before Caret validation: unknown `rt_process_spawn_guarded` extern | Deployed runtime mismatch |
| Simple LSP MCP | Transport responds; symbols/definition empty; diagnostics unavailable | Not healthy enough for push condition |
| Focused SSpec execution | Not executed on a qualified runtime | Required before production PASS |
| Live PTY TUI evidence | Missing | Required before production PASS |
| Current Claude parity | Unprovable: pinned upstream source tree is absent | Historical matrices only |

### Remaining direct-function coverage

The settled-tree audit found 22 production declarations without a focused
behavioral assertion. These declarations remain uncovered even though every
declaration is present in the static trace inventory.

| Lane | Uncovered declarations | Required proof |
|---|---|---|
| TUI pure/component | `_visible_content`, `_status_line`, `_hint_line`, `caret_chat` | Direct production imports; viewport/status/hint values and renderer-route decisions |
| TUI live terminal | `_inner_height`, `_draw_frame`, `_read_line`, `run_chat_tui`, `run_chat_plain` | PTY-driven raw-mode entry/read/submit/exit/cleanup, frame flush, resize, and plain/TUI routing |
| Main startup/hooks | `_resolve_workspace`, `_build_policy`, `_slash_on_model`, `_slash_on_sessions`, `_hidden_commands_enabled`, `_slash_on_resume`, `_on_persist`, `_build_session_hooks` | Production callbacks with isolated env/files/session fixtures; no duplicate fake implementation |
| Config defaults | `config_loaded`, `config_default_provider`, `config_claude_cli_model` | Import production module and observe unset/set/default paths |
| Glob tool | `_glob_match`, `exec_glob` | Direct matching edge cases plus bounded workspace fixture and result semantics |

`exec_list_dir` is reached through the agent loop but its result semantics are
not asserted; add a behavioral assertion while working in the tool lane.

### False-evidence cleanup

The following existing specs exercise inline reimplementations rather than the
production modules and therefore cannot close production coverage:

- `test/01_unit/app/llm_caret/chat_spec.spl`
- `test/01_unit/app/llm_caret/config_spec.spl`
- `test/01_unit/app/llm_caret/types_spec.spl`

Replace copied helpers with production imports where the API remains required.
Do not delete public-looking declarations solely because current repository
references are absent; first classify compatibility/API ownership and record
the decision. The read-only audit identified 47 deletion candidates across the
legacy chat-state island, config accessors, `jo4`/`jo5`, and unused type
constructors, but deletion is a separate reviewed refactor rather than assumed
hardening work.

### Parallel continuation lanes

The best model owns interfaces and final review. Sidecars must use the frozen
`should` convention, canonical matchers, real assertions, and fail-closed
fixtures. No lane may run a paid provider.

| Lane | Owned files | Work | Exit criteria |
|---|---|---|---|
| A — TUI component | `test/01_unit/app/llm_caret/chat_tui_spec.spl` | Cover pure viewport/status/hint behavior and renderer routing that does not require a terminal | Production imports; no inline copies; manual synchronized |
| B — main/config | `test/01_unit/app/llm_caret/main_spec.spl`, `config_spec.spl` | Cover real startup hooks and default branches with isolated env/session fixtures | Host env restored; filesystem confined to `build/tmp`; manuals synchronized |
| C — tools | `test/01_unit/app/llm_caret/tools_spec.spl` | Cover production glob matcher/executor and strengthen list-dir result assertions | Workspace bounded; no shell wildcard dependence; manual synchronized |
| D — live TUI | new focused PTY system spec and plan/manual | Drive `run_chat_tui`, `_read_line`, redraw, resize, EOF/Ctrl-C/Ctrl-D, and cleanup | Real PTY evidence on qualified runtime; terminal restored after every outcome |
| Merge owner | current primary agent | Reconcile source/manual bodies, trace rows, and shared maps; commit exact Caret paths only | No unrelated shared-worktree paths in commit |
| Final reviewer | highest-capability fresh review | Requirement-by-requirement completion audit | Every claimed behavior has executed evidence |

### Required execution order after a qualified runtime is deployed

Run each command at most once after its inputs change. Stop on the first
runtime/toolchain mismatch and record it; do not repeat a green gate.

1. Confirm `bin/simple check src/app/llm_caret/tui_input.spl` reaches and passes
   semantic validation.
2. Confirm LSP symbols, definition, references, and diagnostics return
   non-empty/meaningful results for `step_raw_line_byte`.
3. Execute the focused unit specs for `claude_cli`, `provider`, `main`,
   `config`, `tools`, and `chat_tui`.
4. Execute the CLI process, Claude contract, managed-env, and TUI/hidden system
   specs in interpreter mode.
5. Execute the native Caret smoke with stub fallback disabled.
6. Execute the live PTY TUI spec and retain terminal capture/cleanup evidence.
7. Regenerate manuals with `spipe-docgen`; require `0 stubs` and exact scenario
   body parity.
8. Re-run direct-env, numbered-artifact, trace, and `doc/06_spec` layout gates.
9. Fetch GitHub, rebase/duplicate the scoped commit onto `main@origin`, inspect
   exact changed paths, then push only if the MCP/LSP health condition is met.

### Completion criteria

Caret hardening is not complete until:

- every accepted CLI, TUI, and hidden-feature requirement maps to production
  implementation plus an executed modern SSpec assertion;
- the 22 direct coverage gaps above are closed or explicitly removed through a
  reviewed API-ownership decision;
- CLI wrapper/process exits and outputs pass on the shipped cached artifact;
- TUI behavior passes both pure reducer tests and real PTY lifecycle tests;
- hidden/disabled/default/enabled states are exercised without paid calls;
- all manuals are generated from the executed specs with zero stubs;
- the deployed self-hosted compiler and Simple MCP/LSP are healthy;
- a restored pinned Claude source snapshot supports any claim that every
  current Claude function is mapped and still works.

Until those conditions hold, report the status as **in progress / executable
verification blocked**, never as full Claude parity or production readiness.
