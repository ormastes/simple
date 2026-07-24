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
| `29f6edea49db` | Pushed to `origin/main` (rebased form of local `89b5e9e403b0`) | UTF-8 raw-key decoder, pure raw-line control reducer, unit/component scenarios, manuals, and trace rows |
| `6413e62312f3` | Pushed to `origin/main` | Direct production hook, config, tool, and TUI component coverage |
| `dbbb79c430e0` | Pushed to `origin/main` | Copied chat/type specs replaced by direct production imports and synchronized manuals |
| `e0d214b8fb0f` | Pushed to `origin/main` | Injected TUI I/O boundary, lifecycle-safe routing, unit/runtime specs, and fail-closed live-PTY foundation |
| `0ac4a158e3e3` | Pushed to `origin/main` | Installed-Claude offline compatibility probe, registry-derived hidden/disabled matrix, and PTY artifact provenance/teardown hardening |
| `544c57bcc94a` | Pushed to `origin/main` | Real-TUI default/enabled/disabled hidden admission, explicit child-exit evidence, credential isolation, and synchronized plans/manuals |
| `4556cbbebb6a` | Pushed to `origin/main` | Parts-bin 14-record hidden-stub registry, normalized source-completeness SSpec/manual, architecture/design boundaries, and trace/plan updates |
| `1c110455fef2` | Pushed to `origin/main` | Parts-bin 33-record owner/spec/state map, applicability shapes and outcome probes, generic root reconciliation, `/compact` drift, exact malformed-map rejection, synchronized manual, and plan/trace updates |
| `be28b8d9acdf` | Pushed to `origin/main` | Focused Claude gate owners, real Tasks V2 hook/store model, 73 synchronized owner scenarios, and canonical manual cleanup |
| `a758d7946520` | Pushed to `origin/main` | Deterministic retry loop/effect seam, bounded timing/provider recovery, 15 synchronized retry scenarios, and stale-manual removal |
| `80131399ae27` | Pushed to `origin/main` | Shipped promptless root/alias dispatch through pure, injected plain, and TUI submission paths with zero model/persistence evidence |
| `77f0fbd3a3b3` | Pushed to `origin/main` | Four independent fail-closed cached-wrapper PTY cases for compact/summarize/init/bootstrap plus tightened credential scrubbing |

Workspace-relative MCP/LSP symbols and definitions resolve production targets,
so the navigation health condition is met. Diagnostics
still report the deployed runtime's process-spawn deadlock and remain an
executable-verification blocker. Five unrelated GPU/evidence conflicts remain
in the shared working-copy descendant; they are not part of any Caret commit
and must not be resolved, reverted, or included by this lane.

### Current verified evidence

| Gate | Current result | Authority/limit |
|---|---|---|
| Direct Caret trace | PASS: 25/25 files, 7,278/7,278 LOC, 496/496 file-qualified declarations | Static mapping only |
| Unit manual parity | PASS: 62/62 TUI, 22/22 raw-input, 20/20 runtime, 57/57 main, 12/12 config, 37/37 tools, 24/24 chat, and 14/14 types bodies match source | Zero executed scenarios |
| Component manual parity | PASS: 10/10 TUI/hidden scenario bodies match source, including default-hidden, admitted-hidden, and disabled alias submission with zero responder/persistence | Zero executed scenarios |
| PTY manual parity | PASS: 7/7 live-terminal scenario bodies match source | Static synchronization; checker/SSpec not executed on a qualified artifact |
| Installed-Claude offline probe | PASS: 6/6 cases against Claude Code `2.1.218` (`71abaff5…`): provenance, version, help, missing input, help-hidden `--max-turns`, and removed `--max-tokens` | Real installed-binary checker executed with isolated HOME/config, closed stdin, no prompt, and no inherited provider credentials; SSpec/docgen still blocked |
| Root-registry manual parity | PASS: 5/5 scenario bodies match source, including the production-derived exhaustive matrix | Static synchronization; no CLI/TUI invocation claim |
| Hidden-stub manual parity | PASS: 1/1 scenario body and the complete supporting-helper block match source | Static synchronization; SSpec/docgen not executed on a qualified runtime |
| Feature-gate manual parity | PASS (static): 33/33 owner rows, 33/33 independently pinned contract rows, 33/33 state rows, and 3/3 complete folded executable scenario bodies | SSpec/docgen cannot execute until a qualified runtime exists |
| Focused modern SSpec scan | PASS (static): 495 modern `should` examples across the listed files (407 base plus 88 focused owner/effect examples), canonical matchers, and no placeholder pass | Static source/manual scan only except for the six-case installed-Claude shell checker |
| Direct environment guard | PASS in working and staged modes | Changed Caret paths only |
| Numbered-artifact guard | WARN in this jj workspace: both modes emit Git-worktree/`--cached` errors but still print `OK` and exit zero | Not authoritative here; no numbered artifacts are added by this tranche |
| Generated-spec layout | PASS: zero `.spl` specs under `doc/06_spec` | Layout only |
| Claude CLI declaration reachability | PASS: no unreferenced declaration in `claude_cli.spl` | Source-level reachability |
| Direct `simple check` | FAIL before Caret validation: unknown `rt_process_spawn_guarded` extern | Deployed runtime mismatch |
| Simple LSP MCP | Workspace-relative symbols returned the complete production root registry and definition resolved exactly to `commands.spl:44` | Navigation health confirmed |
| Simple MCP codebase query | Hybrid query reached the LSP workspace-symbol path but exceeded the existing 100 MB watchdog and exited 992 | Broader MCP search/diagnostic execution still blocked; not a Caret PASS |
| Focused SSpec execution | Not executed on a qualified runtime | Required before production PASS |
| Live PTY TUI evidence | Six-scenario fail-closed checker, modern SSpec, and synchronized manual now exist, including `REQ-LLM-CARET-HIDDEN-008` default/enabled/disabled hidden admission; execution is still missing because no cached Caret artifact is deployed | Required before production PASS; artifacts are reserved under `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty/` |
| Current Claude parity | Unprovable: pinned upstream source tree is absent | Historical matrices only |

### Direct-function coverage closure

The settled-tree audit found 22 production declarations without a focused
behavioral assertion. Parallel lanes closed 16 of those gaps with direct
production imports and real assertions. Six terminal-loop declarations remain
uncovered even though every declaration is present in the static inventory.

| Closed lane | Newly covered declarations | Evidence added |
|---|---|---|
| TUI pure/component | `_visible_content`, `_status_line`, `_hint_line` | Tail/fixed viewport, waiting/status composition, and follow/scrolled hints |
| Main startup/hooks | `_resolve_workspace`, `_build_policy`, `_slash_on_model`, `_slash_on_sessions`, `_hidden_commands_enabled`, `_slash_on_resume`, `_on_persist`, `_build_session_hooks` | Isolated PWD/HOME/env/session fixtures and every production `SessionHooks` callback |
| Config defaults | `config_loaded`, `config_default_provider`, `config_claude_cli_model` | The copied config implementation was removed; 12 scenarios now import the production module |
| Glob/list tools | `_glob_match`, `exec_glob`, `exec_list_dir` | Bounded workspace results, rejection paths, empty directories, and repeated-suffix matching |

The new repeated-suffix assertions exposed and drove a production fix in
`_glob_match`: the matcher now uses bounded last-star backtracking rather than
accepting only the first suffix occurrence.

| Remaining lane | Uncovered declarations | Required proof |
|---|---|---|
| TUI live terminal and routing | `caret_chat`, `_inner_height`, `_draw_frame`, `_read_line`, `run_chat_tui`, `run_chat_plain`, plus the new `CaretIo` adapter owner | Component execution through injected I/O plus cached-artifact PTY evidence for renderer selection, raw-mode entry/read/submit/exit/cleanup, frame flush, one-snapshot resize, and plain/TUI routing |

### False-evidence cleanup

The config, chat, and types lanes removed their inline parser/state/model
copies. Their specs now import and exercise the production modules directly,
with synchronized 12-, 24-, and 14-scenario manuals.

The direct coverage does not settle API ownership. Fourteen history/system/JSON
state APIs in `chat.spl` remain orphaned from current CLI/TUI production call
paths, which carry explicit message arrays instead. Do not delete these or
other public-looking declarations solely because repository references are
absent; first classify compatibility/API ownership and record the decision.
The earlier read-only audit identified 47 deletion candidates across the
legacy chat-state island, config accessors, `jo4`/`jo5`, and type constructors,
but the config/type candidates now have real production behavior evidence.
Deletion remains a separate reviewed refactor rather than assumed hardening
work.

These direct imports close the identified copied-test evidence gap; they do not
by themselves prove live terminal behavior.

### Parallel continuation lanes

The best model owns interfaces and final review. Sidecars must use the frozen
`should` convention, canonical matchers, real assertions, and fail-closed
fixtures. No lane may run a paid provider.

| Lane | Owned files | Work | Exit criteria |
|---|---|---|---|
| A — TUI component | `test/01_unit/app/llm_caret/chat_tui_spec.spl` | Complete: pure viewport/status/hint and promptless root-command behavior | Production imports; no inline copies; 62-body manual synchronized |
| B — main/config | `test/01_unit/app/llm_caret/main_spec.spl`, `config_spec.spl` | Complete: real startup hooks and default branches with isolated env/session fixtures | Host env restored; filesystem confined to `build/tmp`; 57/12-body manuals synchronized |
| C — tools | `src/app/llm_caret/tools.spl`, `test/01_unit/app/llm_caret/tools_spec.spl` | Complete statically: production glob matcher/executor and list-dir result assertions | Workspace bounded; matcher defect fixed; 37-body manual synchronized |
| D — live TUI | `scripts/check/check-llm-caret-tui-pty.shs`, focused PTY system spec, manual, plan, and trace rows | Implemented fail-closed: clean-source/runtime-hashed cached `bin/caret` only, dummy provider, forced/auto/piped routing, EOF/Ctrl-C/Ctrl-D, UTF-8/edit/navigation, 12x50 geometry, default/enabled/disabled hidden admission, four promptless canonical/alias cases, raw failure before ANSI, and pre/post `stty` evidence | Static/script validation first; seven-scenario real PTY gate on a qualified cached runtime; terminal restored after every modeled outcome |
| E — installed Claude CLI | installed checker, focused system spec/manual, trace rows | Executed PASS: six bounded offline probes record executable provenance and validate advertised flags, variadic allowed tools, hidden-but-accepted `--max-turns`, and removed `--max-tokens`, with no submitted prompt or inherited provider credentials | Retain the recorded version/hash and never generalize the result to authenticated/provider/session parity |
| F — hidden registry matrix | root command registry spec/manual | Implemented statically: derive lookup, alias, admission, visibility, hidden, and disabled coverage from every production registry record | Execute on a qualified runtime; TUI process contract is covered by lane D, while non-TUI CLI invocation remains separate |
| G — distributed hidden-stub aggregate | `src/app/llm_caret/claude_full/commands/hidden_stub_registry.spl`, mirrored focused SSpec/manual, plan and trace rows | Implemented statically: derive all 14 canonical hidden-disabled stub records from `claude_full` leaf descriptor declarations with `source_id`, `source_file`, `command_name`, `hidden`, and `enabled`; the stale historical feature TSV is not behavioral authority | `ClaudeHiddenStubCommandRecord`, `hiddenDisabledStubCommandRegistry`, `setup_hidden_stub_registry_fixture`, and `check_hidden_stub_registry_contract`; normalized source discovery and two-way registry comparison are present; supporting metadata only with no shipped admission claim; execute SSpec/docgen on a qualified runtime |
| H — distributed feature-gate cross-map | `src/app/llm_caret/claude_full/feature_gate_registry.spl`, mirrored focused SSpec/manual, plan and trace rows | Implemented and statically synchronized: 33 bounded records, independently pinned contract/state matrices, generic root reconciliation, exact malformed rejection, and synchronized manual; execution/docgen remain blocked | `ClaudeFeatureGateRecord`, `claudeFeatureGateRegistry`, `setup_claude_feature_gate_fixture`, `check_claude_feature_gate_registry`, and the independent exact state matrix; preserve `/compact` drift; reject malformed records exactly; parts-bin claim only; execute SSpec/docgen on a qualified runtime |
| Merge owner | current primary agent | Reconcile source/manual bodies, trace rows, and shared maps; commit exact Caret paths only | No unrelated shared-worktree paths in commit |
| Final reviewer | highest-capability fresh review | Requirement-by-requirement completion audit | Every claimed behavior has executed evidence |

### Remaining CLI-then-TUI sequence after lane H

1. **Lane I — modernize mapped gate-owner specs.** Nine focused files are
   implemented and statically synchronized with frozen `step("...")` names,
   direct owner imports, `REQ-LLM-CARET-HIDDEN-008` traceability, and mirrored
   zero-execution manuals. The aggregate already closes Tasks V2 todo-off/no-team,
   team-memory mixed states, insights disabled metadata, ultrareview's three
   rejected combinations, skill-discovery demo/empty/wrong-type rendering,
   persistent-retry false/true admission, and bridge default-false branches.
   Retain focused-spec modernization plus deeper attachment-UI and retry-loop
   effect evidence, and keep each focused manual body synchronized.

   | Focused file/lane | Current status / remaining exact work |
   |---|---|
   | `hooks/useTasksV2_spec.spl` | Complete statically: 11 modern examples cover last-subscriber cleanup, shared singleton observation, stable/updated snapshots, rewatch/debounce, first fetch, disabled no-op, collapse ownership, visibility/timer/filter behavior, and a mirrored full-scenario manual; the stale source-sentinel mismatch remains explicit non-PASS debt |
   | `utils/agent_swarms_enabled_spec.spl` | Complete statically: three modern examples, frozen ANT/opt-in/killswitch steps, scoped requirement, and mirrored full-scenario manual |
   | `memdir/teamMemPaths_spec.spl` | Complete statically: seven modern examples/steps, requirement traceability, containment/path behavior, and mirrored full-scenario manual |
   | `commands/insights_command_spec.spl` | Complete statically: four modern metadata, thirty-day summary, report/browser-fallback, and rejection scenarios; unsupported execution claims removed |
   | `commands/review_rewind_sandbox_spec.spl` | Complete statically: three frozen-step scenarios, review-only requirement scope, exact `used == limit` false boundary, and mirrored full-scenario manual |
   | `bridge/bridge_small_helpers_spec.spl` | Complete statically: 38 modern examples retained; hidden requirement scoped only to bridge availability and the existing manual synchronized |
   | `commands/bridge_command_spec.spl` | Complete statically: four modern examples, 13 preserved steps plus one fail-closed prerequisite step, scoped requirement, callout-state idempotence, and mirrored full-scenario manual |
   | `components/messages/AttachmentMessage_spec.spl` | Complete statically: direct dispatcher evidence for exact fields, ordered plural skills/demo suppression, and fully redacted disabled/empty/wrong-type results; parts-bin only |
   | `services/api/withRetry_spec.spl` | Complete statically: `RetryEffectTrace` and `RetrySequenceResult` provide deterministic loop/effect seams; 15 modern scenarios cover persistent 429/529 beyond `maxRetries`, exact heartbeat rounding, the nonpersistent `maxRetries + 1` boundary, AWS/GCP cache clearing, stale cooldown, bounded Retry-After/backoff, overflow floor, and thinking-budget rejection. `setup_retry_sequence_fixture`, `run_retry_sequence`, and `check_retry_sequence` are synchronized with the canonical zero-execution manual; the obsolete `doc/06_spec/test/...` mis-mirror and hardcoded 822-line sentinel are removed. |

2. **Lane J — CLI gate admission.** Extend the offline Caret CLI fixture only
   for root registry records that can reach the shipped CLI facade. Prove
   registered/reachable canonical and alias inputs, exact output, exit
   behavior, and no state mutation. Do not treat a `claude_full` gate record as
   shipped reachability or help-menu visibility.
   Current static reachability is deliberately narrow: shipped Caret imports
   only `claude_full.commands`; `/compact`, `/summarize`, `/init`, and
   `/bootstrap` can reach shared promptless plain/TUI slash dispatch and return
   the exact unimplemented response, but the shipped Caret CLI/TUI entry graph
   does not call `compactCommand` or `useNewInitPrompt`. Add unit dispatch
   assertions first, then cached offline `--plain` stdin cases with exit `0`,
   exact output, and zero provider invocation. All 33 distributed feature-gate
   dimensions remain parts-bin-only until a real shipped import/call path
   exists; only the compact/init root metadata and aliases are reachable here.
   The pure-dispatch, injected plain-loop, and TUI-submission component portion
   is complete and statically synchronized; cached-wrapper process execution
   remains blocked.

   The frozen promptless-command test contract is:

   - `CaretPromptlessCommandCase(input, canonical, expected_message)`;
   - `setup_promptless_command_cases`;
   - `check_promptless_dispatch`;
   - `Load the accepted promptless command aliases`;
   - `Dispatch the command through the shipped Caret path`;
   - `Check canonical output and zero model submission`.

   The four accepted inputs are `/compact`, `/summarize`, `/init`, and
   `/bootstrap`; aliases must canonicalize to `/compact` and `/init`
   respectively. First add exact pure-dispatch and TUI-submission assertions to
   `chat_tui_spec.spl`, then add an injected-`CaretIo` plain-loop assertion to
   `chat_tui_runtime_spec.spl`. Pure dispatch and TUI submission must directly
   preserve conversation/session state; the plain loop must prove preservation
   through the same non-mutating dispatch flags plus zero responder/persistence
   calls. Every path produces the exact
   `Command not implemented in Caret: /<canonical>` text. The cached-wrapper
   `--plain` stdin process case remains fail-closed pending a qualified Caret
   artifact; do not convert the injected component result into a process PASS.
3. **Lane K — TUI visibility and dispatch.** After the CLI contract is stable,
   project the reachable cases through injected `CaretIo`, then the qualified
   cached-wrapper PTY checker. For compact/init, capture only static
   canonical/alias admission, the exact unimplemented output,
   transcript/status effects, and terminal restoration; their conditional
   owner gates are not shipped call paths. Default/enabled/disabled state
   testing remains scoped to the separate shipped hidden/disabled root-command
   lane. No source fallback, provider credentials, or paid request.
   For the four reachable compact/init canonical/alias inputs, assert exact
   system output, unchanged conversation state, and
   `submitted_to_model=false`; extend PTY evidence only after those injected
   component cases are stable.

   The cached-wrapper checker extension uses `--case promptless` and four
   independent fail-closed PTY labels:
   `promptless-compact`, `promptless-summarize`, `promptless-init`, and
   `promptless-bootstrap`. Each case sends exactly one slash input followed by
   `/exit`, asserts the canonical System transcript (`/compact` for the first
   two, `/init` for the latter two), and must independently preserve the
   existing exit-zero, ANSI, cursor, alternate-screen, geometry, and terminal
   restoration gates. The system SSpec adds one scenario using the existing
   `Open the caret TUI`, `Send a prompt through the visible input`, and
   `Check transcript and status` steps. Missing cached artifacts remain a hard
   failure; no case may skip or fall back to source execution.
   The checker/spec/manual portion is complete and statically synchronized at
   seven PTY scenarios; execution remains blocked on the qualified cached
   artifact.
4. **Lane L — completion audit.** Reconcile every accepted record with its
   focused spec, CLI reachability decision (`reachable` or justified parts-bin
   only), TUI reachability decision, manual, and retained execution artifact.
   Restore a pinned upstream snapshot before making exhaustive current-Claude
   claims.

   Current audit result: the 33 distributed gate dimensions remain
   parts-bin-only; the shipped entry graph reaches only the compact/init root
   records and their summarize/bootstrap aliases. The scoped suite contains 495
   modern scenarios (407 base plus 88 focused owner/effect scenarios), and the
   PTY manual contains seven fail-closed scenarios with zero executed. Simple
   LSP MCP returns the `commands.spl` symbol inventory and resolves the
   `chat_tui.spl` `findRootCommand` call to its production definition. GitHub
   sync is healthy. Execution/release completion is still blocked by the absent
   self-hosted Simple/Caret artifacts and missing pinned upstream Claude tree;
   no exhaustive “every Claude function still works” or runtime PASS is
   claimed.

### 2026-07-24 parallel-audit continuation

The latest sidecar audit found new work rather than changing the evidence
boundary above. The current tranche closes two of those findings:

- the installed Claude Code `2.1.218` probe now distinguishes advertised,
  help-hidden-but-accepted, and removed flags; all six offline cases pass;
- the hidden-command component spec now drives `/debug_tool_call` and
  `/remote_setup` through `run_chat_tui_submission`, proving exact transcript,
  unchanged state, and zero responder/persistence in default-hidden,
  admitted-hidden, and disabled states;
- `_hidden_commands_enabled` now has direct negative evidence for empty, `0`,
  `false`, `yes`, and whitespace-wrapped input, while `1` and case-insensitive
  `true` remain the only admitted values.

Remaining work is ordered by shipped-path value and prerequisite cost:

| Lane | Remaining work | Acceptance |
|---|---|---|
| M — cached plain process | Add four fail-closed `--plain` stdin cases for `/compact`, `/summarize`, `/init`, and `/bootstrap` | Exact canonical output, exit zero, no assistant/unknown extra output, and no session file under isolated HOME |
| N — PTY negative effects | Tighten promptless PTY checks and add hidden aliases plus false env value | Reject extra semantic output, require empty session directory, preserve terminal cleanup for every case |
| O — registry discovery | Add independent source-to-registry discovery for distributed gates | A newly added source gate without a registry row makes the aggregate fail |
| P — direct owner closure | First add behavior tables for `withRetry.isFastModeNotEnabledError`, `shouldRetry`, and `getRetryAfterMs`; then design deterministic seams for MCP auth/client and bridge lifecycle owners | Direct owner import, effect/state assertions, canonical manual; never add constant-only sentinel tests |
| Q — current Claude inventory | Restore a provenance-pinned upstream tree and regenerate file/function matrices | Every current upstream target has an explicit implemented/tested, justified parts-bin, or missing status |
| R — executable Caret | Qualify a current pure-Simple runtime, build cached Caret, and execute focused SSpec/docgen/PTY exactly once | Provenance sidecar, no seed/source fallback, trustworthy example count/exit, retained artifacts |

Runtime recovery remains resource-gated. The worktree has no qualified
runtime/Caret artifact, the shared volume had only about 1.6 GiB free during
the audit, and concurrent bootstrap/native builds were active. Do not start
another build until they finish and at least 5 GiB is free. The sibling
19.7 MB pure-Simple candidate has SHA-256
`09b1ed4583d5b563360af7c4c00b1ef681e09048451279d64ca98c7e4c65549f`
but lacks fresh source provenance; qualify it against current Caret source
before use. Reject the sibling 58 MB candidate because it delegates to a
`simple_seed`, and do not use Stage 3 as a general test/docgen runtime.

### Required execution order after a qualified runtime is deployed

Run each command at most once after its inputs change. Stop on the first
runtime/toolchain mismatch and record it; do not repeat a green gate.

1. Confirm `bin/simple check src/app/llm_caret/tui_input.spl` reaches and passes
   semantic validation.
2. Confirm LSP symbols, definition, references, and diagnostics return
   non-empty/meaningful results for `step_raw_line_byte`.
3. The installed-Claude offline checker already passed all six cases against
   recorded Claude Code `2.1.218`; execute only its SSpec wrapper once after a
   qualified runtime exists, without repeating the external checker directly.
4. Execute the focused unit specs for `claude_cli`, `provider`, `main`,
   `config`, `tools`, and `chat_tui`.
5. Execute the CLI process, Claude contract, managed-env, root-registry,
   hidden-stub-registry, feature-gate-registry, and TUI/hidden system
   specs in interpreter mode.
6. Execute the native Caret smoke with stub fallback disabled.
7. Run `sh scripts/check/check-llm-caret-tui-pty.shs --case all`, then execute
   `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl`; retain
   typescript, input, driver, geometry, hidden default/enabled/disabled, and
   cleanup evidence. Missing
   `script(1)`, `stty`, or a cached artifact is a failure, not a skip.
8. Regenerate manuals with `spipe-docgen`; require `0 stubs` and exact scenario
   body parity.
9. Re-run direct-env, trace, and `doc/06_spec` layout gates. Run the
   numbered-artifact guard from a Git-backed worktree, or first make it
   jj-aware; its current `OK` after Git errors is not release evidence.
10. Fetch GitHub, rebase/duplicate the scoped commit onto `main@origin`, inspect
   exact changed paths, then push only if the MCP/LSP health condition is met.

### Completion criteria

Caret hardening is not complete until:

- every accepted CLI, TUI, and hidden-feature requirement maps to production
  implementation plus an executed modern SSpec assertion;
- the six remaining live TUI coverage gaps above are closed with PTY evidence
  or explicitly removed through a reviewed API-ownership decision;
- CLI wrapper/process exits and outputs pass on the shipped cached artifact;
- TUI behavior passes both pure reducer tests and real PTY lifecycle tests;
- hidden/disabled/default/enabled states are exercised without paid calls;
- all manuals are generated from the executed specs with zero stubs;
- the deployed self-hosted compiler and Simple MCP/LSP are healthy;
- a restored pinned Claude source snapshot supports any claim that every
  current Claude function is mapped and still works.

Until those conditions hold, report the status as **in progress / executable
verification blocked**, never as full Claude parity or production readiness.
