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
| `7767e3dba6c2` | Pushed to `origin/main` | Installed Claude hidden-argument proof, explicit hidden env matrix, and hidden/disabled alias submission with zero responder/persistence |
| `39898a30c30a` | Pushed to `origin/main` | Promptless cached-wrapper TUI/plain cases, direct retry-owner coverage, hidden help exclusions, and synchronized plan/manual repair |

Workspace-relative MCP/LSP symbols and definitions resolve production targets,
so the navigation health condition is met. Diagnostics
still report the deployed runtime's process-spawn deadlock and remain an
executable-verification blocker. Five unrelated GPU/evidence conflicts remain
in the shared working-copy descendant; they are not part of any Caret commit
and must not be resolved, reverted, or included by this lane.

### Current verified evidence

| Gate | Current result | Authority/limit |
|---|---|---|
| Direct Caret trace | PASS (independent final reconciliation): 25/25 files, 7,198/7,198 LOC, 506/506 file-qualified declarations after the bounded-draw helper landed | The checker passed before the final security refactor and was not rerun, per the one-green-run session guard |
| Unit manual parity | PASS: 62/62 TUI, 22/22 raw-input, 22/22 runtime, 64/64 main, 16/16 config, 36/36 provider, 15/15 OpenCode, 9/9 local-Torch, 37/37 tools, 24/24 chat, and 14/14 types bodies match source | Zero executed scenarios |
| Component manual parity | PASS: 10/10 TUI/hidden scenario bodies match source, including default-hidden, admitted-hidden, and disabled alias submission with zero responder/persistence | Zero executed scenarios |
| PTY manual parity | PASS: 7/7 live-terminal scenario bodies match source | Static synchronization; checker/SSpec not executed on a qualified artifact |
| Installed-Claude offline probe | PASS: 6/6 cases against Claude Code `2.1.218` (`71abaff5…`): provenance, version, help, missing input, help-hidden `--max-turns`, and removed `--max-tokens` | Real installed-binary checker executed with isolated HOME/config, closed stdin, no prompt, and no inherited provider credentials; SSpec/docgen still blocked |
| Root-registry manual parity | PASS: 5/5 scenario bodies match source, including the production-derived exhaustive matrix | Static synchronization; no CLI/TUI invocation claim |
| Hidden-stub manual parity | PASS: 1/1 scenario body and the complete supporting-helper block match source | Static synchronization; SSpec/docgen not executed on a qualified runtime |
| Feature-gate manual parity | PASS (static): 33/33 owner rows, 33/33 independently pinned contract rows, 33/33 state rows, and 4/4 complete folded executable scenario bodies; bounded import-frontier discovery resolves 33 unique physical source/owner edges | This catches imported-registry drift only, not arbitrary unimported or upstream-only gates; SSpec/docgen cannot execute until a qualified runtime exists |
| Curated SSpec scan | PASS (static): 622 `should` examples across the CLI/TUI/owner cohort (531 base plus 91 focused owner/effect examples), canonical matchers, and no placeholder pass | This is a scenario count, not a claim that all 622 use frozen `step(...)` flows; static source/manual scan only except for the six-case installed-Claude shell checker |
| Direct environment guard | PASS in working and staged modes | Changed Caret paths only |
| Numbered-artifact guard | WARN in this jj workspace: both modes emit Git-worktree/`--cached` errors but still print `OK` and exit zero | Not authoritative here; no numbered artifacts are added by this tranche |
| Generated-spec layout | PASS: zero `.spl` specs under `doc/06_spec` | Layout only |
| Claude CLI declaration reachability | PASS: no unreferenced declaration in `claude_cli.spl` | Source-level reachability |
| Direct `simple check` | FAIL before Caret validation: unknown `rt_process_spawn_guarded` extern | Deployed runtime mismatch |
| Simple LSP MCP | Workspace-relative symbols returned the complete production root registry and definition resolved exactly to `commands.spl:44` | Navigation health confirmed |
| Simple MCP codebase query | Hybrid query reached the LSP workspace-symbol path but exceeded the existing 100 MB watchdog and exited 992 | Broader MCP search/diagnostic execution still blocked; not a Caret PASS |
| Focused SSpec execution | Not executed on a qualified runtime | Required before production PASS |
| Live PTY TUI evidence | Seven-scenario fail-closed checker, modern SSpec, and synchronized manual now exist, including `REQ-LLM-CARET-HIDDEN-008` canonical/alias admission for default, enabled, disabled, and explicit-false environment states; execution is still missing because no cached Caret artifact is deployed | Required before production PASS; artifacts are reserved under `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty/` |
| Current Claude parity | Unprovable: pinned upstream source tree is absent | Historical matrices only |

### Direct-function coverage closure

The original settled-tree audit found 22 declarations without a focused
behavioral assertion. Subsequent injected-runtime work closed the old six-item
TUI row: `caret_chat`, `_inner_height`, `_draw_frame`, `_read_line`,
`run_chat_tui`, and `run_chat_plain` are now called directly by
`chat_tui_runtime_spec.spl`. The remaining direct TUI acceptance gap is the real
`production_caret_io` boundary plus execution of the provenance-checked cached
wrapper.

| Closed lane | Newly covered declarations | Evidence added |
|---|---|---|
| TUI pure/component | `_visible_content`, `_status_line`, `_hint_line` | Tail/fixed viewport, waiting/status composition, and follow/scrolled hints |
| Main startup/hooks | `_resolve_workspace`, `_build_policy`, `_slash_on_model`, `_slash_on_sessions`, `_hidden_commands_enabled`, `_slash_on_resume`, `_on_persist`, `_build_session_hooks` | Isolated PWD/HOME/env/session fixtures and every production `SessionHooks` callback |
| Config defaults | `config_loaded`, `config_default_provider`, `config_claude_cli_model` | The copied config implementation was removed; 12 scenarios now import the production module |
| Glob/list tools | `_glob_match`, `exec_glob`, `exec_list_dir` | Bounded workspace results, rejection paths, empty directories, and repeated-suffix matching |

The new repeated-suffix assertions exposed and drove a production fix in
`_glob_match`: the matcher now uses bounded last-star backtracking rather than
accepting only the first suffix occurrence.

| Remaining lane | Uncovered declaration/boundary | Required proof |
|---|---|---|
| TUI live terminal and routing | `production_caret_io` and the cached process boundary | Cached-artifact PTY evidence for renderer selection, raw-mode entry/read/submit/exit/cleanup, frame flush, one-snapshot resize, and plain/TUI routing |

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
| D — live TUI | `scripts/check/check-llm-caret-tui-pty.shs`, focused PTY system spec, manual, plan, and trace rows | Implemented fail-closed: clean-source/runtime-hashed cached `bin/caret` only, dummy provider, forced/auto/piped routing, EOF/Ctrl-C/Ctrl-D, UTF-8/edit/navigation, 12x50 geometry, default/enabled/disabled hidden admission, four promptless TUI plus four explicit `--plain` canonical/alias cases, forbidden semantic output/session files, raw failure before ANSI, and pre/post `stty` evidence | Static/script validation first; seven-scenario gate on a qualified cached runtime; terminal restored after every modeled TUI outcome |
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
   | `services/api/withRetry_spec.spl` | Complete statically: `RetryEffectTrace` and `RetrySequenceResult` provide deterministic loop/effect seams; 18 modern scenarios cover persistent 429/529 beyond `maxRetries`, exact heartbeat rounding, the nonpersistent `maxRetries + 1` boundary, AWS/GCP cache clearing, stale cooldown, bounded Retry-After/backoff, overflow floor, thinking-budget rejection, and direct `isFastModeNotEnabledError`/`shouldRetry`/`getRetryAfterMs` owner boundaries. `setup_retry_sequence_fixture`, `run_retry_sequence`, and `check_retry_sequence` are synchronized with the canonical zero-execution manual; the obsolete `doc/06_spec/test/...` mis-mirror and hardcoded 822-line sentinel are removed. |

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
   records and their summarize/bootstrap aliases. The scoped suite contains 622
   curated `should` scenarios (531 base plus 91 focused owner/effect
   scenarios), and the
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
- visible `/help` and root summaries now explicitly exclude both canonical and
  alias spellings of hidden/disabled commands;
- all four promptless commands have fail-closed cached-wrapper designs through
  both real TUI and explicit `--plain` stdin, rejecting unknown/assistant
  output and isolated-HOME session files;
- the three previously unreferenced direct retry owners now have focused
  status/message, default decision, and Retry-After conversion vectors.
- the real-PTY hidden lane now includes canonical and alias spellings across
  default, enabled, disabled, and explicit-`false` environment states;
- the bounded feature-gate discovery oracle resolves all 33 imported owner
  functions to 33 unique physical source/owner edges and rejects either-side
  drift without adding filesystem work to shipped paths;
- the bridge lifecycle model gives all 16 isolated lifecycle owners
  deterministic spawn, heartbeat, cleanup, completion, acknowledgement, retry,
  timeout, stdin, status, and signal state/effect evidence in 26 synchronized
  scenarios;
- the MCP client now has 18 synchronized direct-owner scenarios for terminal
  error classification, connection decisions, per-server cache isolation,
  ordered batch bounds, capability counts, and exactly-one URL elicitation
  retry.

Remaining work is ordered by shipped-path value and prerequisite cost:

| Lane | Remaining work | Acceptance |
|---|---|---|
| M — cached plain process | Complete statically: four fail-closed `--plain` stdin cases for `/compact`, `/summarize`, `/init`, and `/bootstrap` | Execute on the qualified cached artifact; exact canonical output, exit zero, no assistant/unknown output, and no session file under isolated HOME |
| N — PTY negative effects | Complete statically: promptless negative checks plus hidden canonical/alias and false-env cases are represented in the real PTY checker/spec/manual | Execute once on the qualified cached artifact while preserving forbidden-output/session gates and terminal cleanup |
| O — registry discovery | Complete for the bounded imported registry frontier: 33/33 discovered physical source/owner edges and an exact negative drift fixture | Restore a pinned current-upstream tree before claiming discovery beyond the imported frontier |
| P — direct owner closure | Entry, Claude/OpenAI/compatible transports, config, OpenCode, local Torch, provider delegation, retry, MCP client, bridge lifecycle, MCP auth/OAuth, bridge messaging, and structured CLI I/O are complete statically | Remaining behavioral owner work is bridge entry/transport callbacks, MCP result mapping, and pure response-normalization seams; never add constant-only sentinel tests |
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

A later 54,946,360-byte candidate appeared at
`build/bootstrap/full/aarch64-apple-darwin/simple` with SHA-256
`6275039bf1ca469b4255535778935d9f11df51aa374f6d740a9b8fe4a5f67492`.
It is also rejected: no adjacent provenance manifest exists, `simple_seed` is
adjacent, and bounded strings explicitly require/re-spawn the Rust seed through
`SIMPLE_BOOTSTRAP_DRIVER` while embedding `src/compiler_rust/target/bootstrap`
paths. It must not execute Caret tests or docgen.

### 2026-07-25 mapping refresh

The final independent trace reconciliation proves exactly 25/25 files,
7,198/7,198 LOC, and 506/506 declarations after the bounded-draw helper. The
checker itself was not rerun after the final security refactor.
The broader one-shot lexical audit is triage rather
than behavior evidence:

- `claude_full`: 848 source files, 349 specs, 7,009 top-level functions;
  3,007 have no lexical reference and 666 are ledger-named;
- shipped 25-file roots: 447 top-level functions; 168 have no lexical
  reference;
- name collisions, indirect dispatch, ledgers, and constant accessors make
  these counts unsuitable as completion percentages.

The highest shipped-path gaps are now ordered as follows:

1. `main.spl:main` and `tui_io.spl:production_caret_io` through a
   provenance-qualified cached process and PTY;
2. pure response-normalization seams for success/error owner mappings;
3. bridge headless/entry wiring and transport callbacks;
4. MCP result mapping and any OAuth branches not covered by the current direct
   redaction/error/flow/step-up scenarios;
5. a pinned upstream Claude source inventory for exhaustive parity claims.

The exact public `@anthropic-ai/claude-code@2.1.218` tarball was inspected.
SHA-256
`3a434c8bcb493e9ca87315d9aa6064835c5987e8fbc85c181bb76157dd5c45d8`
contains seven package entries and no source tree. It cannot satisfy lane Q.

Parallel direct-owner closure now includes:

- MCP auth: nine synchronized scenarios cover all six credential mutation
  owners, server isolation, idempotence, ordered effects, and fail-closed
  unsupported operations through `McpAuthMutationModel`;
- bridge messaging: ten synchronized scenarios cover bounded UUID ownership,
  discriminants, eligibility/title policy, ingress/deduplication, server
  controls, and stable result construction through real owners plus
  `BridgeMessagingModel`;
- both lanes removed their targeted constant/source-line sentinels and retain
  explicit zero-execution/no-upstream claims.
- structured CLI I/O now has 16 synchronized scenarios over the real
  `StructuredIO` owner; all 13 targeted boolean/source-line sentinels are gone,
  abort and input-close clear all pending state, and ordered input, replay,
  permission, hook, elicitation, sandbox, and MCP outcomes are asserted.
- the MCP-auth lane retains its nine mutation scenarios and adds fifteen direct
  OAuth/redaction/error/provider scenarios; repeated sensitive parameters now
  redact at exact query boundaries without corrupting `upstate`-like names;
- the shipped OpenAI-compatible provider has eleven new injected request and
  completion scenarios, exact URL/header/body/error evidence, malformed content
  type rejection, and a single live `compat_send` build/HTTP/complete path.

The next CLI-first round is frozen as four non-overlapping owners:

- `main.spl`: `run_main_args(raw_args)` owns injected entry orchestration and
  `main()` delegates only process argument acquisition;
- `claude_api.spl`: `ClaudeApiRequest`, `build_claude_api_request`, and
  `complete_claude_api_exchange` own request/completion seams;
- `openai_api.spl`: `OpenAIApiRequest`, `build_openai_request`, and
  `complete_openai_exchange` own request/completion seams;
- `config.spl`: `complete_config_load` owns the file-read completion boundary,
  with real fixture, missing-file, and API-key environment-owner scenarios.

This round must retain exact executable/manual scenario parity and must not
claim a live network, terminal, or provider call.

The round is now integrated statically:

- `main()` delegates once to `run_main_args(get_cli_args())`; six new scenarios
  cover help, unknown option, missing config, invalid provider, missing resume,
  and incompatible Metal GUI exits while checking exact runtime-owner state;
- Claude API has 13 modern scenarios and OpenAI API has 14, each over typed
  request/build/completion seams, URL/body/header escaping, fail-closed
  empty/malformed/fieldless/wrong-type/unterminated content, raw error
  preservation, and retry-preserving send ordering;
- each production send builds once and retains `with_retry`; its callback owns
  one `http_request_raw` expression per attempt, so the evidence does not
  falsely claim one total network attempt;
- config has 16 synchronized scenarios, including a real repository fixture,
  a missing-file rejection, injected empty-content completion, and isolated
  Claude/OpenAI/compatible API-key environment ownership.

The Simple LSP MCP responds, but absolute paths in this goal workspace still
return an empty symbol list and diagnostics report the documented source-mode
`process_run` deadlock. No syntax, runtime, docgen, network, or terminal PASS is
claimed for this round.

The following CLI-owner audit found two additional production ownership gaps:

- `provider.spl` registered `local_torch` but returned “not implemented,” and
  duplicated three HTTP request/parser/retry stacks instead of calling the
  hardened Claude/OpenAI/compatible owners;
- `mod.spl` maintained another private Claude/OpenAI HTTP stack and limited
  direct public send to two CLI providers despite describing a unified API.

The next parallel round freezes these non-overlapping lanes:

- OpenCode: `OpencodeInvocation`, `build_opencode_invocation`, and
  `complete_opencode_process`, with one process call and an offline fixture;
- local torch initially froze path/cleanup seams; security review superseded
  that design with `python_single_quoted`, inline `build_torch_script`, and
  `complete_local_torch_exchange`, eliminating temporary files entirely;
- provider: all backend routing delegates to shipped owner modules, including
  a real `local_torch` route, with no provider-local HTTP/retry/JSON stack;
- public module: `_dispatch_current` routes chat/direct sends through
  `provider.dispatch_send`, retaining public history/session behavior while
  removing the third private provider stack.

That provider round is now integrated statically:

- OpenCode has 15 synchronized scenarios over typed invocation, one process
  call, strict structured parsing, plain-text success, malformed-structure
  rejection, and offline fixture argv behavior;
- local Torch has nine synchronized scenarios over Python quoting, inline
  script construction, one shell-free `python -c` process call, stdout/stderr
  completion, and the absence of temporary-file/cleanup effects;
- provider dispatch now delegates to the Claude, OpenAI, compatible, CLI,
  OpenCode, and local-Torch owners; the duplicated HTTP/retry/JSON stack is
  removed and all 36 provider scenarios are synchronized;
- the public module delegates chat and direct sends through that one provider
  dispatcher and resets provider-specific path, credential, endpoint, system,
  session, turn, and history state during initialization.
- final review replaced OpenCode's brace scan with the shared strict JSON
  parser, made its fixture reject reordered/extra argv, and moved the
  uninitialized public-state scenario before all module initialization;
- local Torch now uses only the process facade and exact argv; the reviewed
  implementation has no shared `/tmp` path, output-file read, symlink target,
  or cleanup branch.

The static curated cohort is now 622 `should` scenarios: 531 base plus 91
focused owner/effect scenarios. This count does not claim universal frozen-step
adoption. Executable verification remains blocked by the absence of a
provenance-qualified pure-Simple runtime and cached Caret.

The remaining provider-test debt is a pure injected normalization seam for
successful Claude/OpenAI/compatible/local owner responses and an unset-safe
credential-environment test seam. Those gaps are recorded rather than hidden
behind source-string assertions.

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
4. Execute the focused unit specs for `claude_cli`, `claude_api`,
   `openai_api`, `openai_compat`, `opencode_cli`, `local_torch`, `provider`,
   `main`, `config`, `tools`, and `chat_tui`.
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
- the remaining `production_caret_io` and cached-process TUI boundaries are
  closed with PTY evidence or explicitly removed through a reviewed
  API-ownership decision;
- CLI wrapper/process exits and outputs pass on the shipped cached artifact;
- TUI behavior passes both pure reducer tests and real PTY lifecycle tests;
- hidden/disabled/default/enabled states are exercised without paid calls;
- all manuals are generated from the executed specs with zero stubs;
- the deployed self-hosted compiler and Simple MCP/LSP are healthy;
- a restored pinned Claude source snapshot supports any claim that every
  current Claude function is mapped and still works.

Until those conditions hold, report the status as **in progress / executable
verification blocked**, never as full Claude parity or production readiness.

### 2026-07-25 TUI component and PTY hardening checkpoint

Completed statically:

- `run_chat_plain` distinguishes `nil` EOF from an empty line and ignores
  blank/whitespace input without discarding later commands;
- `_draw_if_visible` owns row admission for every `_draw_frame` write, with a
  captured five-row terminal fixture;
- the runtime spec/manual are synchronized at 20 scenarios with zero executed;
- the seven PTY scenario labels and frozen steps remain unchanged; the outer
  timeout is 240 seconds for `hidden`/`promptless` and 120 seconds otherwise;
- piped automatic `/exit` requires byte-exact `> ` stdout, empty stderr, zero
  exit, and no ANSI;
- provenance fails closed unless it records `runtime=pure-simple-self-hosted`,
  `runtime_probe=pass`, and `rust_seed_used=false`; timeout cleanup uses bounded
  child rescans.

Remaining, in rank order:

1. Execute `production_caret_io`/`caret_is_tty` and all seven PTY scenarios on
   a provenance-qualified cached Caret artifact.
2. Add bounded bind/router/lifecycle behavior evidence for `run_server`.
3. Add pure injected success-normalization evidence for the
   Claude/OpenAI/compatible/local provider owners.
4. Add bind/request/launch/cleanup evidence for `run_gui`.
5. Exercise the Metal render/submit/present loop on a qualified native host.
6. Restore a pinned upstream Claude source inventory before an exhaustive
   current-function parity claim.

No provenance-qualified self-hosted Caret artifact exists, and no real PTY
scenario has executed; static TUI and checker hardening is not a TUI PASS.

### 2026-08-08 typed terminal lifecycle implementation tranche

The interface is frozen first in
`doc/05_design/llm_caret_claude_cli_harden.md` under **Typed terminal lifecycle
contract**. This tranche is deliberately narrower than PTY execution: it makes
terminal setup and cleanup failures observable through the injected production
boundary without changing provider, command, session, or plain-renderer
contracts.

| Lane | Owned paths | Contract | Completion evidence |
|---|---|---|---|
| A — terminal adapter | `src/app/llm_caret/tui_io.spl` | `CaretTerminalResult`; `CaretIo.begin_tui/end_tui`; production reverse cleanup bookkeeping | adapter has no old lifecycle fields and reports ordered phase/error results |
| B — TUI caller | `src/app/llm_caret/chat_tui.spl` | `run_chat_tui` maps setup/cleanup failures to fixed `CaretLoopResult` reasons and emits success only after cleanup | exactly one begin/end lifecycle invocation per modeled TUI run; plain path makes none |
| C — deterministic proof | `test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl` | fake capability uses the same signature | setup, cleanup, normal exit, and plain routing assertions use no network/provider |
| Merge owner | primary Caret lane | resolve only these three paths plus this plan/manual parity if needed | inspect scoped diff, run focused test once, then update blocker record |
| Final reviewer | highest-capability fresh review | interface adherence and failure-path coverage | reject old-field compatibility shims, duplicated terminal primitives, placeholder assertions, or unrelated changes |

No lower-model sidecar owns shared interfaces: names, field order, result
reasons, and required test cases were frozen by the design commit before the
lanes started. The merge must preserve unrelated shared-worktree changes and
must not claim live PTY execution until the qualified cached artifact exists.

Verification note: the focused runtime spec and its manually synchronized
mirror each define 20 top-level scenarios, including typed terminal lifecycle
and plain hidden-command admission. This is static documentation alignment,
not docgen or executable evidence. A direct run under the available macOS arm64
self-hosted runtime instead fails before all examples: its parser rejects the
canonical `describe "...":`/`it "...":` SSpec grammar. See
`doc/08_tracking/bug/self_hosted_sspec_describe_colon_parser_2026-08-08.md`.
Before an execution claim, deploy the current parser source, record the
resolved spec path/hash, then regenerate the mirrored manual from the repaired
qualified runtime. Do not mark this lane executable-PASS until all assertions
pass.

### Next executable CLI-to-TUI proof: offline Claude cached wrapper

Current parser source already supports canonical SSpec colon blocks through
`try_parse_bare_ident_string_call` and `parse_trailing_colon_block_arg`; the
existing `parse001_spec_files_spec.spl` covers that grammar. The deployed
self-hosted artifact rejecting it is out of provenance and must be rebuilt
before any execution claim. While that rebuild is pending, the next
non-overlapping test slice is frozen as follows:

| Owner | Frozen change |
|---|---|
| `scripts/check/check-llm-caret-tui-pty.shs` | Extend `run_pty_case(label, ui_mode, input_kind, geometry)` to `run_pty_case(label, ui_mode, input_kind, geometry, provider_mode)`. Existing calls pass `dummy`; `offline-claude` passes `fixture-claude`. `fixture-success` feeds `fixture-success` then `/exit`. |
| Wrapper launch | `fixture-claude` uses fixed argv only: cached `bin/caret --config test/fixtures/llm_caret/mock_claude_cli.sdn --provider claude_cli --model sonnet --system "Be concise" --tui`; no shell evaluation, network, credentials, or provider fallback. |
| Checker oracle | Require transcript `You: fixture-success` and `Assistant: fixture-ok`; reject `sk-ant-fixture-secret` and `unsupported --max-tokens`; retain cached-artifact provenance, exit, ANSI, raw cleanup, and isolated-session gates. |
| `llm_caret_tui_pty_spec.spl` | Add one modern scenario with steps `Open the cached caret TUI with offline Claude CLI fixture`, `Send a prompt through the visible input`, and `Check transcript and status`; assert the `offline-claude` evidence reports PASS. |
| Manual/merge owner | Regenerate the mirrored manual only with the rebuilt qualified runtime; report this scenario as designed/static until then. |

The checker and SSpec lanes own distinct files. The merge owner must not alter
the existing hidden/default/enabled/disabled cases: this one scenario adds
offline end-to-end Claude argv, subprocess, JSON response, and transcript proof
adjacent to their hidden-command coverage.
