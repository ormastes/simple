# LLM Caret CLI and TUI Hardening — System Test and Traceability Plan

Date: 2026-07-24

## Purpose

This is the single coordinating test plan for hardening LLM Caret in this
order:

1. deterministic CLI behavior;
2. interactive TUI behavior and visible evidence;
3. hidden, disabled, preview, and feature-flagged behavior;
4. row-level Claude parity.

It does not claim that all Claude Code behavior is implemented or passing.
It distinguishes current-tree evidence from the historical upstream snapshot
used to generate the full-parity matrices.

## Evidence Authority and Staleness

| Evidence | Current finding | Authority |
|---|---|---|
| `src/app/llm_caret/*.spl` | 25 direct Caret files; 7,198 LOC; 506 declarations | Finalized working-tree inventory |
| `doc/09_report/llm_caret_claude_cli_traceability.md` | Maps all 25 direct files and 7,198 current LOC | Current static mapping; not executable evidence |
| `scripts/check/check-llm-caret-claude-cli-trace.shs` | Final independent reconciliation: 25/25 files (100%); 7,198/7,198 LOC (100%); 506/506 file-qualified symbols | Checker passed before the final security refactor and was not rerun, per the one-green-run session guard |
| Full self-hosted CLI bootstrap | Stage 3 built; Stage 4 full-CLI native build was killed by signal 9; no candidate deployed | Current executable-test blocker; do not retry in this session |
| Cached Caret live-PTY qualification | Checker/spec/manual contain fail-closed hidden, promptless, and offline-Claude scenarios; the offline fixture drives fixed `claude_cli` argv, deterministic JSON response decoding, and transcript rendering without credentials or network. `--case prerequisites` requires a matching adjacent provenance manifest and fails closed when the cached artifact is absent | Current executable-test blocker; no live PASS or skipped prerequisite |
| `tmp/claude/claude-code-main/src` | Missing | Current-tree evidence |
| Full-parity feature matrix | 599 rows, 1,902 historical source files, 512,685 historical LOC | Snapshot-derived evidence; cannot be refreshed against upstream now |
| Full-parity file matrix | 1,902 rows | Snapshot-derived evidence |
| Full-parity symbol matrix | 14,119 rows | Snapshot-derived evidence |
| Full-parity implementation gate | 745 mapped targets exist; 1,157 missing; 599/1,902 targets reach 80% source LOC | Current target tree checked against stale snapshot rows |
| Full-parity primary tests | 174/1,902 mapped primary test paths exist | Current test tree checked against stale snapshot rows |
| Claude-full system specs | 349 executable specs | Current-tree evidence after adding the focused `AttachmentMessage` dispatcher spec |
| Generated Claude-full manuals | 65 correctly mirrored; 147 specs also/only have stale `doc/06_spec/test/...` manuals; 138 have neither path; 1 has both | Current-tree evidence after adding the canonical retry manual and removing its obsolete stale mirror |

The missing upstream tree makes claims such as “every current Claude feature”
or “no new Claude function is missing” assumptions, not evidence. Restore a
pinned, provenance-recorded upstream snapshot before regenerating any matrix.
Until then, preserve the matrices as historical evidence and do not delete or
rewrite their rows.

## Frozen Modern SSpec Contract

New or substantially revised hardening specs must use these names verbatim.

| Kind | Frozen names |
|---|---|
| Interfaces | `CaretCliFeatureCase`, `CaretTuiFeatureCase`, `CaretHiddenFeatureCase` |
| CLI helpers | `setup_cli_fixture`, `run_cli_case`, `check_cli_result` |
| Installed CLI helper | `probe_current_claude_cli` |
| TUI helpers | `setup_tui_fixture`, `run_tui_action`, `check_tui_snapshot` |
| Hidden helper | `setup_hidden_feature_fixture`, `check_hidden_feature_gate` |
| CLI steps | `Load the accepted Claude feature map`; `Invoke the caret CLI provider`; `Check the structured CLI response` |
| Installed CLI steps | `Load the accepted Claude feature map`; `Invoke the installed Claude CLI with no prompt or provider credentials`; `Check the structured CLI response` |
| TUI steps | `Open the caret TUI`; `Send a prompt through the visible input`; `Check transcript and status` |
| Hidden steps | `Enable the hidden-feature fixture`; `Check the hidden-feature gate` |

Every placeholder helper must fail explicitly with `assert(false)` or
`fail(...)`. No silent helper, `pass_todo`, tautological assertion, or skipped
scenario counts as coverage.

## Requirement Traceability

| Requirement | Implementation evidence | Current tests | Surface/status | Required hardening |
|---|---|---|---|---|
| REQ-LLM-CARET-CLAUDE-TRACE-001 | Historical Claude source references in `doc/09_report/llm_caret_claude_cli_traceability.md` | `llm_caret_claude_cli_traceability_spec.spl` | CLI / FAIL: upstream tree missing | Restore pinned source and regenerate feature groups |
| REQ-LLM-CARET-CLAUDE-TRACE-002 | 25 direct files under `src/app/llm_caret` | Checker maps all 25 files and 7,198 LOC | CLI/TUI / PASS | Keep rows synchronized when direct files move or split |
| REQ-LLM-CARET-CLAUDE-TRACE-003 | `check-llm-caret-claude-cli-trace.shs` | Traceability system spec | CLI / PASS: 100% files, 100% LOC, exact file-qualified symbols | Keep the current filesystem inventory synchronized |
| REQ-LLM-CARET-CLAUDE-TRACE-004 | Checker emits named counters and status | Traceability system spec | CLI / BLOCKED at runner mismatch in parent run | Modernize with frozen steps and assert exit code plus report fields |
| REQ-LLM-CARET-CLAUDE-TRACE-005 | File-qualified Simple symbol inventory | Checker proves 506/506 current declarations | CLI / PASS | Regenerate symbol rows and require zero missing/stale symbols |
| REQ-LLM-CARET-CLI-HARDEN-006 | Production CLI/provider/session/tool declarations plus the installed Claude executable's offline argument surface | Direct production unit specs plus `llm_caret_claude_cli_advanced_spec.spl` and `llm_caret_claude_cli_stream_spec.spl` for deterministic advanced/stream behavior; `llm_caret_installed_claude_cli_spec.spl` is supplemental environmental compatibility evidence | CLI / installed checker PASS; direct and cached Caret execution blocked | Retain the installed probe evidence, then execute direct and cached Caret contracts on the qualified self-hosted runtime |
| REQ-LLM-CARET-TUI-HARDEN-007 | `CaretIo`, `caret_chat`, and TUI/plain loops | Runtime component spec plus `llm_caret_tui_pty_spec.spl` routing/lifecycle/raw-rejection scenarios | TUI / designed fail-closed; live execution blocked | Require PTY PASS and pre/post mode plus cursor/screen restoration artifacts |
| REQ-LLM-CARET-HIDDEN-008 | Shipped hidden-command admission; supporting `claude_full` parts-bin hidden-disabled, distributed-gate, and focused owner evidence | `llm_caret_tui_hidden_feature_spec.spl`, the shipped root matrix, hidden-stub and feature-gate registries, narrowly scoped focused owner scenarios including bridge availability/admission, and the real-process `hidden` PTY case | Hidden / component, registry, source-completeness, distributed cross-map, focused parts-bin owner, and PTY process coverage designed; execution blocked | Execute the three registry specs and focused owner specs plus default/enabled/disabled PTY cases without credentials; shipped fulfillment remains exclusively the root/component/PTY lane |
| REQ-LLM-CARET-TUI-HARDEN-009 | Injected `CaretIo` frame/read/loop boundary | Runtime component spec plus PTY UTF-8/edit/navigation/geometry, redacted offline Claude provider failure, and modeled EOF scenarios | TUI / component designed; live execution blocked | Execute component scenarios and retained live capture on a cached artifact |
| REQ-LLM-CARET-FULL-001..003 | Feature/file/symbol TSV matrices | Full-parity inventory/plan gate | CLI/TUI / STALE | Re-extract only from restored pinned upstream |
| REQ-LLM-CARET-FULL-004 | 745/1,902 target files exist | Implementation gate plus row specs | All / FAIL | Zero missing implementation and test rows |
| REQ-LLM-CARET-FULL-005 | File matrix LOC thresholds | Implementation checker | All / FAIL: 599/1,902 at 80% | Prefer behavioral proof when an approved architecture replaces LOC parity |
| REQ-LLM-CARET-FULL-006 | No feature is marked out of scope in matrices | Plan checker | All / unproved | Keep all rows; phase work without declaring skipped rows complete |
| REQ-LLM-CARET-FULL-007 | Historical progress counters | Implementation checker | All / FAIL: current count is 599/1,902, not the old 551/1,884 baseline | Report fresh counters on every completion claim |
| NFR-LLM-CARET-TRACE-001..004 | Offline shell checker and MDSOC boundary | Traceability spec | CLI / partly covered | Keep deterministic; remove hardcoded report assumptions |
| NFR-LLM-CARET-TUI-005..007 | Simple-only capability boundary, cached real PTY, one-size-snapshot bounded teardown | Runtime component spec and `check-llm-caret-tui-pty.shs` | TUI / static-complete, execution blocked | No leaf externs, source fallback, paid provider, retry, polling, or prerequisite skip |
| NFR-LLM-CARET-FULL-001..005 | `claude_full` capsule and matrices | Distributed Claude-full specs | All / incomplete | Add facade, performance, observability, invalidation, and row-test evidence |

## Caret Feature-to-Test Map

| Feature | Implementation | Unit/integration evidence | System evidence | Surface/status |
|---|---|---|---|---|
| CLI argument parsing, help, and production wrapper | `main.spl`, `bin/caret` | `main_spec.spl` | `llm_caret_cli_hardening_spec.spl` has four source-process cases plus cached-wrapper selection/rejection | CLI / designed process evidence; execution blocked |
| Installed Claude CLI argument compatibility | installed `claude` executable plus `claude_cli.spl` argument builder assumptions | `claude_cli_spec.spl` | `llm_caret_installed_claude_cli_spec.spl` has six bounded, credential-free offline cases for path/hash/version/help/missing-input, hidden `--max-turns`, and removed `--max-tokens` behavior | CLI / checker PASS on Claude Code `2.1.218`; does not prove provider or session behavior |
| One-shot prompt and structured response | `main.spl`, `provider.spl` | `main_spec.spl`, `provider_spec.spl` | `llm_caret_interfaces_spec.spl` calls provider functions only | CLI / no process evidence |
| Claude argv: model, system, resume, limits, stream, schema, tools, verbose, extras | `claude_cli.spl` | `claude_cli_spec.spl` | Live specs are credentialed and opt-in | CLI / deterministic unit coverage; no wrapper launch |
| Provider selection and config | `provider.spl`, `config.spl` | `provider_spec.spl`; `config_spec.spl` has real fixture, missing-file, injected-empty, and API-key environment-owner scenarios | None | CLI / static unit evidence; execution blocked |
| Tool loop and permission policy | `chat.spl`, `tools.spl`, `main.spl` | `tools_spec.spl`, `main_spec.spl` | No CLI fixture proves deny/allow and exit/output contract | CLI / unit-only |
| Session save/list/resume | `session.spl`, `main.spl`, `chat_tui.spl` | `session_spec.spl`, `chat_tui_spec.spl` | Live resume uses real Claude; no offline process scenario | CLI/TUI / unit plus opt-in live |
| Server mode and request guards | `server.spl`, `main.spl` | `main_spec.spl`, `server_spec.spl` | None launches `--server` | CLI / unit-only |
| TUI selection, transcript, markdown, scroll, slash dispatch | `chat_tui.spl`, `tui_input.spl`, `tui_io.spl` | `chat_tui_spec.spl`, `chat_tui_input_spec.spl`, `chat_tui_runtime_spec.spl` | Component transitions include typed `begin_tui`/`end_tui` failure routing and plain hidden-command admission; real cached-wrapper PTY lifecycle and deterministic offline Claude dispatch are in `llm_caret_tui_pty_spec.spl` through `check-llm-caret-tui-pty.shs` | TUI / component proof present; cached execution is fail-closed and deferred to a qualified bootstrap artifact |
| `/help`, `/exit`, `/new`, `/model`, `/provider`, `/sessions`, `/resume` | `chat_tui.spl` | `chat_tui_spec.spl` | TUI hidden-feature spec drives provider/resume/new through `run_chat_tui_submission` | TUI / component dispatch; no live terminal |
| `/compact`, `/summarize`, `/init`, `/bootstrap` | `claude_full/commands.spl` root metadata/aliases through `chat_tui.spl` generic dispatch | `chat_tui_spec.spl`, `chat_tui_runtime_spec.spl` | Pure dispatch, TUI submission, and injected plain loop prove canonical unimplemented output, unchanged conversation/session/title/status, one exact System transcript line with cleared input, and zero model/persistence; command help does not advertise them and the 33 leaf-gate dimensions remain parts-bin-only | CLI/TUI / component proof; cached-wrapper stdin execution blocked |
| CLI/TUI/GUI shared dummy-provider seam | `provider.spl`, `interface_text.spl`, GUI modules | Core unit specs | `llm_caret_interfaces_spec.spl` | All / no modern steps or visible TUI evidence |
| Live Claude responses, tokens, model, system prompt, resume | `claude_cli.spl` | Parser/argv unit specs | `llm_caret_live_spec.spl`, `llm_caret_live_comprehensive_spec.spl` | CLI / opt-in; comprehensive spec contains three skip helpers |

## Historical Full-Parity Phase Map

These counts describe historical matrix rows, not verified current Claude.

| Phase | File rows | Targets present | Primary tests present | Surface |
|---|---:|---:|---:|---|
| P1 core CLI runtime | 62 | 34 | 22 | CLI |
| P2 tools and slash commands | 393 | 234 | 12 | CLI/TUI |
| P3 terminal UI | 615 | 274 | 30 | TUI |
| P4 remote bridge and server | 40 | 35 | 20 | CLI/hidden/remote |
| P5 services and extensibility | 172 | 17 | 17 | CLI/hidden |
| P6 support utilities and hardening | 622 | 151 | 73 | Shared |

The 349 existing Claude-full system specs exceed the 174 matrix paths because
many tests are aggregated, renamed, or not referenced by the historical
`primary_tests` cells. Coverage is not inferred from spec count.

## Hidden and Feature-Flag Map

| Hidden/gated feature | Implementation | Existing spec | Current evidence/gap |
|---|---|---|---|
| Hidden `/debug-tool-call`; disabled `/remote-setup` | `claude_full/commands.spl` | `root_commands_registry_spec.spl`, `llm_caret_tui_hidden_feature_spec.spl`, `llm_caret_tui_pty_spec.spl` | Registry-derived matrix covers every identity/admission state; component dispatch covers non-disclosure, enabled execution, and disabled rejection; the new PTY case drives all three through the real Caret TUI, with execution still pending |
| Hidden disabled stub commands: ant-trace, env, bughunter, issue, onboarding, share, summary, teleport, break-cache, ctx-viz, good-claude, mock-limits, oauth-refresh, perf-issue | command index capsules plus `commands/hidden_stub_registry.spl` | `hidden_stub_registry_spec.spl` plus the earlier `ant-trace/index_spec.spl`, `env/index_spec.spl`, `stub_commands_spec.spl`, and `more_stub_commands_spec.spl` | `claude_full` parts-bin aggregate and independent normalized source-completeness comparison implemented; modern manual is synchronized, but executable SSpec/docgen evidence is blocked |
| Fast mode research preview | `commands/fast/index.spl`, `commands/fast/fast.spl` | `fast_command_spec.spl` | Enable/hidden/toggle covered at function level; no CLI/TUI visibility capture |
| Remote-control/bridge entitlement, profile, version, env-less and CCR mirror gates | `bridge/bridgeEnabled.spl`, bridge command capsules | `bridge_small_helpers_spec.spl`, `bridge_command_spec.spl` plus mirrored manuals | 38 helper and 4 command scenarios are modern and statically synchronized; no offline root CLI/TUI gate scenario and no execution PASS |
| Extra usage interactive/noninteractive visibility | `commands/extra-usage/index.spl` | `extra_usage_command_spec.spl` | Function coverage; no process-mode selection evidence |
| Hidden remote review command | `commands/review/reviewRemote.spl` | `test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl`, `feature_gate_registry_spec.spl` | Aggregate metadata plus signed-out/session/PR/diff rejection and diff-only/file-count-only/combined readiness are mapped; process invocation remains missing |
| Todo/Tasks V2 flag and hidden-empty behavior | `hooks/useTasksV2.spl` | `useTasksV2_spec.spl`, `feature_gate_registry_spec.spl` plus mirrored focused manual | Eleven focused hook/store/helper scenarios and the complete aggregate gate projection are statically synchronized; visible TUI transition and runtime execution are not covered. The obsolete `240` sentinel was removed; the historical matrix target `250` remains non-PASS debt pending pinned-upstream regeneration |
| New init prompt ANT/env gate | `commands/init.spl` | `init_commands_spec.spl` | Function combinations covered; no command invocation evidence |
| Experimental beta disable and agent teams environment keys | `utils/managedEnvConstants.spl` | `managed_env_constants_spec.spl` plus mirrored manual | Exact safe-list membership and non-provider-managed classification covered; execution blocked |
| Hidden model-visible meta messages | `components/messages/nullRenderingAttachments.spl` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` | Named inventory covered; must remain distinct from user-visible hidden commands |
| Compact environment disable | root `/compact` metadata plus `compactCommand(disableCompactEnvTruthy)` | `test/03_system/tools/llm/claude_full/commands/compact_command_spec.spl`, `feature_gate_registry_spec.spl` | The bounded cross-map preserves root enabled/visible metadata and independently derives both leaf environment states |
| Chrome beta/noninteractive and insights enablement | Chrome/insights command capsules | focused command specs plus `feature_gate_registry_spec.spl` | Insights has four modern metadata/summary/report/rejection scenarios and a mirrored manual; function-level evidence is linked to the parts-bin map, while process admission remains unproved |
| Hidden MCP `xaa-idp` and ultrareview | independent MCP/review capsules | focused MCP/review specs plus `feature_gate_registry_spec.spl` | Default metadata and enabling probes are aggregated; complete current-upstream discovery and process invocation remain unproved |
| Agent swarms, team memory, and buddy | independent feature capsules | focused feature specs plus `feature_gate_registry_spec.spl` | Swarms' 3 and team-memory's 7 focused modern scenarios now have mirrored manuals; aggregate probes retain full gate matrices including both killswitch routes, while buddy remains aggregate-only; no shipped root admission claim |
| Immediate-command experiment and removed worktree gate | independent experiment/command capsules | focused utility specs plus `feature_gate_registry_spec.spl` | Immediacy and unconditional worktree-mode ownership remain distinct from command admission |
| Skill-discovery rendering and persistent retry | attachment/retry helpers | `feature_gate_registry_spec.spl`, `components/messages/AttachmentMessage_spec.spl`, `services/api/withRetry_spec.spl` | Skill discovery has three direct dispatcher scenarios for exact visible/demo/redacted render metadata. Retry has a deterministic loop/effect seam and 18 modern scenarios for persistent/max-boundary/provider/overflow plus direct classifier/header-owner behavior. Both remain parts-bin-only; retry execution is still blocked |

The accepted `claude_full` parts-bin map now spans 33 selected distributed
gate dimensions. The 599-row historical feature matrix remains scope evidence
rather than runtime gate metadata, and `hiddenModelVisibleFeatures()` still
covers only six model-visible meta-message surfaces. The new registry is
bounded: source/spec path checks prove its declared records are structurally
complete, but cannot automatically discover a future upstream or distributed
gate. Shipped Caret admission still derives from the root/component/PTY lane.

The bounded hidden-stub aggregate tranche now owns the 14 canonical
hidden-disabled command capsules. Its exact paths are
`src/app/llm_caret/claude_full/commands/hidden_stub_registry.spl`,
`test/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.spl`,
and
`doc/06_spec/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.md`.
Freeze its parts-bin record as `ClaudeHiddenStubCommandRecord` with
`source_id`, `source_file`, `command_name`, `hidden`, and `enabled`; freeze its
aggregate as `hiddenDisabledStubCommandRegistry`, and its SSpec helpers as
`setup_hidden_stub_registry_fixture` and
`check_hidden_stub_registry_contract`.
Preserve both source fields because all 14 descriptors expose the same command
name `stub`.
Use the manual steps `Load the parts-bin hidden-stub registry` and
`Check every hidden stub is disabled`. The modern scenario must prove the
inventory is nonempty, contains all 14 unique source identities, and derives
`hidden=true` plus `enabled=false` from each leaf descriptor.

The completeness gate must not trust the aggregate's fixed count alone. It
must discover every `commands/**/index.spl` stub descriptor in the source tree,
normalize canonical hyphenated source IDs against their import-safe underscore
facades, and compare that normalized set exactly with the production registry.
Hyphen/underscore twins represent one command identity; the underscore module
is the import owner and the hyphenated ID is the canonical user/source
identity. Any new canonical stub without registry membership, any orphan
registry record, or any duplicate normalized identity fails.

The distributed cross-map tranche owns
`src/app/llm_caret/claude_full/feature_gate_registry.spl`,
`test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl`, and its
mirrored manual. `ClaudeFeatureGateRecord` preserves `source_id`,
`source_file`, `owner_spec`, `surface`, applicability/state shape,
`gate_owner`, root metadata, default knowledge/state, gate kind, and Boolean
or textual condition probes. Its aggregate is
`claudeFeatureGateRegistry`; the SSpec helpers are
`setup_claude_feature_gate_fixture` and
`check_claude_feature_gate_registry`, plus an independent exact state-matrix
checker. The three modern scenarios validate the bounded accepted map and all
33 state dimensions, reconcile every named root plus the `/compact`
root-versus-owner witness, and compare malformed-registry diagnostics exactly.

## Modern SSpec Gaps and Target Specs

Current relevant system-test inventory has 357 specs; 279 use `step("...")`,
7 carry a REQ identifier, and 3 contain capture/evidence markers.
No placeholder tautologies or legacy Given/When/Then helpers were found, but
absence of placeholders does not prove behavioral coverage.

Current focused executable specs:

| Executable spec | Generated manual | Required proof |
|---|---|---|
| `test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.md` | Three scenarios: four source-process cases plus cached-wrapper selection and invalid-override rejection; current runner execution remains blocked |
| `test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.md` | Three fail-closed cached-artifact scenarios: provenance prerequisite, offline Claude response, and redacted provider-error/unknown-option evidence, retaining command, stdout, stderr, exit, and provenance artifacts |
| `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md` | Direct production `claude_cli_send` proof for resume, maximum turns, JSON schema, ordered `Read`/`Write` allowed tools, fixture extra argument, and deterministic structured response; no cached-wrapper claim |
| `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.md` | Direct production `claude_cli_stream` proof for ordered system/assistant/result envelopes, structured provider-error redaction, and malformed or duplicate-terminal fail-closed behavior; no cached-wrapper claim |
| `test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md` | Six bounded offline compatibility scenarios record installed path/version/hash and validate help, missing-input rejection, help-hidden accepted `--max-turns`, and removed `--max-tokens` rejection with no submitted prompt or inherited provider credentials |
| `test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl` | `doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.md` | Eight deterministic CLI/parser/provider/state scenarios with complete folded source; current runner execution remains blocked |
| `test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.md` | Ten TUI/hidden component scenarios, including Unicode raw-line reduction and hidden/disabled alias submission with zero responder/persistence; expected live capture remains unexecuted |
| `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.md` | Seven fail-closed process scenarios: cached/offline prerequisites, forced/auto/piped routing, modeled teardown, UTF-8/edit/geometry, hidden canonical/alias admission across default/enabled/disabled/false states, promptless TUI/plain command roots, and raw-entry rejection before ANSI mutation |
| `test/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.md` | Five scenarios, including one registry-derived exhaustive hidden/disabled/admission matrix that cannot silently omit a newly registered root command |
| `test/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.md` | One leaf-derived parts-bin hidden-disabled metadata scenario with independent source discovery, unique canonical identities, hyphen/underscore twin normalization, and two-way completeness |
| `test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/feature_gate_registry_spec.md` | Four parts-bin scenarios: exact 33-record owner/spec/state matrix, generic root reconciliation plus `/compact` drift, exact malformed-registry rejection, and bounded 33-edge imported-source discovery with a negative drift fixture |
| `test/03_system/tools/llm/claude_full/bridge/bridgeMain_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgeMain_spec.md` | Twenty-six direct-owner lifecycle scenarios covering all 16 isolated spawn, heartbeat, cleanup, completion, acknowledgement, retry, timeout, status, stdin, and signal owners |
| `test/03_system/tools/llm/claude_full/bridge/bridgeMessaging_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgeMessaging_spec.md` | Ten direct-owner scenarios for bounded UUID state, discriminants, eligibility/title policy, ingress/deduplication, control responses, and stable result construction |
| `test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/services/mcp/client_spec.md` | Eighteen direct-owner MCP client scenarios for error classification, connection decisions, cache isolation, batching/order/counts, URL elicitation retry, and result policies |
| `test/03_system/tools/llm/claude_full/services/mcp/auth_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/services/mcp/auth_spec.md` | Twenty-four scenarios: nine credential-mutation state/effect cases plus fifteen direct OAuth, redaction, normalization, provider, XAA, secret-input, scope, and step-up owner cases |
| `test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl` | `doc/06_spec/03_system/tools/llm/claude_full/cli/structuredIO_spec.md` | Sixteen direct `StructuredIO` scenarios for ordered input, routing, pending cleanup, replay, bridge injection, permission/hook/elicitation/sandbox, and MCP outcomes |
| `test/01_unit/app/llm_caret/openai_compat_spec.spl` | `doc/06_spec/01_unit/app/llm_caret/openai_compat_spec.md` | Eleven injected request/completion scenarios for the shipped OpenAI-compatible provider, with no live network or provider call |
| Nine focused owner/effect specs: Tasks V2, swarms, team memory, insights, review/rewind/sandbox, bridge helpers, bridge command, AttachmentMessage, and withRetry | Same relative paths under `doc/06_spec/03_system/tools/llm/claude_full/` | 91 modern scenarios with frozen steps/helpers and synchronized manuals; requirements are narrowly scoped, all manuals report zero execution, and none establishes shipped reachability |

Every relevant REQ needs at least a happy, edge, and error/rejection scenario.
The CLI fixture must use stdlib/facade process APIs, never local `rt_*`
externs. The TUI fixture must use the repository UI access protocol when the
surface exposes it; screenshot-only evidence is insufficient.

## Scenario and Evidence Policy

- CLI manuals display the three frozen CLI steps and a compact `exec`/`text`
  capture; setup and parsing details are folded.
- The cached-Caret CLI manual owns production-wrapper evidence rather than
  source-entrypoint evidence. It retains `command.txt`, scrubbed `stdout.txt`,
  scrubbed `stderr.txt`, `exit.txt`, `provenance.txt`, and `combined.txt` per
  case under `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_cli_cached/`.
- The installed-Claude manual uses the three frozen installed-CLI steps, links
  raw stdout/stderr/exit/provenance artifacts, and explicitly excludes provider,
  authentication, resume, network, billing, and model-quality claims.
- TUI manuals display the three frozen TUI steps and embed a compact TUI
  capture under
  `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty/`.
- Live-terminal manuals link the complete `script(1)` typescripts, driver logs,
  input bytes, pre/post `stty` modes, and geometry under
  `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty/`.
  A missing cached artifact, adjacent provenance manifest, `script(1)`,
  `stty`, `pgrep`, `cmp`, SHA-256 utility, marker, or restoration row is a failure,
  never a skip. Each child has one fixed 20-second watchdog and no retry. On
  timeout the watchdog freezes each direct-child snapshot before descending,
  performs at most three `pgrep -P` rescans to close the fork-before-STOP race,
  and terminates every captured `script`/runner/Caret PID. If the timeout marker
  is present, the parent waits for TERM, CONT, delayed KILL, and a
  teardown-complete marker before returning. This is bounded recursive teardown
  evidence, not a general process-tree proof. The outer SSpec deadline is
  240 seconds for `hidden` and `promptless`, whose sequential per-child budgets
  can exceed 120 seconds, and 120 seconds for all other scenario groups.
  `typescript.txt` is the canonical ANSI terminal screen capture, not a raster
  screenshot; its frame is interpreted together with terminal-mode, geometry,
  alternate-screen, cursor, and transcript assertions.
- Piped automatic routing submits `/exit` and accepts only stdout exactly `> `,
  empty stderr, zero exit, and no ANSI bytes. A prompt substring is not
  completion evidence.
- The live hidden scenario retains three typescripts: default hidden rejection
  matching unknown-command behavior, explicitly enabled sanitized execution,
  and disabled-command rejection. Its checker requires the exact `system:`
  semantic prefixes so raw PTY input echo cannot satisfy the oracle. All use a
  fixed 12x80 PTY, remove provider/cloud credentials, use the dummy provider,
  submit no model prompt, and require the explicit child marker
  `caret_exit=0` in addition to `script -e`.
- Hidden-feature manuals display both frozen hidden steps and the accepted case
  matrix; repetitive rows may fold, but rejected-state evidence remains visible.
- Use `# @evidence-display: embed_tui`. Capture remains off outside the
  scenarios that need it.
- The live specs remain supplemental. They cannot substitute for deterministic
  dummy/fake-backed acceptance and may not silently pass when credentials or
  long-live mode are absent.
- Fix the live-spec run comments that still name `test/system/...`; the
  executable path is `test/03_system/tools/llm/...`.
- Replace `_skip_long_live` placeholder passes with an explicit opt-in suite
  boundary or real scenarios; skipped completion is not release evidence.

## Cached Caret Artifact and Provenance Contract

The live checker selects the first executable repository-cached Caret artifact,
then requires an adjacent `${artifact}.provenance` file. It does not search for
a second artifact after selecting an executable whose provenance is missing or
invalid. The manifest is line-oriented `key=value` text with exactly one
nonempty value for each required key:

```text
source_commit=<40-or-64-lowercase-hex-commit>
binary_sha256=<64-lowercase-hex>
runtime_sha256=<64-lowercase-hex>
runtime_path=bin/release/<target>/simple
runtime=pure-simple-self-hosted
runtime_probe=pass
rust_seed_used=false
target=<canonical-host-target>
```

The checker:

1. selects `shasum -a 256` or `sha256sum`, failing if neither exists;
2. verifies `binary_sha256` against the selected executable;
3. requires a clean committed tree, then verifies `source_commit` against Git
   `HEAD`, or against jj `@-` when the jj `@` working-copy commit is empty;
4. verifies `target` equals the detected host architecture, OS, and Linux ABI;
5. requires `runtime_path` to name `bin/release/<target>/simple`, rehashes that
   executable, and verifies `runtime_sha256`;
6. requires the producer-attested `runtime=pure-simple-self-hosted`,
   `runtime_probe=pass`, and `rust_seed_used=false` fields;
7. exports `SIMPLE_CARET_NATIVE` as that exact verified artifact before
   invoking `bin/caret`, with source fallback disabled.

Live PTY driving is currently qualified only for Darwin `script(1)` and
util-linux `script(1)`. FreeBSD, OpenBSD, NetBSD, and other variants fail closed
until their exact harmless invocation syntax has an executable capability gate;
their target triples below remain build-manifest identities, not PTY PASS
claims.

After the future full native build succeeds, create the manifest immediately
from the same clean, committed working copy. These commands are the canonical
build-and-manifest sequence:

```bash
case "$(uname -s):$(uname -m)" in
  Darwin:arm64|Darwin:aarch64) target=aarch64-apple-darwin ;;
  Darwin:x86_64|Darwin:amd64) target=x86_64-apple-darwin ;;
  Linux:arm64|Linux:aarch64) architecture=aarch64 ;;
  Linux:x86_64|Linux:amd64) architecture=x86_64 ;;
  FreeBSD:arm64|FreeBSD:aarch64) target=aarch64-unknown-freebsd ;;
  FreeBSD:x86_64|FreeBSD:amd64) target=x86_64-unknown-freebsd ;;
  OpenBSD:arm64|OpenBSD:aarch64) target=aarch64-unknown-openbsd ;;
  OpenBSD:x86_64|OpenBSD:amd64) target=x86_64-unknown-openbsd ;;
  NetBSD:arm64|NetBSD:aarch64) target=aarch64-unknown-netbsd ;;
  NetBSD:x86_64|NetBSD:amd64) target=x86_64-unknown-netbsd ;;
  *) exit 1 ;;
esac
if [ "$(uname -s)" = Linux ]; then
  if getconf GNU_LIBC_VERSION >/dev/null 2>&1; then
    target="${architecture}-unknown-linux-gnu"
  elif ldd --version 2>&1 | grep -i -F musl >/dev/null 2>&1; then
    target="${architecture}-unknown-linux-musl"
  else
    exit 1
  fi
fi

runtime="bin/release/${target}/simple"
artifact="build/bootstrap/caret-package/caret"
test -x "${runtime}"
case "${runtime}" in
  *src/compiler_rust/*) exit 1 ;;
esac
seed_delegate="$(dirname "${runtime}")/simple_seed"
test -x "${seed_delegate}"
if cmp -s "${runtime}" "${seed_delegate}"; then
  exit 1
fi
runtime_id=$("${runtime}" --version 2>&1) || exit 1
case "${runtime_id}" in
  *"Rust-built Simple binary"*|*"bootstrap seed only"*) exit 1 ;;
esac
test "$("${runtime}" -c 'print(6 * 7)' 2>/dev/null)" = 42
if test -e .jj; then
  test "$(jj log -r @ --no-graph -T 'if(empty, "true\n", "false\n")')" = true
  source_commit=$(jj log -r '@-' --no-graph -T 'commit_id ++ "\n"')
elif git rev-parse --verify HEAD >/dev/null 2>&1; then
  test -z "$(git status --porcelain)"
  source_commit=$(git rev-parse --verify HEAD)
else
  exit 1
fi
mkdir -p "$(dirname "${artifact}")"
"${runtime}" native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/llm_caret/main.spl --strip \
  --output "${artifact}"
test -x "${artifact}"

hash_file() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  elif command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    return 1
  fi
}
binary_sha256=$(hash_file "${artifact}") || exit 1
runtime_sha256=$(hash_file "${runtime}") || exit 1
{
  printf 'source_commit=%s\n' "${source_commit}"
  printf 'binary_sha256=%s\n' "${binary_sha256}"
  printf 'runtime_sha256=%s\n' "${runtime_sha256}"
  printf 'runtime_path=%s\n' "${runtime}"
  printf 'runtime=pure-simple-self-hosted\n'
  printf 'runtime_probe=pass\n'
  printf 'rust_seed_used=false\n'
  printf 'target=%s\n' "${target}"
} >"${artifact}.provenance"
```

Do not copy a manifest from another artifact, edit a hash to satisfy the
checker, build from uncommitted source, or retain a sidecar after replacing its
binary. The subsequent `--case prerequisites` run must print the selected
artifact, manifest path, matched source check, binary hash, runtime path/hash,
pure-Simple runtime identity, passing runtime probe, `rust_seed_used=false`, and
target
before any PTY case is accepted.

## Execution Order and Exact Commands

Run each gate once after its inputs change; stop after convergence.

```bash
sh scripts/check/check-llm-caret-claude-cli-trace.shs
sh scripts/check/check-llm-caret-full-parity-plan.shs
sh scripts/check/check-llm-caret-full-parity-implementation.shs
sh scripts/check/check-llm-caret-installed-claude-cli.shs --case all
sh scripts/check/check-llm-caret-tui-pty.shs --case all

bin/simple test test/01_unit/app/llm_caret/main_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/claude_cli_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/claude_api_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/openai_api_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/chat_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/chat_tui_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/chat_tui_input_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/config_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/tools_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/llm_caret/types_spec.spl --mode=interpreter

bin/simple test test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --mode=interpreter
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl --mode=interpreter
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl --mode=interpreter
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl --mode=interpreter
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl --mode=interpreter
bin/simple test test/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.spl --mode=interpreter
bin/simple test test/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.spl --mode=interpreter
bin/simple test test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --mode=native

bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl --output doc/06_spec --no-index
bin/simple test test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl --mode=interpreter

sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
find doc/06_spec -name '*_spec.spl' | wc -l
```

The last command must print `0`. Each docgen invocation must report the changed
spec complete with `0 stubs`.

## Pass/Fail Criteria

PASS requires all of the following:

- the focused trace checker maps at least 80% of current direct files and LOC,
  and traces every current direct-file function/struct/extern;
- CLI deterministic scenarios launch the real wrapper and assert exit,
  structured response, stderr, and side effects;
- TUI scenarios send input through the visible surface and verify transcript
  plus status with captured evidence;
- live PTY qualification proves forced/automatic routing, ANSI-free piped
  fallback with exact prompt-only `/exit` completion and empty stderr, modeled
  terminal teardown, UTF-8 editing/navigation, one bounded geometry, the
  semantic transcript text `You: a界c!`, explicit zero Caret child exits, and
  failure before terminal mutation when raw entry is unavailable;
- the selected live artifact has a matching adjacent provenance manifest,
  binary digest, clean committed source revision, host target, and rehashed
  build runtime; the manifest attests a passing pure-Simple self-hosted runtime
  probe and `rust_seed_used=false`, and the wrapper is pinned to that verified
  artifact;
- the installed-Claude probe submits no prompt, inherits no provider
  credentials, retains path/version/hash/raw stdout/stderr/exit artifacts, and
  makes no authenticated/provider/session claim;
- the root-command registry scenario derives lookup, alias, admission, and
  visibility coverage from every production record;
- the hidden-stub registry derives every record from its leaf descriptor and
  exactly matches independent normalized source discovery in both directions;
- every accepted hidden/flag case proves default and enabled/rejected states;
- the real TUI hidden case proves default non-disclosure, enabled debug-command
  execution, and disabled-command rejection through retained PTY transcripts;
- all frozen helpers and step text are preserved;
- no unresolved runtime symbol, timeout, signal exit, usage exit, empty suite,
  placeholder pass, or missing manual is accepted;
- restored upstream provenance exists before any “all Claude functions” claim;
- full-parity matrices have zero unimplemented or untested rows before a full
  parity completion claim.

Current status is **FAIL / implementation present, execution blocked**. Direct
file/LOC/symbol mapping and the focused manuals are current. Process-level CLI,
live-PTY TUI capture, and the full-parity rows remain unproved by executable
evidence.

## 2026-07-24 Execution Update

The focused hardening lane now includes:

- `llm_caret_claude_cli_feature_contract_spec.spl`, covering the shared
  production builder/parser, local subprocess dispatch, stream envelopes,
  hidden fast/review gates, removed-flag rejection, and redaction;
- `llm_caret_cli_hardening_spec.spl`, launching the actual Caret entrypoint for
  help, offline success, provider failure, and unknown-option cases, plus
  cached production-wrapper selection and invalid-override rejection;
- `llm_caret_cli_cached_spec.spl` plus its checker, requiring a provenance-
  qualified cached Caret artifact and retaining scrubbed command/stdout/stderr/
  exit/provenance evidence for help, offline Claude response, provider failure,
  and unknown-option rejection;
- `llm_caret_installed_claude_cli_spec.spl`, covering six bounded offline
  probes of the currently installed Claude executable with isolated HOME,
  config, working directory, and provider credentials removed;
- `llm_caret_tui_hidden_feature_spec.spl`, covering visible input/transcript,
  provider/model/session status, ANSI/UTF-8 decoder and raw-line control
  transitions, permission
  denial, retry limits, hidden commands, and SGTTI exclusion;
- `llm_caret_tui_pty_spec.spl` plus its shell checker, requiring a repository
  cached `bin/caret` target and real `script(1)` PTY while retaining typescript,
  input, driver, geometry, terminal-mode, and hidden-admission evidence for
  every case;
- `managed_env_constants_spec.spl`, covering the experimental-beta disable and
  agent-team hidden environment keys without reading host state;
- `root_commands_registry_spec.spl`, deriving canonical/slash/alias identity,
  admission, visibility, hidden, and disabled coverage from every production
  root registry record;
- `hidden_stub_registry_spec.spl`, deriving 14 hidden-disabled metadata records
  from leaf descriptors and comparing them with normalized source discovery;
- `feature_gate_registry_spec.spl`, deriving 33 distributed gate projections,
  linking exact owner/spec evidence, preserving `/compact` drift, and rejecting
  malformed registry records;
- `llm_caret_cli_tui_hardening_smoke.spl`, a non-SSpec native entry for
  toolchain-isolated production-seam validation.

Current Claude Code `2.1.218` was probed without a prompt-bearing success path.
The installed CLI:

- returned a missing-input failure for a promptless stream-JSON invocation;
  that observation does not independently prove verbose-option validation;
- rejects `--max-tokens` as an unknown option;
- accepts `--max-turns` even though top-level help intentionally omits it;
- exposes `--allowedTools <tools...>` as one variadic option.

Production changes now enforce those contracts. The real provider dispatcher
routes through `claude_cli_send` instead of maintaining a second private
builder/parser. TUI `/provider`, `/model`, successful `/resume`, and `/new`
refresh visible status; `/new` obtains a fresh session ID instead of reusing
and overwriting the prior persisted conversation.

Focused system manuals are mirrored under `doc/06_spec/03_system/...`.
Source-synchronized unit manuals now mirror 84 Claude CLI, 36 provider, 15
OpenCode CLI, nine local-Torch, 24 production-chat, 62 TUI, 22 raw-input, 22
injected-runtime, 64 main-entry, 16 production-config, 13 Claude API, 14 OpenAI
API, 37 production-tools, and 14 production-types scenarios.
Because docgen cannot execute in the current runtime, all refreshed manuals
explicitly report zero executed scenarios and do not claim a PASS.
The established 430-example base includes the source-synchronized unit,
CLI-contract/process, TUI/hidden, managed-environment, installed-Claude,
root/feature/hidden registry, PTY, bridge-lifecycle, and MCP-client scenarios
listed above. The seven-scenario net expansion of direct `StructuredIO`
coverage, fifteen restored/direct MCP OAuth scenarios, eleven injected
OpenAI-compatible provider scenarios, six injected main-entry scenarios, four
config owner scenarios, 27 modern Claude/OpenAI API scenarios, 15 OpenCode
process/parse scenarios, nine shell-free local-Torch scenarios, and five
additional provider-delegation scenarios plus the two production-imported
blank-input and undersized-frame scenarios raise that base to 531. The 91
focused owner/effect examples now synchronized
across Tasks V2, swarms, team memory, insights, review/rewind/sandbox, bridge
helpers/command, AttachmentMessage, and withRetry raise the scoped modern
curated `should` total to 622 examples with canonical matchers. This total is a
scenario inventory, not a claim that every legacy base scenario already uses
the frozen `step(...)` form. The pre-existing
unit/component/process manuals retain
their documented body-parity checks. The feature-gate manual statically checks
exact 33-row contract/state parity and carries complete folded executable
parity for all four scenario bodies; helper contracts are visible while their
implementations remain authoritative in the executable spec.

Executable status remains **FAIL / runtime blocked**. The deployed
self-hosted `bin/simple` lacks `rt_process_spawn_guarded`, so the process SSpec
stops during semantic resolution before its scenario body. An isolated
pure-Simple bootstrap compiler accepted the hardening source through native
code generation, but the permitted third attempt stopped at the hosted-runtime
link boundary (`_MTLCreateSystemDefaultDevice` and `_rt_http_request`). Do not
repeat these commands in this session. After the concurrent compiler lane
deploys a full CLI containing the guarded-process symbol, run each focused
unit/system gate once and then the native smoke.

### Follow-up hardening and evidence audit

The current tree now rejects malformed/non-contract Claude JSON, rejects empty
or malformed successful NDJSON streams, requires a terminal stream event, and
redacts protocol-level error/result payloads. Typed JSON traversal replaces the
previous global substring extraction on these production paths and aggregates
all assistant text blocks. Offline fixtures cover empty, malformed,
unterminated, and secret-bearing streams.

TUI session transitions now preserve backend isolation:

- `/new` clears the provider session before issuing a fresh app session ID;
- `/provider` refreshes provider-specific model/key/base URL/CLI path and
  clears the foreign provider session;
- `/resume` restores provider, model, provider session, messages, title, and
  visible status together;
- command-line resume defaults to the persisted provider/model and discards
  the provider session when an explicit backend/model override is incompatible;
- reset/resume confirmations render after transcript replacement so they stay
  visible.

Hidden root commands now pass through `admitRootCommand`: hidden commands are
rejected by default and admitted only when enabled, while disabled commands
remain rejected under every fixture. Retry backoff is capped after jitter and
the configured retry timeout now prevents an over-budget sleep.

The completion audit is still red. Adding the Simple-only `tui_io.spl`
capability owner plus the CLI entry/API/config seams makes the current direct
scope 25 files / 7,198 LOC with 506/506 file-qualified declarations in the
regenerated trace inventory.
The focused checker covers all file-qualified declarations, including the
ANSI/UTF-8 raw-key decoder, raw-line reducer, and parser validation helpers.
The historical
1,902-row full-parity matrix has 1,157 missing targets and 1,728 missing primary
specs, and its upstream source tree is absent. The component TUI spec covers
the pure raw-key decoder, input-widget transition, and control-byte precedence.
The live checker now defines the driven PTY qualification and retains
artifacts, but no live PASS or capture is claimed until a cached artifact
executes every fail-closed case.
The root registry now has a production-derived exhaustive scenario for every
registered canonical name, slash name, alias, admission state, and visible
membership, and the root hidden/disabled states have a real Caret TUI PTY
scenario ready for execution. The 14 hidden-disabled stub descriptors now have
a bounded parts-bin aggregate plus an independent source-completeness gate.
Experimental environment gates and the remaining distributed hidden features
are still not part of one aggregate production invocation map. These gaps
prohibit a full Claude parity or production-ready PASS claim.

### 2026-07-25 TUI component and PTY checkpoint

The production-imported runtime spec and manual now contain 22 synchronized
scenarios with zero executed. Blank or whitespace-only plain input continues
to the next command, while `nil` remains EOF. `_draw_if_visible` bounds every
frame write, including a captured five-row terminal fixture.

The PTY checker/spec/manual retain the same seven scenario labels and frozen
steps. Static hardening adds case-specific outer deadlines, exact piped
prompt-only completion with empty stderr, bounded descendant rescans, and
required pure-Simple/passing-probe/no-Rust-seed provenance. Shell syntax and
static parity were checked; zero real PTY cases executed.

Remaining function evidence is explicit: `production_caret_io`/`caret_is_tty`,
`run_server` lifecycle, successful provider-response normalization, `run_gui`
lifecycle, and the Metal render/submit/present loop. The pinned upstream Claude
source and full parity gaps also remain.

No provenance-qualified self-hosted Caret artifact exists, and no real PTY
scenario has executed; static TUI and checker hardening is not a TUI PASS.
