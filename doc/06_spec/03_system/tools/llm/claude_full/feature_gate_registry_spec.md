# Claude Full Feature-Gate Registry

> Validates a bounded Claude-full parts-bin map from gate-owner functions to
> focused or aggregate system-test evidence.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Feature-Gate Registry

## At a Glance

| Field | Value |
|---|---|
| Category | Tools / LLM / Claude Full |
| Status | Active source; execution requires a qualified self-hosted Simple runtime |
| Execution in this tranche | 0 scenarios executed; no PASS is claimed |
| Requirements | `REQ-LLM-CARET-HIDDEN-008` (supporting parts-bin metadata) |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Source | `test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl` |
| Updated | 2026-07-25 |
| Generator | Manual synchronization; docgen execution remains blocked |

## Scope and Claim Boundary

`claudeFeatureGateRegistry()` imports pure leaf owners and projects 33 selected
gate dimensions into `ClaudeFeatureGateRecord`. A record states whether its
Boolean columns model hidden state, enabled state, both, a textual outcome, or
metadata. Unknown defaults are marked explicitly and are not mislabeled as
owner defaults.

The executable SSpec checks:

- exact ordered identities, source files, owner symbols, and mapped specs;
- exact state shape, gate kind, default metadata, and every probe outcome;
- all 33 imported function-owner declarations against registry
  `source_file|gate_owner` edges in both directions;
- every nonempty root-command record against the production root registry;
- `/compact` root enabled/visible metadata against both leaf environment
  states;
- exact ordered diagnostics from a deliberately malformed registry.

This is an inward-only `claude_full` parts-bin capsule. Its discovery boundary
is the function import frontier of `feature_gate_registry.spl`: an imported
function owner without a registry edge and a registry edge without an imported
source declaration both fail. It does not scan for arbitrary unimported gates,
prove shipped Caret admission or CLI/TUI reachability, or establish complete
current-upstream Claude parity. Root/component/live-PTY evidence remains
authoritative for shipped hidden-command behavior.

This manual has exact identity/source/spec/state-matrix parity and complete
folded executable parity for all four scenario bodies. Supporting helper
implementations remain authoritative in the linked `.spl` file; their complete
contracts are visible below.

## Accepted Owner-to-Test Map

| Identity | State shape | Production owner | Gate owner | System-test evidence |
|---|---|---|---|---|
| `compact` | enabled | `src/app/llm_caret/claude_full/commands/compact/index.spl` | `compactCommand` | `test/03_system/tools/llm/claude_full/commands/compact_command_spec.spl` |
| `fast` | hidden+enabled | `src/app/llm_caret/claude_full/commands/fast/index.spl` | `fastCommand` | `test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl` |
| `fast-immediacy` | enabled | `src/app/llm_caret/claude_full/commands/fast/index.spl` | `fastCommand` | `test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl` |
| `chrome` | enabled | `src/app/llm_caret/claude_full/commands/chrome/index.spl` | `chromeCommand` | `test/03_system/tools/llm/claude_full/commands/chrome_command_spec.spl` |
| `insights` | hidden+enabled | `src/app/llm_caret/claude_full/commands/insights.spl` | `insightsCommand` | `test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl` |
| `insights-interactive-mode` | outcome | `src/app/llm_caret/claude_full/commands/insights.spl` | `runInsights` | `test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl` |
| `extra-usage-interactive` | hidden+enabled | `src/app/llm_caret/claude_full/commands/extra_usage/index.spl` | `extraUsageCommand` | `test/03_system/tools/llm/claude_full/commands/extra_usage_command_spec.spl` |
| `extra-usage-noninteractive` | hidden+enabled | `src/app/llm_caret/claude_full/commands/extra_usage/index.spl` | `extraUsageNonInteractiveCommand` | `test/03_system/tools/llm/claude_full/commands/extra_usage_command_spec.spl` |
| `review-remote` | hidden | `src/app/llm_caret/claude_full/commands/review/reviewRemote.spl` | `reviewRemoteCommand` | `test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl` |
| `review-remote-prerequisites` | outcome | `src/app/llm_caret/claude_full/commands/review/reviewRemote.spl` | `reviewRemoteNextStep` | `test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl` |
| `ultrareview` | enabled | `src/app/llm_caret/claude_full/commands/review/ultrareviewEnabled.spl` | `ultrareviewEnabled` | `test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl` |
| `xaa-idp` | hidden | `src/app/llm_caret/claude_full/commands/mcp/xaaIdpCommand.spl` | `xaaIdpCommand` | `test/03_system/tools/llm/claude_full/commands/mcp_large_spec.spl` |
| `immediate-command` | enabled | `src/app/llm_caret/claude_full/utils/immediateCommand.spl` | `shouldInferenceConfigCommandBeImmediate` | `test/03_system/tools/llm/claude_full/utils/immediate_command_spec.spl` |
| `worktree-mode` | enabled | `src/app/llm_caret/claude_full/utils/worktreeModeEnabled.spl` | `isWorktreeModeEnabled` | `test/03_system/tools/llm/claude_full/utils/worktree_mode_enabled_spec.spl` |
| `init-prompt` | enabled | `src/app/llm_caret/claude_full/commands/init.spl` | `useNewInitPrompt` | `test/03_system/tools/llm/claude_full/commands/init_commands_spec.spl` |
| `tasks-v2` | enabled | `src/app/llm_caret/claude_full/hooks/useTasksV2.spl` | `useTasksV2Enabled` | `test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl` |
| `agent-swarms` | enabled | `src/app/llm_caret/claude_full/utils/agentSwarmsEnabled.spl` | `isAgentSwarmsEnabled` | `test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl` |
| `team-memory` | enabled | `src/app/llm_caret/claude_full/memdir/teamMemPaths.spl` | `isTeamMemoryEnabled` | `test/03_system/tools/llm/claude_full/memdir/teamMemPaths_spec.spl` |
| `buddy-notification` | hidden+enabled | `src/app/llm_caret/claude_full/buddy/useBuddyNotification.spl` | `buddyNotificationDecision` | `test/03_system/tools/llm/claude_full/buddy/useBuddyNotification_spec.spl` |
| `skill-discovery-rendering` | hidden+enabled | `src/app/llm_caret/claude_full/components/messages/AttachmentMessage.spl` | `attachmentMessageRenderSkillDiscovery` | `test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl` |
| `persistent-retry` | enabled | `src/app/llm_caret/claude_full/services/api/withRetry.spl` | `isPersistentRetryEnabled` | `test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl` |
| `hidden-model-visible` | metadata | `src/app/llm_caret/claude_full/components/messages/nullRenderingAttachments.spl` | `hiddenModelVisibleFeatures` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `experimental-beta-env` | metadata | `src/app/llm_caret/claude_full/utils/managedEnvConstants.spl` | `safeEnvVars/isProviderManagedEnvVar` | `test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl` |
| `agent-teams-env` | metadata | `src/app/llm_caret/claude_full/utils/managedEnvConstants.spl` | `safeEnvVars/isProviderManagedEnvVar` | `test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl` |
| `bridge-entitlement` | enabled | `src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl` | `isBridgeEnabled` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `bridge-entitlement-blocking` | enabled | `src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl` | `isBridgeEnabledBlocking` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `bridge-disabled-reason` | outcome | `src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl` | `getBridgeDisabledReason` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `bridge-env-less` | enabled | `src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl` | `isEnvLessBridgeEnabled` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `bridge-cse-shim` | enabled | `src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl` | `isCseShimEnabled` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `bridge-min-version` | outcome | `src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl` | `checkBridgeMinVersion` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `bridge-auto-connect` | enabled | `src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl` | `getCcrAutoConnectDefault` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `bridge-ccr-mirror` | enabled | `src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl` | `isCcrMirrorEnabled` | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| `bridge-command-admission` | hidden+enabled | `src/app/llm_caret/claude_full/commands/bridge/bridge.spl` | `bridgeCommand/bridgeCommandFor` | `test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl` |

## Independently Pinned Contract Metadata

These values are repeated independently in the executable contract-signature
matrix. Clearing `/init`, changing an allowed gate kind, or redirecting a
record to a different valid owner/spec cannot pass through coordinated drift.

| Identity | Surface | Gate kind | Root command |
|---|---|---|---|
| `compact` | `root-command-admission` | `environment` | `/compact` |
| `fast` | `command-admission` | `conditional` | none |
| `fast-immediacy` | `command-immediacy` | `conditional` | none |
| `chrome` | `session-mode-admission` | `context` | none |
| `insights` | `command-admission` | `conditional` | none |
| `insights-interactive-mode` | `interactive-session-admission` | `context` | none |
| `extra-usage-interactive` | `interactive-command-admission` | `context` | none |
| `extra-usage-noninteractive` | `noninteractive-command-admission` | `context` | none |
| `review-remote` | `hidden-command-metadata` | `static` | none |
| `review-remote-prerequisites` | `remote-review-readiness` | `context` | none |
| `ultrareview` | `review-entitlement` | `conditional` | none |
| `xaa-idp` | `hidden-mcp-subcommand` | `static` | none |
| `immediate-command` | `command-immediacy` | `conditional` | none |
| `worktree-mode` | `cli-mode-admission` | `static` | none |
| `init-prompt` | `prompt-variant` | `environment` | `/init` |
| `tasks-v2` | `task-store-selection` | `context` | none |
| `agent-swarms` | `agent-team-admission` | `environment` | none |
| `team-memory` | `team-memory-admission` | `conditional` | none |
| `buddy-notification` | `notification-admission` | `context` | none |
| `skill-discovery-rendering` | `attachment-visibility` | `conditional` | none |
| `persistent-retry` | `retry-policy` | `conditional` | none |
| `hidden-model-visible` | `model-visible-user-hidden-metadata` | `static` | none |
| `experimental-beta-env` | `safe-environment-metadata` | `metadata-only` | none |
| `agent-teams-env` | `safe-environment-metadata` | `metadata-only` | none |
| `bridge-entitlement` | `remote-control-entitlement` | `conditional` | none |
| `bridge-entitlement-blocking` | `remote-control-blocking-entitlement` | `conditional` | none |
| `bridge-disabled-reason` | `remote-control-disabled-reason` | `conditional` | none |
| `bridge-env-less` | `env-less-bridge-admission` | `conditional` | none |
| `bridge-cse-shim` | `cse-shim-admission` | `conditional` | none |
| `bridge-min-version` | `minimum-version-admission` | `conditional` | none |
| `bridge-auto-connect` | `auto-connect-default` | `conditional` | none |
| `bridge-ccr-mirror` | `ccr-mirror-admission` | `conditional` | none |
| `bridge-command-admission` | `remote-control-command-admission` | `conditional` | none |

## Exact State Matrix

`H/E` means hidden/enabled. `N/A` means that Boolean dimension is not
applicable; textual outcomes remain asserted in the executable matrix.

| Identity | Default authority | Exact probe expectations |
|---|---|---|
| `compact` | known: H=N/A, E=true | `default E=true`; `disabled-by-env E=false` |
| `fast` | unknown | all four input pairs: admission follows `enabled`; immediacy does not affect H/E |
| `fast-immediacy` | unknown | all four input pairs: result follows `immediate`; admission does not affect it |
| `chrome` | known: E=true | `default E=true`; `noninteractive E=false` |
| `insights` | unknown | `disabled-input H=false E=false`; `enabled H=false E=true` |
| `insights-interactive-mode` | unknown contextual baseline | `interactive E=true outcome=report`; `noninteractive E=false` with the interactive-only message |
| `extra-usage-interactive` | known: H=false E=true | default enabled; noninteractive, disable-command-only, and provisioning rejection disabled |
| `extra-usage-noninteractive` | known: H=true E=false | default hidden/disabled; noninteractive visible/enabled; disable-command and provisioning rejection visible/disabled |
| `review-remote` | known: H=true, E=N/A | hidden metadata only; enablement is not fabricated |
| `review-remote-prerequisites` | unknown contextual baseline | `signed-out→signin`; missing session/PR/diff rejection; diff-only, file-count-only, and combined diff evidence each reach `review` |
| `ultrareview` | unknown | false/false, true/false, false/true all disabled; true/true enabled |
| `xaa-idp` | known: H=true, E=N/A | hidden metadata only; enablement is not fabricated |
| `immediate-command` | unknown | external false is deferred; external experiment and ANT are immediate |
| `worktree-mode` | known: E=true | stale feature gate removed |
| `init-prompt` | known: E=false | feature-off dominates; ANT and truthy env enable only with feature=true |
| `tasks-v2` | known: E=false | todo-off false even for team lead; solo true; team member false; feature-on team lead true |
| `agent-swarms` | known: E=false | ANT true; env/flag opt-in true with killswitch; killswitch independently blocks both env and flag routes |
| `team-memory` | known: E=false | both mixed states false; both true enabled |
| `buddy-notification` | known: H=true E=false | companion/window rejection hidden; eligible teaser visible/enabled |
| `skill-discovery-rendering` | known: H=true E=false | disabled, empty, and wrong type hidden; normal and demo visible with distinct feedback detail |
| `persistent-retry` | known: E=false | false/true inputs remain false/true |
| `hidden-model-visible` | known metadata; H/E=N/A | outcome `count=6;all-hidden-model-visible=true` |
| `experimental-beta-env` | known metadata; H/E=N/A | outcome `safe=true;provider-managed=false` |
| `agent-teams-env` | known metadata; H/E=N/A | outcome `safe=true;provider-managed=false` |
| `bridge-entitlement` | unknown entitlement baseline | `unentitled` plus isolated build/subscriber/gate rejection false; entitled true |
| `bridge-entitlement-blocking` | unknown entitlement baseline | same `unentitled` and isolated matrix through the blocking wrapper |
| `bridge-disabled-reason` | unknown | exact build, subscriber, profile, organization, and gate messages; entitled outcome empty |
| `bridge-env-less` | known: E=false | explicit env-less true only while bridge mode is on |
| `bridge-cse-shim` | known: E=true | explicit shim false while bridge mode is on; mode-off fallback true |
| `bridge-min-version` | unknown | old version rejected with exact message; current, empty-min, zero-min, or mode-off accepted |
| `bridge-auto-connect` | unknown | all four Boolean pairs; requires build and gate together |
| `bridge-ccr-mirror` | known: E=false | build-off false; env or gate enables only with mirror build |
| `bridge-command-admission` | known: H=false E=true | wrapper default enabled; all three rejected Boolean pairs hidden/disabled; true/true visible/enabled |

## Scenario

### REQ-LLM-CARET-HIDDEN-008: bounded gate-owner cross-map

#### should validate the bounded accepted Claude feature-gate registry

- Load the accepted Claude feature-gate registry.
  - Expected: the ordered 33-record identity list and the owner-to-test map
    above match exactly.
  - Expected: the structural checker returns `[]`.
  - Expected: the exact state matrix returns `complete`.
  - Expected: source discovery resolves 33 imported functions to their real
    declarations and the bidirectional completeness checker returns `[]`.
  - Expected: every owner function is declared by its mapped source and named
    by its mapped spec.
  - Expected: every nonempty root command, including `/compact` and `/init`,
    matches production root hidden/enabled metadata.
  - Expected: skill-discovery and persistent-retry false/true paths are called
    directly from this aggregate SSpec.

<details>
<summary>Executable SSpec</summary>

```simple
it "should validate the bounded accepted Claude feature-gate registry":
    step("Load the accepted Claude feature-gate registry")
    val records = setup_claude_feature_gate_fixture()

    expect(_feature_gate_ids(records)).to_equal([
        "compact",
        "fast",
        "fast-immediacy",
        "chrome",
        "insights",
        "insights-interactive-mode",
        "extra-usage-interactive",
        "extra-usage-noninteractive",
        "review-remote",
        "review-remote-prerequisites",
        "ultrareview",
        "xaa-idp",
        "immediate-command",
        "worktree-mode",
        "init-prompt",
        "tasks-v2",
        "agent-swarms",
        "team-memory",
        "buddy-notification",
        "skill-discovery-rendering",
        "persistent-retry",
        "hidden-model-visible",
        "experimental-beta-env",
        "agent-teams-env",
        "bridge-entitlement",
        "bridge-entitlement-blocking",
        "bridge-disabled-reason",
        "bridge-env-less",
        "bridge-cse-shim",
        "bridge-min-version",
        "bridge-auto-connect",
        "bridge-ccr-mirror",
        "bridge-command-admission"
    ])
    expect(_feature_gate_contract_signatures(records)).to_equal([
        "compact|src/app/llm_caret/claude_full/commands/compact/index.spl|test/03_system/tools/llm/claude_full/commands/compact_command_spec.spl|root-command-admission|enabled|compactCommand|/compact|false|true|true|false|true|environment",
        "fast|src/app/llm_caret/claude_full/commands/fast/index.spl|test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl|command-admission|hidden+enabled|fastCommand||false|false|false|true|false|conditional",
        "fast-immediacy|src/app/llm_caret/claude_full/commands/fast/index.spl|test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl|command-immediacy|enabled|fastCommand||false|false|false|false|false|conditional",
        "chrome|src/app/llm_caret/claude_full/commands/chrome/index.spl|test/03_system/tools/llm/claude_full/commands/chrome_command_spec.spl|session-mode-admission|enabled|chromeCommand||false|false|true|false|true|context",
        "insights|src/app/llm_caret/claude_full/commands/insights.spl|test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl|command-admission|hidden+enabled|insightsCommand||false|false|false|false|false|conditional",
        "insights-interactive-mode|src/app/llm_caret/claude_full/commands/insights.spl|test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl|interactive-session-admission|outcome|runInsights||false|false|false|false|true|context",
        "extra-usage-interactive|src/app/llm_caret/claude_full/commands/extra_usage/index.spl|test/03_system/tools/llm/claude_full/commands/extra_usage_command_spec.spl|interactive-command-admission|hidden+enabled|extraUsageCommand||false|false|true|false|true|context",
        "extra-usage-noninteractive|src/app/llm_caret/claude_full/commands/extra_usage/index.spl|test/03_system/tools/llm/claude_full/commands/extra_usage_command_spec.spl|noninteractive-command-admission|hidden+enabled|extraUsageNonInteractiveCommand||false|false|true|true|false|context",
        "review-remote|src/app/llm_caret/claude_full/commands/review/reviewRemote.spl|test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl|hidden-command-metadata|hidden|reviewRemoteCommand||false|false|true|true|false|static",
        "review-remote-prerequisites|src/app/llm_caret/claude_full/commands/review/reviewRemote.spl|test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl|remote-review-readiness|outcome|reviewRemoteNextStep||false|false|false|false|false|context",
        "ultrareview|src/app/llm_caret/claude_full/commands/review/ultrareviewEnabled.spl|test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl|review-entitlement|enabled|ultrareviewEnabled||false|false|false|false|false|conditional",
        "xaa-idp|src/app/llm_caret/claude_full/commands/mcp/xaaIdpCommand.spl|test/03_system/tools/llm/claude_full/commands/mcp_large_spec.spl|hidden-mcp-subcommand|hidden|xaaIdpCommand||false|false|true|true|false|static",
        "immediate-command|src/app/llm_caret/claude_full/utils/immediateCommand.spl|test/03_system/tools/llm/claude_full/utils/immediate_command_spec.spl|command-immediacy|enabled|shouldInferenceConfigCommandBeImmediate||false|false|false|false|false|conditional",
        "worktree-mode|src/app/llm_caret/claude_full/utils/worktreeModeEnabled.spl|test/03_system/tools/llm/claude_full/utils/worktree_mode_enabled_spec.spl|cli-mode-admission|enabled|isWorktreeModeEnabled||false|false|true|false|true|static",
        "init-prompt|src/app/llm_caret/claude_full/commands/init.spl|test/03_system/tools/llm/claude_full/commands/init_commands_spec.spl|prompt-variant|enabled|useNewInitPrompt|/init|false|true|true|false|false|environment",
        "tasks-v2|src/app/llm_caret/claude_full/hooks/useTasksV2.spl|test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl|task-store-selection|enabled|useTasksV2Enabled||false|false|true|false|false|context",
        "agent-swarms|src/app/llm_caret/claude_full/utils/agentSwarmsEnabled.spl|test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl|agent-team-admission|enabled|isAgentSwarmsEnabled||false|false|true|false|false|environment",
        "team-memory|src/app/llm_caret/claude_full/memdir/teamMemPaths.spl|test/03_system/tools/llm/claude_full/memdir/teamMemPaths_spec.spl|team-memory-admission|enabled|isTeamMemoryEnabled||false|false|true|false|false|conditional",
        "buddy-notification|src/app/llm_caret/claude_full/buddy/useBuddyNotification.spl|test/03_system/tools/llm/claude_full/buddy/useBuddyNotification_spec.spl|notification-admission|hidden+enabled|buddyNotificationDecision||false|false|true|true|false|context",
        "skill-discovery-rendering|src/app/llm_caret/claude_full/components/messages/AttachmentMessage.spl|test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl|attachment-visibility|hidden+enabled|attachmentMessageRenderSkillDiscovery||false|false|true|true|false|conditional",
        "persistent-retry|src/app/llm_caret/claude_full/services/api/withRetry.spl|test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl|retry-policy|enabled|isPersistentRetryEnabled||false|false|true|false|false|conditional",
        "hidden-model-visible|src/app/llm_caret/claude_full/components/messages/nullRenderingAttachments.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|model-visible-user-hidden-metadata|metadata|hiddenModelVisibleFeatures||false|false|true|false|false|static",
        "experimental-beta-env|src/app/llm_caret/claude_full/utils/managedEnvConstants.spl|test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl|safe-environment-metadata|metadata|safeEnvVars/isProviderManagedEnvVar||false|false|true|false|false|metadata-only",
        "agent-teams-env|src/app/llm_caret/claude_full/utils/managedEnvConstants.spl|test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl|safe-environment-metadata|metadata|safeEnvVars/isProviderManagedEnvVar||false|false|true|false|false|metadata-only",
        "bridge-entitlement|src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|remote-control-entitlement|enabled|isBridgeEnabled||false|false|false|false|false|conditional",
        "bridge-entitlement-blocking|src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|remote-control-blocking-entitlement|enabled|isBridgeEnabledBlocking||false|false|false|false|false|conditional",
        "bridge-disabled-reason|src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|remote-control-disabled-reason|outcome|getBridgeDisabledReason||false|false|false|false|false|conditional",
        "bridge-env-less|src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|env-less-bridge-admission|enabled|isEnvLessBridgeEnabled||false|false|true|false|false|conditional",
        "bridge-cse-shim|src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|cse-shim-admission|enabled|isCseShimEnabled||false|false|true|false|true|conditional",
        "bridge-min-version|src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|minimum-version-admission|outcome|checkBridgeMinVersion||false|false|false|false|false|conditional",
        "bridge-auto-connect|src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|auto-connect-default|enabled|getCcrAutoConnectDefault||false|false|false|false|false|conditional",
        "bridge-ccr-mirror|src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl|ccr-mirror-admission|enabled|isCcrMirrorEnabled||false|false|true|false|false|conditional",
        "bridge-command-admission|src/app/llm_caret/claude_full/commands/bridge/bridge.spl|test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl|remote-control-command-admission|hidden+enabled|bridgeCommand/bridgeCommandFor||false|false|true|false|true|conditional"
    ])
    expect(check_claude_feature_gate_registry(records)).to_equal([])
    expect(check_claude_feature_gate_state_matrix(records)).to_equal("complete")
    val discovered_sources = discover_feature_gate_sources()
    expect(discovered_sources.len()).to_equal(33)
    expect(check_feature_gate_source_completeness(records, discovered_sources)).to_equal([])

    for record in records:
        val owner_source = file_read_text(record.source_file)
        val owner_spec = file_read_text(record.owner_spec)
        expect(owner_source.len()).to_be_greater_than(0)
        expect(owner_spec.len()).to_be_greater_than(0)
        expect(record.gate_owner.len()).to_be_greater_than(0)
        for owner in record.gate_owner.split("/"):
            expect(owner_source).to_contain("fn " + owner + "(")
            expect(owner_spec).to_contain(owner)
        if record.root_command != "":
            val root = findRootCommand(record.root_command)
            expect(root.found).to_be(true)
            expect(root.command.slashName).to_equal(record.root_command)
            expect(root.command.hidden).to_be(record.root_hidden)
            expect(root.command.enabled).to_be(record.root_enabled)

    val skill_attachment = AttachmentModel.empty("skill_discovery")
    skill_attachment.skills = [AttachmentSkill.new("test-skill", "skill-1")]
    expect(attachmentMessageRenderSkillDiscovery(skill_attachment, false, false).visible).to_be(false)
    expect(attachmentMessageRenderSkillDiscovery(skill_attachment, true, false).visible).to_be(true)
    expect(isPersistentRetryEnabled(false)).to_be(false)
    expect(isPersistentRetryEnabled(true)).to_be(true)
```

</details>

#### should preserve compact root metadata and conditional owner behavior

- Reconcile root metadata with owner behavior.
  - Expected: `/compact` is enabled and visible in the production root map.
  - Expected: `disableCompactEnvTruthy=false` enables the leaf descriptor.
  - Expected: `disableCompactEnvTruthy=true` disables the leaf descriptor.

<details>
<summary>Executable SSpec</summary>

```simple
it "should preserve compact root metadata and conditional owner behavior":
    step("Reconcile root metadata with owner behavior")
    val records = setup_claude_feature_gate_fixture()
    val compact = _feature_gate_record(records, "compact")
    val root = findRootCommand("/compact")
    val owner_default = _feature_gate_probe(compact, "default")
    val owner_disabled = _feature_gate_probe(compact, "disabled-by-env")

    expect(root.found).to_be(true)
    expect(root.command.enabled).to_be(true)
    expect(root.command.hidden).to_be(false)
    expect(compact.root_command).to_equal("/compact")
    expect(compact.root_enabled).to_be(true)
    expect(compact.root_hidden).to_be(false)
    expect(owner_default.condition).to_equal("disableCompactEnvTruthy=false")
    expect(owner_default.enabled).to_be(true)
    expect(owner_disabled.condition).to_equal("disableCompactEnvTruthy=true")
    expect(owner_disabled.enabled).to_be(false)
```

</details>

#### should reject duplicate ownerless and incomplete gate records

- Check feature-gate completeness and rejection.
  - Expected: one exact ordered diagnostic array reports duplicate identity
    and root command, ownerless/incomplete/rootless metadata, malformed probes,
    default mismatch, incomplete conditional behavior, invalid kind/shape,
    falsely labeled unknown default, and missing compact reconciliation.
  - Expected: no unexpected diagnostic can be hidden by `to_contain`.

<details>
<summary>Executable SSpec</summary>

```simple
it "should reject duplicate ownerless and incomplete gate records":
    step("Check feature-gate completeness and rejection")
    val diagnostics = check_claude_feature_gate_registry(_malformed_feature_gate_fixture())

    expect(diagnostics).to_equal([
        "duplicate-source-id:duplicate",
        "duplicate-root-command:/dup",
        "ownerless-record:duplicate",
        "root-metadata-without-command:incomplete",
        "incomplete-record:incomplete",
        "empty-probe-condition:incomplete:default",
        "duplicate-probe-id:incomplete:default",
        "empty-probe-id:incomplete",
        "default-probe-mismatch:incomplete",
        "conditional-probes-incomplete:incomplete",
        "invalid-gate-kind:invalid",
        "invalid-state-shape:invalid",
        "unknown-default-labeled:invalid",
        "compact-drift-missing"
    ])
```

</details>

#### should reject import-frontier owners without registry coverage in either direction

- Compare the bounded import frontier with registry owner edges.
  - Expected: a duplicate imported source-owner edge is rejected exactly.
  - Expected: an imported future owner without a registry row is rejected
    exactly.
  - Expected: a registry owner whose import/source declaration disappears is
    rejected exactly.
  - Expected: the checker reports the full ordered diagnostic array, so one
    direction cannot hide drift in the other.

<details>
<summary>Executable SSpec</summary>

```simple
it "should reject import-frontier owners without registry coverage in either direction":
    step("Compare the bounded import frontier with registry owner edges")
    val records = setup_claude_feature_gate_fixture()
    val diagnostics = check_feature_gate_source_completeness(
        records,
        _feature_gate_drifted_source_fixture()
    )

    expect(diagnostics).to_equal([
        "duplicate-discovered-source-owner:src/app/llm_caret/claude_full/commands/compact/index.spl|compactCommand",
        "unregistered-source-owner:src/app/llm_caret/claude_full/future/newGate.spl|newGateEnabled",
        "registry-owner-not-discovered:src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|isCcrMirrorEnabled"
    ])
```

</details>

## Supporting Checker Contract

The executable helper fails lookups explicitly instead of returning element
zero silently. `check_claude_feature_gate_registry` validates:

- unique nonempty source IDs and root commands;
- root metadata only when a root command is named;
- nonempty source/spec/surface/owner/state/probe fields;
- gate kinds `static`, `conditional`, `environment`, `context`, or
  `metadata-only`;
- state shapes `hidden`, `enabled`, `hidden+enabled`, `outcome`, or `metadata`;
- unique nonempty probe IDs and nonempty conditions;
- known-default agreement and rejection of a `default` label when the default
  is unknown;
- behaviorally distinct conditional/environment/context probes;
- the exact `/compact` root-versus-leaf drift witness.

The independent `check_claude_feature_gate_state_matrix` pins every Boolean and
textual outcome listed in the Exact State Matrix table. Structural
self-consistency alone cannot green the first scenario.

`discover_feature_gate_sources` reads only the registry module, resolves its
`app.llm_caret.claude_full.*.{...}` imports to `src/.../*.spl`, and retains
imports that are real top-level function declarations. It does not walk the
full tree, execute owners, or run from a production request path.

`check_feature_gate_source_completeness` compares unique
`source_file|gate_owner` edges in both directions. Repeated registry edges are
allowed because one owner can project multiple state dimensions; duplicate
discovery edges, unregistered imported owners, and undiscovered registry
owners produce exact diagnostics. This is a bounded import-frontier oracle,
not automatic discovery of arbitrary unimported or upstream-only features.

<details>
<summary>Bounded source-discovery helper implementation</summary>

```simple
val FEATURE_GATE_REGISTRY_SOURCE = "src/app/llm_caret/claude_full/feature_gate_registry.spl"
val FEATURE_GATE_SOURCE_PREFIX = "src/app/llm_caret/claude_full/"

class ClaudeFeatureGateSource:
    source_file: text
    gate_owner: text

fn _feature_gate_contains_text(values: [text], wanted: text) -> bool:
    for value in values:
        if value == wanted:
            return true
    false

fn _feature_gate_source_key(source_file: text, gate_owner: text) -> text:
    source_file + "|" + gate_owner

fn discover_feature_gate_sources() -> [ClaudeFeatureGateSource]:
    var discovered: [ClaudeFeatureGateSource] = []
    val registry_source = file_read_text(FEATURE_GATE_REGISTRY_SOURCE)

    for raw_line in registry_source.split("\n"):
        val line = raw_line.trim()
        if line.starts_with("use app.llm_caret.claude_full.") and line.contains(".{") and line.ends_with("}"):
            val import_parts = line.split(".{")
            if import_parts.len() == 2:
                val module_import = import_parts[0].substring(4, import_parts[0].len())
                val source_file = "src/" + module_import.replace(".", "/") + ".spl"
                val source = file_read_text(source_file)
                val imported_symbols = import_parts[1].substring(0, import_parts[1].len() - 1)
                for raw_symbol in imported_symbols.split(","):
                    val symbol = raw_symbol.trim()
                    if source.contains("fn " + symbol + "("):
                        discovered.push(ClaudeFeatureGateSource(
                            source_file: source_file,
                            gate_owner: symbol
                        ))
    discovered

fn check_feature_gate_source_completeness(
    records: [ClaudeFeatureGateRecord],
    discovered: [ClaudeFeatureGateSource]
) -> [text]:
    var diagnostics: [text] = []
    var discovered_keys: [text] = []
    var registered_keys: [text] = []

    for source in discovered:
        val key = _feature_gate_source_key(source.source_file, source.gate_owner)
        if _feature_gate_contains_text(discovered_keys, key):
            diagnostics.push("duplicate-discovered-source-owner:" + key)
        else:
            discovered_keys.push(key)

    for record in records:
        for owner in record.gate_owner.split("/"):
            val key = _feature_gate_source_key(record.source_file, owner)
            if not _feature_gate_contains_text(registered_keys, key):
                registered_keys.push(key)

    for source_key in discovered_keys:
        if not _feature_gate_contains_text(registered_keys, source_key):
            diagnostics.push("unregistered-source-owner:" + source_key)

    for registered_key in registered_keys:
        if not _feature_gate_contains_text(discovered_keys, registered_key):
            diagnostics.push("registry-owner-not-discovered:" + registered_key)

    diagnostics

fn _feature_gate_drifted_source_fixture() -> [ClaudeFeatureGateSource]:
    val discovered = discover_feature_gate_sources()
    var drifted: [ClaudeFeatureGateSource] = []

    for source in discovered:
        if source.gate_owner != "isCcrMirrorEnabled":
            drifted.push(source)
    drifted.push(ClaudeFeatureGateSource(
        source_file: FEATURE_GATE_SOURCE_PREFIX + "future/newGate.spl",
        gate_owner: "newGateEnabled"
    ))
    if discovered.len() > 0:
        drifted.push(discovered[0])
    drifted
```

</details>

</details>
