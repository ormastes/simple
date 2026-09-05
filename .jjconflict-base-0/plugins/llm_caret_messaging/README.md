# LLM Caret Messaging Integration

This package describes the composite Claude, Codex, Gemini, MCP, and messaging
configuration installed by `caret messaging plugin install`. It is not an
SFFI plugin and does not modify the generic native-library plugin registry.

The installer must parse and merge settings, make a backup, and record owned
paths plus before/after hashes. Uninstall removes only entries whose current
hash still matches an installer-owned value. A changed or user-owned entry is
reported and preserved. Hook files contain commands only; credentials are
resolved by the bridge from `secret://` references and are never copied into an
agent settings file.

Hooks enqueue lifecycle events to a loopback or Unix-socket bridge and return
quickly. External delivery, retry, rate limiting, and dead-letter handling are
bridge responsibilities. Codex App Server is the primary Codex control path;
its notify hook is only a compatibility path for independently started CLI
sessions.

The package includes `skills/llm-caret-messaging/SKILL.md` for shared agent
behavior and a durable MCP launch configuration. MCP identity, workspace, and
scope values are process-bound environment configuration; tool arguments cannot
escalate them. The packaged environment contains no transport credential.
`caret messaging mcp` is a supervisor command: it freshness-checks and
builds `build/database/llm_caret_messaging_mcp`, then hands inherited MCP stdio
to that cached native worker. Consequently an interpreter-hosted Claude, Codex,
or Gemini process does not interpret the PureDatabase hot path.

Install, validate, and remove with:

```text
caret messaging plugin install --agents claude,codex,gemini
caret messaging plugin activate
caret messaging plugin activate --apply
caret messaging plugin deactivate
caret messaging plugin deactivate --apply
caret messaging plugin check
caret messaging plugin uninstall
```

`plugin check` validates owned-file hashes, decoded configuration, the selected
Claude/Codex/Gemini activation, and freshness of the compiled MCP, hook, and
bridge workers. Missing or stale workers produce a nonzero result with explicit
`mcp_ready`, `hook_ready`, and `bridge_ready` fields; valid manifests alone are
not reported as a healthy chat integration.

`caret messaging status`, `mcp --probe`, and `bridge --probe` use the same
freshness rule and return nonzero while required workers are absent or stale.
Probe JSON includes the exact worker artifact and `artifact_ready` boolean.

Native activation:

Install the managed payload first. Activation refuses a target without its
ownership record. Without `--apply`, it prints the credential-free native
Claude marketplace/plugin, Codex MCP, and Gemini extension commands only.
Successful activation writes a native ownership record. Deactivation requires
that record, removes the exact three agent registrations, and leaves the shared
Claude marketplace available for other plugins. Managed-file uninstall refuses
to run until native registrations have been deactivated.

Gemini is linked from the managed `gemini/` extension root. This separation is
intentional: Claude and Gemini both discover `hooks/hooks.json`, but use
different event sets and configuration schemas. Gemini therefore never loads
the Claude hook file from the composite package root.

```sh
claude plugin marketplace add . --scope project
claude plugin install llm-caret-messaging@simple-plugins --scope project
codex mcp add llm-caret-messaging -- caret messaging mcp
gemini extensions link plugins/llm_caret_messaging --consent
```

The Claude commands use the repository `.claude-plugin/marketplace.json` and
the official marketplace flow; no user settings file is overwritten directly.

Version 1 is a composite integration: `--agents` must select Claude, Codex, and
Gemini together. Partial, duplicate, or unknown selections fail before any
filesystem change. The installer persists the validated selection in
`config/selected-agents.sdn`, includes it in ownership hashing, verifies it
during `plugin check`, and removes/restores it with the same uninstall guards.

For automatic lifecycle-to-task updates, launch or steer the provider session
with `LLM_CARET_TASK_ID`, `LLM_CARET_ROOM_ID`, and `LLM_CARET_AGENT_ID` in its
local capability environment. Managed hooks also accept the equivalent
redacted payload fields `llm_caret_task_id`, `llm_caret_room_id`, and
`llm_caret_agent_id`. Correlation metadata is stored separately from hook
payloads and never contains transport credentials.

Executable evidence includes the primitive HTTP routing flow, the twelve-tool
MCP flow, and `llm_caret_messaging_hook_bridge_spec.spl` for correlated
Claude/Codex/Gemini lifecycle updates. Simulator evidence never counts as a
credential-backed external-platform pass.
