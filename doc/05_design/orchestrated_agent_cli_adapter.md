# Orchestrated agent CLI adapter admission

Status: integration in progress; authored checks are NOT_RUN. The two reused
contracts came from identified, read-only main-tree prototypes:
`agent_cli_v1.spl` and `agent_invocation_binding_v1.spl`. Their admission belongs
to the same consumed AgentSession integration, not a standalone completion claim.

Observed local help/version evidence dated 2026-11-07 is retained under
`build/orchestrator-toolchain-20261107/agent-cli-help` in the original workspace.
The exact supported profiles are Codex 0.167.0, Claude Code 2.1.318 and Kimi
2.5.0. Unknown versions and providers fail closed. Kimi's observed prompt mode
is noninteractive, so interactive task injection is refused. Codex exec/resume
help documents lone `-` as stdin input; the argv-only adapter refuses that
sentinel rather than silently changing how task content is delivered.

Capability values record provider/version/executable digest. They do not prove
installation or authorization. The host/provider image probe supplies observed
evidence; the controller retains and correlates it with the immutable image,
policy, task and workspace. Caret submits intent and consumes actual observations.
The common Simple Container API owns Windows Docker/Linux Podman engine commands;
this adapter only produces the selected agent's command arguments.

REQ-CARET-AGENT-CLI-001: accept only the exact evidenced CLI interface versions
and supported execution modes; unknown versions and stdin-selector ambiguity
fail closed without provider or native fallback.

REQ-CARET-AGENT-CLI-002: preserve arbitrary authorized prompt text in one
argument, with explicit model/resume values and version-specific option
termination. Construct no additional permission or shell-interpreted options.

REQ-CARET-AGENT-CLI-003: bind exact authorized task scope/content and retained
policy digests to ordered invocation evidence. Integrity matches alone do not
prove installed CLI identity, image provenance or launch authorization.

The binding includes policy source/catalog digests, exact authorized task scope
and content digest, provider/version/executable digest, mode/output format and
ordered argument digests. Resume IDs are explicit; no last-session fallback,
arbitrary extra flags or permission-bypass options are generated. Existing
unversioned local Caret launch paths are not certified by this new contract.

The six-scenario production-import unit spec and its mirrored manual cover the
pure boundary. The retained controller resolver and real provider probe must
consume it before this integration can be called executable AgentSession support.
