# Caret legacy provider launch guard

Scope: prevent legacy launch paths from applying Claude CLI arguments to
Gemini, Kimi or OpenCode, and from applying Claude's resume flag to Codex.
This is a pre-spawn compatibility guard, not execution authorization.

REQ-CARET-LAUNCH-001: preserve default Claude and explicit Claude/Codex fresh
legacy plans. Preserve unknown-provider and nonexecutable-team errors.

REQ-CARET-LAUNCH-002: unsupported provider aliases, empty executable plans and
Codex legacy resume return `provider_adapter_required:<provider>` before
async or messaging spawn. The public launch boundary also rejects manually
constructed nonempty unsupported-provider plans. The established legacy
Claude interface remains available; no CLI version or executable identity
qualification is implied by this compatibility behavior.

REQ-CARET-LAUNCH-003: pane teams preflight every member before creating any
smux session or child. A supported first member followed by an unsupported
member must leave the session registry unchanged. smux remains the stream and
pane-child owner; this change adds no reader or scheduler.

The single shared `agent_plan_launch_error_v1` guard is used by the async,
messaging and pane paths. Unsupported builder output has empty argv. Codex
resume needs a version-specific adapter: installed `codex-cli 0.167.0` help
reports `codex exec resume [OPTIONS] [SESSION_ID] [PROMPT]`, not `--resume`.
No replacement resume flags are guessed here.

Production-import regression:
`test/03_system/app/llm_caret/feature/provider_launch_authority_spec.spl`.
Its six scenarios cover fresh-plan preservation, both spawn refusal paths,
forged unsupported and empty plans, Codex resume, unknown/team semantics and
whole-team preflight without session effects. Existing copied-implementation
unit specs are not evidence for the production fix.

Provenance: the isolated implementation follows the legacy fail-closed idea
observed read-only in the unrelated dirty main worktree, with additional
Codex resume and manually constructed unsupported-plan rejection. No main
worktree file was copied. Main's unmerged `agent_cli_v1` and mux V3 contracts
are not admitted by this change. Checked launch, version/digest validation,
generation/authority execution integration and V3 adoption remain separate.

Validation status: executable scenarios and generated-manual tooling remain
UNRUN because this lane has no admitted product runtime. Static review cannot
qualify CLI execution, smux runtime behavior, provider conformance or release.
The companion manual is authored from the spec and is not generated evidence.
