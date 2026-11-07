# Caret legacy provider launch guard

Source: `test/03_system/app/llm_caret/feature/provider_launch_authority_spec.spl`.
Status: authored companion manual; execution and docgen UNRUN (no admitted
product runtime). No provider CLI or smux runtime qualification is claimed.

1. Build fresh default Claude and Codex plans. Their established argv is
   preserved and the compatibility guard accepts both.
2. Build Gemini, Kimi and OpenCode plans, including supported aliases. Their
   argv is empty; async and messaging launch return an adapter-required reason
   and pid -1 before invoking the configured executable.
3. Submit a manually constructed nonempty Kimi plan and an empty Claude plan.
   Both return adapter-required reasons and pid -1.
4. Request Codex resume. The legacy plan is empty and launch refuses it;
   Claude's `--resume` flag is never applied to Codex.
5. Request an unknown provider and a team plan. Existing unknown-provider and
   nonexecutable-team refusal reasons remain visible.
6. Request a pane team with valid Claude first and unsupported Kimi second.
   The entire request fails before creating a smux session; no pane agent is
   recorded and the session count remains unchanged.

Requirements: REQ-CARET-LAUNCH-001 through REQ-CARET-LAUNCH-003, defined in
`doc/05_design/caret_provider_launch_guard.md`.
