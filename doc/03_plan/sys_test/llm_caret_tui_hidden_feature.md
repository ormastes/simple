# LLM Caret TUI and Hidden-Feature Test-Plan Appendix

This appendix covers the deterministic TUI and hidden-feature lane that
complements `llm_caret_claude_cli_harden.md`. It does not call Claude, OpenAI,
or another paid API.

## Frozen test interface

- Cases: `CaretTuiFeatureCase`, `CaretHiddenFeatureCase`
- Setup/action/check helpers: `setup_tui_fixture`, `run_tui_action`,
  `check_tui_snapshot`, `setup_hidden_feature_fixture`,
  `check_hidden_feature_gate`
- Manual steps: `Open the caret TUI`,
  `Send a prompt through the visible input`, `Check transcript and status`,
  `Enable the hidden-feature fixture`, `Check the hidden-feature gate`

## Scope and evidence

The spec drives the production `run_chat_tui_submission` transition, input
widget model, dummy responder, styled transcript state, slash-provider hook,
permission-gated tool loop, retry decisions, Claude REPL error route,
production hidden-command dispatch/admission, and the SGTTI source boundary.
It does not drive raw-terminal key reading or frame timing. The compact
component snapshot is written to
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature/caret_tui.txt`.

A live PTY, ANSI/pixel screenshot, paid provider, network retry, and production
SGTTI allocation profile are excluded. The SGTTI check is explicitly limited
to absence from `src/app/llm_caret/main.spl` and `chat_tui.spl`.

## Traceability

| Behavior | Executable evidence | Generated manual | Status |
|---|---|---|---|
| Visible prompt, dummy reply, provider/model/session status | `test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.md` | Designed |
| Provider switch is visible in transcript and refreshed status | same | same | Implemented; executable run blocked by stale self-hosted runtime |
| Permission denial is rendered as tool error | same | same | Designed |
| Retry admission, cap, Retry-After, visible query error route | same | same | Designed |
| Hidden command is rejected by default, admitted by fixture, and stays non-visible | same | same | Implemented; executable run blocked by stale self-hosted runtime |
| Disabled command remains rejected with hidden features enabled | same | same | Implemented; executable run blocked by stale self-hosted runtime |
| Normal Caret entrypoints exclude SGTTI imports/construction | same | same | Designed |

## Pass/fail criteria

PASS requires all seven examples to execute with real assertions, the TUI capture
to round-trip exactly, the hidden command to remain non-visible, and the
production entrypoint/TUI sources to remain SGTTI-free. Full raw-terminal-loop
input and frame evidence remains a separate required gap before a broad TUI
production-readiness claim.

The generated manual must report `0 stubs`, retain the scope limitation above,
show all five frozen manual-step strings, and include folded executable source.
