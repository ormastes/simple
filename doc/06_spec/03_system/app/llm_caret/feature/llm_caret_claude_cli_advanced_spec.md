# LLM Caret Advanced Claude CLI Forwarding

> Direct offline contract for the production `claude_cli_send` advanced
> argument boundary. This is not cached-Caret wrapper qualification.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

This manual records zero executed scenarios: the qualified pure-Simple test
runtime is not currently available. It describes the executable contract and
does not claim a live-provider, CLI-wrapper, or TUI PASS.

<details>
<summary>Full Scenario Manual</summary>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application / provider CLI |
| Requirement | REQ-LLM-CARET-FULL-003 |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl` |
| Fixture | `test/fixtures/llm_caret/mock_claude_cli.shs` |
| Evidence | Runner `exec` and textual response capture |

## Scope and Safety

The spec calls the production `app.llm_caret.claude_cli.claude_cli_send`
function. Its local executable fixture receives a one-shot JSON request and
never accesses credentials, an installed `claude` executable, or the network.
The contract is deliberately distinct from cached `bin/caret` qualification,
which is owned by `llm_caret_cli_cached_spec.spl`.

## Scenario

### should forward the advanced request through the production Claude sender

1. Prepare offline Claude CLI fixture.
2. Send advanced provider request.
3. Check forwarded response and status.

The request fixes the sender inputs to session `advanced-resume`, maximum turns
`3`, schema `{"type":"object"}`, and a single variadic `--allowedTools`
vector ordered as `Read`, then `Write`; `--fixture-extra` proves the approved
extra-argument tail is retained. The fixture rejects any missing, reordered,
or malformed field and only then emits deterministic JSON. The response must be
non-error `advanced-ok`, model `sonnet`, session `advanced-session`, and the
parser-default `end_turn` stop reason.

## Execution Boundary

Run with the self-hosted runtime once it is available:

```sh
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl --mode=native
```

Then regenerate this manual with `bin/simple spipe-docgen ... --output
doc/06_spec --no-index`. A source fallback, bootstrap seed, unavailable runtime,
or fixture failure is not execution evidence.

</details>
