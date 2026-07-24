# LLM Caret Claude CLI Feature Contract

> This offline system specification exercises the accepted Claude CLI feature map without network access. The provider cases use the production argument builder and structured-response parser. Hidden command checks use production fast-mode and remote-review command gates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude CLI Feature Contract

This offline system specification exercises the accepted Claude CLI feature map without network access. The provider cases use the production argument builder and structured-response parser. Hidden command checks use production fast-mode and remote-review command gates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md |
| Plan | doc/03_plan/sys_test/llm_caret_claude_cli_full_parity.md |
| Design | doc/05_design/llm_caret_claude_cli_full_parity.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This offline system specification exercises the accepted Claude CLI feature
map without network access. The provider cases use the production argument
builder, structured-response parser, and dispatch path with a local executable
fixture. Hidden command checks use production fast-mode and remote-review
command gates.

The fixture intentionally does not execute `claude`; paid live acceptance is a
separate opt-in lane.

## Scope

The specification covers:

- accepted feature-map presence;
- the CLI capsule row;
- fast-command mapping;
- review-command mapping;
- prompt argument construction;
- JSON output selection;
- model selection;
- system-prompt forwarding;
- session resume;
- maximum-turn forwarding;
- omission of Claude Code's removed maximum-token flag;
- structured-output schema forwarding;
- allowed-tool forwarding;
- extra-argument forwarding;
- verbose-output selection;
- mandatory verbose mode for stream-json;
- Claude Code system, assistant, and result stream envelopes;
- aggregation of multiple assistant text blocks;
- JSON-schema `structured_output` result envelopes;
- rejection of malformed or contract-free JSON responses;
- offline production subprocess dispatch;
- offline NDJSON stream subprocess dispatch, empty/malformed output rejection,
  and terminal-event enforcement;
- subprocess-error secret redaction;
- protocol-level stream error/result secret redaction;
- public `llm_init`/`llm_chat` history routing;
- successful structured responses;
- usage counters;
- structured provider errors;
- default stop reasons;
- fast-command disabled visibility;
- fast-command enabled visibility;
- disabled-gate side-effect prevention;
- permanently hidden remote review metadata.

The specification does not cover:

- live authentication;
- remote billing;
- Claude service availability;
- terminal rendering;
- full-screen TUI input;
- browser or Metal GUI rendering;
- network retry timing;
- provider rate limits.

## Syntax

```bash
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl --output doc/06_spec --no-index
```

## Accepted Feature Map

The accepted inventory is
`doc/03_plan/trace/llm_caret_claude_cli_full_parity_feature_matrix.tsv`.
The scenario requires rows for the top-level CLI capsule and the two hidden
feature witnesses used by this test. Missing rows fail before provider behavior
is accepted.

## Frozen Test Interface

`CaretCliFeatureCase` carries one deterministic provider request and response.
The helper vocabulary is frozen for parallel CLI and TUI work:

- `setup_cli_fixture`
- `run_cli_case`
- `check_cli_result`
- `setup_hidden_feature_fixture`
- `check_hidden_feature_gate`

Displayed manual flow uses these exact steps:

1. `Load the accepted Claude feature map`
2. `Invoke the caret CLI provider`
3. `Check the structured CLI response`
4. `Enable the hidden-feature fixture`
5. `Check the hidden-feature gate`

## Provider Cases

### Single Shot

The first case proves the required prompt, JSON output format, model, and
maximum-turn arguments. Its response proves content, model identity, session
identity, token usage, and a non-error status.

### Resume With Tools

The second case adds a system prompt, an existing session identifier, and two
allowed tools. The structured response uses the alternative token-usage field
names accepted by the production parser.

### Structured Error

The third case proves an `is_error` response becomes a structured error with
the `error` stop reason. It is an executable reject path, not a placeholder
pass.

## Hidden Feature Contract

The fast command is hidden and disabled when its feature gate is false. Enabling
the fixture exposes the command and preserves its immediate-command metadata.
Calling the disabled command must not prefetch, switch models, or enable fast
mode.

Remote review is a distinct permanently hidden command. Its hidden status is
checked separately so an enabled fast fixture cannot accidentally make every
hidden command visible.

## Failure Handling

The test fails when:

- the accepted map is absent;
- a required feature row is absent;
- argument construction drops a configured field;
- the production provider bypasses the tested wrapper;
- the public convenience API bypasses the tested wrapper;
- a removed Claude flag reaches the subprocess;
- structured response parsing loses content or usage;
- an error response is accepted as success;
- disabled fast mode becomes visible;
- a disabled command performs prefetch work;
- the remote review command becomes visible.

## Safety

All provider responses come from local immutable fixtures. The executable
fixture rejects removed flags and never accesses the network. No Claude process
is started, no API key is read, and no paid API call can occur from this file.

## Evidence

A passing run proves the production CLI builder/parser and hidden-command gate
functions satisfy this bounded contract. It complements, but does not replace,
the traceability, full-parity inventory, implementation, and opt-in live gates.

## Scenarios

### LLM caret Claude CLI feature contract

### REQ-LLM-CARET-FULL-003: accepted CLI provider features

#### should map production CLI argument and response behavior

- Load the accepted Claude feature map
   - Expected: cases.len() equals `3`
- Invoke the caret CLI provider
- Check the structured CLI response
- check cli result


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the accepted Claude feature map")
expect(file_exists(FEATURE_MAP)).to_be(true)
val feature_map = file_read(FEATURE_MAP)
expect(feature_map).to_contain("\tcli\t")
expect(feature_map).to_contain("commands/fast")
expect(feature_map).to_contain("commands/review")

val cases = setup_cli_fixture()
expect(cases.len()).to_equal(3)
for case in cases:
    step("Invoke the caret CLI provider")
    val response = run_cli_case(case)
    step("Check the structured CLI response")
    check_cli_result(case, response)
```

</details>

### REQ-LLM-CARET-FULL-006: hidden feature gates

#### should keep gated and permanently hidden commands unavailable

- Enable the hidden-feature fixture
   - Expected: fixtures.len() equals `2`
- Check the hidden-feature gate
- check hidden feature gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enable the hidden-feature fixture")
val fixtures = setup_hidden_feature_fixture()
expect(fixtures.len()).to_equal(2)
step("Check the hidden-feature gate")
check_hidden_feature_gate(fixtures)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_claude_cli_full_parity.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_full_parity.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>
