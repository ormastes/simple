# provider_spec

> Purpose: Prove that Provider List.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# provider_spec

Purpose: Prove that Provider List.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_caret/provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Provider List.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Provider List

#### should list all providers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should list all providers
- Verify: should list all providers
   - Expected: providers.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should list all providers")
step("Verify: should list all providers")
# @req: REQ-APP-LLM-CARET-001
val providers = list_providers()
expect(providers.len()).to_equal(7)  # oracle: 7 — named expected value from the requirement
```

</details>

#### should include dummy

- should include dummy
- Verify: should include dummy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include dummy")
step("Verify: should include dummy")
expect(is_valid_provider("dummy")).to_be(true)
```

</details>

#### should include claude_cli

- should include claude_cli
- Verify: should include claude_cli


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include claude_cli")
step("Verify: should include claude_cli")
val providers = list_providers()
var found = false
for p in providers:
    if p == "claude_cli":
        found = true
expect(found).to_be(true)
```

</details>

#### should include opencode_cli

- should include opencode_cli
- Verify: should include opencode_cli


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include opencode_cli")
step("Verify: should include opencode_cli")
val providers = list_providers()
var found = false
for p in providers:
    if p == "opencode_cli":
        found = true
expect(found).to_be(true)
```

</details>

#### should include claude_api

- should include claude_api
- Verify: should include claude_api


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include claude_api")
step("Verify: should include claude_api")
val providers = list_providers()
var found = false
for p in providers:
    if p == "claude_api":
        found = true
expect(found).to_be(true)
```

</details>

#### should include openai

- should include openai
- Verify: should include openai


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include openai")
step("Verify: should include openai")
val providers = list_providers()
var found = false
for p in providers:
    if p == "openai":
        found = true
expect(found).to_be(true)
```

</details>

#### should include openai_compat

- should include openai_compat
- Verify: should include openai_compat


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include openai_compat")
step("Verify: should include openai_compat")
val providers = list_providers()
var found = false
for p in providers:
    if p == "openai_compat":
        found = true
expect(found).to_be(true)
```

</details>

#### should include local_torch

- should include local_torch
- Verify: should include local_torch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include local_torch")
step("Verify: should include local_torch")
val providers = list_providers()
var found = false
for p in providers:
    if p == "local_torch":
        found = true
expect(found).to_be(true)
```

</details>

### Provider Validation

#### should validate claude_cli

- should validate claude_cli
- Verify: should validate claude_cli


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should validate claude_cli")
step("Verify: should validate claude_cli")
expect(is_valid_provider("claude_cli")).to_be(true)
```

</details>

#### should validate opencode_cli

- should validate opencode_cli
- Verify: should validate opencode_cli


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should validate opencode_cli")
step("Verify: should validate opencode_cli")
expect(is_valid_provider("opencode_cli")).to_be(true)
```

</details>

#### should validate claude_api

- should validate claude_api
- Verify: should validate claude_api


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should validate claude_api")
step("Verify: should validate claude_api")
expect(is_valid_provider("claude_api")).to_be(true)
```

</details>

#### should validate openai

- should validate openai
- Verify: should validate openai


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should validate openai")
step("Verify: should validate openai")
expect(is_valid_provider("openai")).to_be(true)
```

</details>

#### should validate openai_compat

- should validate openai_compat
- Verify: should validate openai_compat


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should validate openai_compat")
step("Verify: should validate openai_compat")
expect(is_valid_provider("openai_compat")).to_be(true)
```

</details>

#### should validate local_torch

- should validate local_torch
- Verify: should validate local_torch


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should validate local_torch")
step("Verify: should validate local_torch")
expect(is_valid_provider("local_torch")).to_be(true)
```

</details>

#### should reject an unknown provider

- should reject an unknown provider
- Verify: should reject an unknown provider


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject an unknown provider")
step("Verify: should reject an unknown provider")
expect(is_valid_provider("unknown")).to_be(false)
```

</details>

#### should reject an empty provider

- should reject an empty provider
- Verify: should reject an empty provider


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject an empty provider")
step("Verify: should reject an empty provider")
expect(is_valid_provider("")).to_be(false)
```

</details>

### LLMResponse Error

#### should create an error response

- should create an error response
- Verify: should create an error response
   - Expected: resp.error equals `connection refused`
   - Expected: resp.provider equals `claude_cli`
   - Expected: resp.stop_reason equals `error`
   - Expected: resp.content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create an error response")
step("Verify: should create an error response")
val resp = new_llm_error("claude_cli", "connection refused")
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("connection refused")
expect(resp.provider).to_equal("claude_cli")
expect(resp.stop_reason).to_equal("error")
expect(resp.content).to_equal("")
```

</details>

### Dummy Provider

#### should always return hello without external configuration

- should always return hello without external configuration
- Verify: should always return hello without external configuration
   - Expected: resp.content equals `hello`
   - Expected: resp.model equals `dummy-hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should always return hello without external configuration")
step("Verify: should always return hello without external configuration")
val resp = dispatch_send("dummy", "anything", "", "", "", "", "", "", 0, 0, "[]")
expect(resp.is_error).to_be(false)
expect(resp.content).to_equal("hello")
expect(resp.model).to_equal("dummy-hello")
```

</details>

#### should reject Claude-only advanced arguments for another provider

- should reject Claude-only advanced arguments for another provider
- Verify: should reject Claude-only advanced arguments for another provider
   - Expected: resp.provider equals `dummy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject Claude-only advanced arguments for another provider")
step("Verify: should reject Claude-only advanced arguments for another provider")
val resp = dispatch_send_advanced(
    "dummy", "anything", "", "", "", "", "", "", 0, 0, "[]",
    "{\"type\":\"object\"}", ["Read"], []
)
expect(resp.is_error).to_be(true)
expect(resp.provider).to_equal("dummy")
expect(resp.error).to_contain("require claude_cli")
```

</details>

### Provider Dispatch Failures

#### should reject unknown and misconfigured local providers

- should reject unknown and misconfigured local providers
- Verify: should reject unknown and misconfigured local providers
   - Expected: unknown.provider equals `unknown`
   - Expected: unknown.error equals `unknown provider: unknown`
   - Expected: unavailable.provider equals `local_torch`
   - Expected: unavailable.error equals `model_path not configured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject unknown and misconfigured local providers")
step("Verify: should reject unknown and misconfigured local providers")
val unknown = dispatch_send(
    "unknown", "anything", "", "", "", "", "", "", 0, 0, "[]"
)
expect(unknown.is_error).to_be(true)
expect(unknown.provider).to_equal("unknown")
expect(unknown.error).to_equal("unknown provider: unknown")

val unavailable = dispatch_send(
    "local_torch", "anything", "", "", "", "", "", "", 0, 0, "[]"
)
expect(unavailable.is_error).to_be(true)
expect(unavailable.provider).to_equal("local_torch")
expect(unavailable.error).to_equal("model_path not configured")
```

</details>

#### should reject remote providers without credentials before network access

- should reject remote providers without credentials before network access
- Verify: should reject remote providers without credentials before network access
   - Expected: anthropic.provider equals `claude_api`
   - Expected: anthropic.error equals `ANTHROPIC_API_KEY not set`
   - Expected: openai.provider equals `openai`
   - Expected: openai.error equals `OPENAI_API_KEY not set`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject remote providers without credentials before network access")
step("Verify: should reject remote providers without credentials before network access")
val anthropic = dispatch_send(
    "claude_api", "", "", "", "", "", "", "", 0, 0, "[]"
)
expect(anthropic.is_error).to_be(true)
expect(anthropic.provider).to_equal("claude_api")
expect(anthropic.error).to_equal("ANTHROPIC_API_KEY not set")

val openai = dispatch_send(
    "openai", "", "", "", "", "", "", "", 0, 0, "[]"
)
expect(openai.is_error).to_be(true)
expect(openai.provider).to_equal("openai")
expect(openai.error).to_equal("OPENAI_API_KEY not set")
```

</details>

#### should preserve Claude CLI fields through advanced dispatch

- should preserve Claude CLI fields through advanced dispatch
- Verify: should preserve Claude CLI fields through advanced dispatch
   - Expected: resp.error equals ``
   - Expected: resp.provider equals `claude_cli`
   - Expected: resp.content equals `advanced-ok`
   - Expected: resp.model equals `sonnet`
   - Expected: resp.session_id equals `advanced-session`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should preserve Claude CLI fields through advanced dispatch")
step("Verify: should preserve Claude CLI fields through advanced dispatch")
# The mock fixture fails closed (exit 70) unless the resume session,
# max_turns and the FULL tool vector are forwarded, so these arguments
# must match `test/fixtures/llm_caret/mock_claude_cli.shs`.
val resp = dispatch_send_advanced(
    "claude_cli", "fixture-advanced", "sonnet", "", "",
    MOCK_CLAUDE, "", "advanced-resume", 3, 0, "[]",
    "{\"type\":\"object\"}", ["Read", "Write"], ["--fixture-extra"]
)
expect(resp.is_error).to_be(false)
expect(resp.error).to_equal("")
expect(resp.provider).to_equal("claude_cli")
expect(resp.content).to_equal("advanced-ok")
expect(resp.model).to_equal("sonnet")
expect(resp.session_id).to_equal("advanced-session")
```

</details>

#### should preserve the Claude CLI session on a plain send

- should preserve the Claude CLI session on a plain send
- Verify: should preserve the Claude CLI session on a plain send
   - Expected: resp.provider equals `claude_cli`
   - Expected: resp.content equals `fixture-ok`
   - Expected: resp.session_id equals `resume-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should preserve the Claude CLI session on a plain send")
step("Verify: should preserve the Claude CLI session on a plain send")
val resp = dispatch_send(
    "claude_cli", "fixture-success", "sonnet", "", "",
    MOCK_CLAUDE, "Be concise", "", 0, 0, "[]"
)
expect(resp.is_error).to_be(false)
expect(resp.provider).to_equal("claude_cli")
expect(resp.content).to_equal("fixture-ok")
expect(resp.session_id).to_equal("resume-1")
```

</details>

#### should leave the session empty when the Claude CLI fails closed

- should leave the session empty when the Claude CLI fails closed
- Verify: should leave the session empty when the Claude CLI fails closed
   - Expected: resp.provider equals `claude_cli`
   - Expected: resp.session_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should leave the session empty when the Claude CLI fails closed")
step("Verify: should leave the session empty when the Claude CLI fails closed")
# Same prompt as the advanced example, but without the resume session
# and full tool vector the fixture requires: exit 70, no session.
val resp = dispatch_send_advanced(
    "claude_cli", "fixture-advanced", "sonnet", "", "",
    MOCK_CLAUDE, "", "", 0, 0, "[]",
    "{\"type\":\"object\"}", ["Read"], ["--fixture-extra"]
)
expect(resp.is_error).to_be(true)
expect(resp.provider).to_equal("claude_cli")
expect(resp.error).to_contain("exited with code 70")
expect(resp.session_id).to_equal("")
```

</details>

### Uninitialized Public LLM State

#### should reject chat and direct send before initialization

- should reject chat and direct send before initialization
- Verify: should reject chat and direct send before initialization
   - Expected: llm_history_len() equals `0`
   - Expected: llm_history_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject chat and direct send before initialization")
step("Verify: should reject chat and direct send before initialization")
expect(llm_history_len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(llm_chat("not initialized")).to_contain(
    "call llm_init_defaults() or llm_init() first"
)
expect(llm_send("not initialized")).to_contain(
    "call llm_init_defaults() or llm_init() first"
)
expect(llm_history_len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### Production Provider Owners

#### should normalize a missing Claude API key through direct and public dispatch

- should normalize a missing Claude API key through direct and public dispatch
- Prepare provider dispatch inputs
- Dispatch through the production owner
- Check exact normalized response and ownership
   - Expected: direct.content equals ``
   - Expected: direct.model equals ``
   - Expected: direct.provider equals `claude_api`
   - Expected: direct.session_id equals ``
   - Expected: direct.stop_reason equals `error`
   - Expected: direct.input_tokens equals `0`
   - Expected: direct.output_tokens equals `0`
   - Expected: direct.error equals `ANTHROPIC_API_KEY not set`
   - Expected: direct.raw equals ``
   - Expected: public equals `ERROR: ANTHROPIC_API_KEY not set`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should normalize a missing Claude API key through direct and public dispatch")
step("Prepare provider dispatch inputs")
val old_key = env_get("ANTHROPIC_API_KEY") ?? ""
val key_cleared = env_set("ANTHROPIC_API_KEY", "")
llm_init("claude_api", "")
llm_set_api_key("")

step("Dispatch through the production owner")
val direct = dispatch_send(
    "claude_api", "hello", "", "", "", "", "", "",
    0, 0, "[{\"role\":\"user\",\"content\":\"hello\"}]"
)
val public = llm_send("hello")
llm_clear()
val key_restored = env_set("ANTHROPIC_API_KEY", old_key)

step("Check exact normalized response and ownership")
expect(key_cleared).to_be(true)
expect(key_restored).to_be(true)
expect(direct.content).to_equal("")
expect(direct.model).to_equal("")
expect(direct.provider).to_equal("claude_api")
expect(direct.session_id).to_equal("")
expect(direct.stop_reason).to_equal("error")
expect(direct.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(direct.output_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(direct.error).to_equal("ANTHROPIC_API_KEY not set")
expect(direct.is_error).to_be(true)
expect(direct.raw).to_equal("")
expect(public).to_equal("ERROR: ANTHROPIC_API_KEY not set")
```

</details>

#### should reset stale credentials and normalize a missing OpenAI API key

- should reset stale credentials and normalize a missing OpenAI API key
- Prepare provider dispatch inputs
- Dispatch through the production owner
- Check exact normalized response and ownership
   - Expected: direct.content equals ``
   - Expected: direct.model equals ``
   - Expected: direct.provider equals `openai`
   - Expected: direct.session_id equals ``
   - Expected: direct.stop_reason equals `error`
   - Expected: direct.input_tokens equals `0`
   - Expected: direct.output_tokens equals `0`
   - Expected: direct.error equals `OPENAI_API_KEY not set`
   - Expected: direct.raw equals ``
   - Expected: public equals `ERROR: OPENAI_API_KEY not set`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reset stale credentials and normalize a missing OpenAI API key")
step("Prepare provider dispatch inputs")
val old_key = env_get("OPENAI_API_KEY") ?? ""
val key_cleared = env_set("OPENAI_API_KEY", "")
llm_init("claude_api", "stale-model")
llm_set_api_key("stale-provider-key")
llm_set_base_url("https://stale-provider.invalid")
llm_init("openai", "")

step("Dispatch through the production owner")
val direct = dispatch_send(
    "openai", "hello", "", "", "", "", "", "",
    0, 0, "[{\"role\":\"user\",\"content\":\"hello\"}]"
)
val public = llm_send("hello")
llm_clear()
val key_restored = env_set("OPENAI_API_KEY", old_key)

step("Check exact normalized response and ownership")
expect(key_cleared).to_be(true)
expect(key_restored).to_be(true)
expect(direct.content).to_equal("")
expect(direct.model).to_equal("")
expect(direct.provider).to_equal("openai")
expect(direct.session_id).to_equal("")
expect(direct.stop_reason).to_equal("error")
expect(direct.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(direct.output_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(direct.error).to_equal("OPENAI_API_KEY not set")
expect(direct.is_error).to_be(true)
expect(direct.raw).to_equal("")
expect(public).to_equal("ERROR: OPENAI_API_KEY not set")
```

</details>

#### should normalize a missing local Torch model through direct and public dispatch

- should normalize a missing local Torch model through direct and public dispatch
- Prepare provider dispatch inputs
- Dispatch through the production owner
- Check exact normalized response and ownership
   - Expected: direct.content equals ``
   - Expected: direct.model equals ``
   - Expected: direct.provider equals `local_torch`
   - Expected: direct.session_id equals ``
   - Expected: direct.stop_reason equals `error`
   - Expected: direct.input_tokens equals `0`
   - Expected: direct.output_tokens equals `0`
   - Expected: direct.error equals `model_path not configured`
   - Expected: direct.raw equals ``
   - Expected: public equals `ERROR: model_path not configured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should normalize a missing local Torch model through direct and public dispatch")
step("Prepare provider dispatch inputs")
llm_init("local_torch", "")
llm_set_cli_path("")

step("Dispatch through the production owner")
val direct = dispatch_send(
    "local_torch", "hello", "", "", "", "", "", "",
    0, 0, "[]"
)
val public = llm_send("hello")

step("Check exact normalized response and ownership")
expect(direct.content).to_equal("")
expect(direct.model).to_equal("")
expect(direct.provider).to_equal("local_torch")
expect(direct.session_id).to_equal("")
expect(direct.stop_reason).to_equal("error")
expect(direct.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(direct.output_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(direct.error).to_equal("model_path not configured")
expect(direct.is_error).to_be(true)
expect(direct.raw).to_equal("")
expect(public).to_equal("ERROR: model_path not configured")
llm_clear()
```

</details>

#### should preserve dummy success and exact unknown-provider failures

- should preserve dummy success and exact unknown-provider failures
- Prepare provider dispatch inputs
- Dispatch through the production owner
- Check exact normalized response and ownership
   - Expected: dummy.content equals `hello`
   - Expected: dummy.model equals `dummy-hello`
   - Expected: dummy.provider equals `dummy`
   - Expected: dummy.session_id equals `dummy-session`
   - Expected: dummy.stop_reason equals `end_turn`
   - Expected: dummy.input_tokens equals `0`
   - Expected: dummy.output_tokens equals `1`
   - Expected: dummy.error equals ``
   - Expected: dummy.raw equals ``
   - Expected: public equals `hello`
   - Expected: unknown.provider equals `unknown`
   - Expected: unknown.session_id equals ``
   - Expected: unknown.stop_reason equals `error`
   - Expected: unknown.input_tokens equals `0`
   - Expected: unknown.output_tokens equals `0`
   - Expected: unknown.error equals `unknown provider: unknown`
   - Expected: unknown.raw equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should preserve dummy success and exact unknown-provider failures")
step("Prepare provider dispatch inputs")
llm_init("dummy", "dummy-hello")

step("Dispatch through the production owner")
val dummy = dispatch_send(
    "dummy", "hello", "", "", "", "", "", "dummy-session",
    0, 0, "[]"
)
val public = llm_send("hello")
val unknown = dispatch_send(
    "unknown", "hello", "", "", "", "", "", "",
    0, 0, "[]"
)

step("Check exact normalized response and ownership")
expect(dummy.content).to_equal("hello")
expect(dummy.model).to_equal("dummy-hello")
expect(dummy.provider).to_equal("dummy")
expect(dummy.session_id).to_equal("dummy-session")
expect(dummy.stop_reason).to_equal("end_turn")
expect(dummy.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(dummy.output_tokens).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(dummy.error).to_equal("")
expect(dummy.is_error).to_be(false)
expect(dummy.raw).to_equal("")
expect(public).to_equal("hello")
expect(unknown.provider).to_equal("unknown")
expect(unknown.session_id).to_equal("")
expect(unknown.stop_reason).to_equal("error")
expect(unknown.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(unknown.output_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(unknown.error).to_equal("unknown provider: unknown")
expect(unknown.is_error).to_be(true)
expect(unknown.raw).to_equal("")
llm_clear()
```

</details>

#### should keep transport and parsing in each production provider owner

- should keep transport and parsing in each production provider owner
- Prepare provider dispatch inputs
- Dispatch through the production owner
- Check exact normalized response and ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should keep transport and parsing in each production provider owner")
step("Prepare provider dispatch inputs")
val provider_path = "src/app/llm_caret/provider.spl"
val public_path = "src/app/llm_caret/mod.spl"

step("Dispatch through the production owner")
val provider_source = rt_file_read_text(provider_path) ?? ""
val public_source = rt_file_read_text(public_path) ?? ""

step("Check exact normalized response and ownership")
expect(provider_source.contains("http_request_raw")).to_be(false)
expect(provider_source.contains("with_retry")).to_be(false)
expect(provider_source.contains("fn _escape_json")).to_be(false)
expect(provider_source.contains("fn _extract_json")).to_be(false)
expect(provider_source.contains("fn _LB")).to_be(false)
expect(provider_source.contains("fn _RB")).to_be(false)
expect(provider_source.contains("fn _Q")).to_be(false)
expect(provider_source).to_contain("val resp = claude_api_send(")
expect(provider_source).to_contain("val resp = openai_send(")
expect(provider_source).to_contain("val resp = compat_send(")
expect(provider_source).to_contain("val resp = local_torch_send(")
expect(public_source.contains("http_request_raw")).to_be(false)
expect(public_source.contains("fn _send_")).to_be(false)
expect(public_source).to_contain("dispatch_send(")
```

</details>

### Public LLM State

#### should serialize public history with escaped message content

- should serialize public history with escaped message content
- Verify: should serialize public history with escaped message content
   - Expected: llm_chat("say \"hi\"\nnext") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize public history with escaped message content")
step("Verify: should serialize public history with escaped message content")
llm_init("dummy", "dummy-hello")
expect(llm_chat("say \"hi\"\nnext")).to_equal("hello")
expect(_build_messages_json()).to_equal(
    "[{\"role\":\"user\",\"content\":\"say \\\"hi\\\"\\nnext\"}," +
    "{\"role\":\"assistant\",\"content\":\"hello\"}]"
)
expect(_build_direct_messages_json("say \"hi\"\nnext")).to_equal(
    "[{\"role\":\"user\",\"content\":\"say \\\"hi\\\"\\nnext\"}]"
)
llm_clear()
```

</details>

#### should reject unsupported providers through both public send routes

- should reject unsupported providers through both public send routes
- Verify: should reject unsupported providers through both public send routes
   - Expected: llm_history_len() equals `1`
   - Expected: llm_history_role(0) equals `user`
   - Expected: llm_history_content(0) equals `hello`
   - Expected: llm_history_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject unsupported providers through both public send routes")
step("Verify: should reject unsupported providers through both public send routes")
llm_init("unsupported", "none")
val chat_response = llm_chat("hello")
expect(chat_response).to_equal(
    "ERROR: unknown provider: unsupported"
)
expect(llm_history_len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(llm_history_role(0)).to_equal("user")
expect(llm_history_content(0)).to_equal("hello")

llm_init("unsupported", "none")
val send_response = llm_send("hello")
expect(send_response).to_equal(
    "ERROR: unknown provider: unsupported"
)
expect(llm_history_len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should keep API-only settings from altering Claude CLI requests

- should keep API-only settings from altering Claude CLI requests
- Verify: should keep API-only settings from altering Claude CLI requests
   - Expected: llm_send("fixture-success") equals `fixture-ok`
   - Expected: llm_provider() equals `claude_cli`
   - Expected: llm_model() equals `sonnet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should keep API-only settings from altering Claude CLI requests")
step("Verify: should keep API-only settings from altering Claude CLI requests")
llm_init("claude_cli", "sonnet")
llm_set_api_key("offline-key")
llm_set_base_url("http://offline.invalid")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
expect(llm_provider()).to_equal("claude_cli")
expect(llm_model()).to_equal("sonnet")
llm_clear()
```

</details>

#### should reset public conversation state on initialization

- should reset public conversation state on initialization
- Verify: should reset public conversation state on initialization
   - Expected: llm_chat("fixture-success") equals `fixture-ok`
   - Expected: llm_history_len() equals `2`
   - Expected: llm_history_len() equals `0`
   - Expected: llm_send("fixture-no-system") equals `no-system-ok`
   - Expected: llm_send("fixture-success") equals `fixture-ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reset public conversation state on initialization")
step("Verify: should reset public conversation state on initialization")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_chat("fixture-success")).to_equal("fixture-ok")
expect(llm_history_len()).to_equal(2)  # oracle: 2 — named expected value from the requirement

llm_system("stale system prompt")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
expect(llm_history_len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(llm_send("fixture-no-system")).to_equal("no-system-ok")

llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
```

</details>

#### should reuse a successful Claude session on the next public send

- should reuse a successful Claude session on the next public send
- Verify: should reuse a successful Claude session on the next public send
   - Expected: llm_send("fixture-success") equals `fixture-ok`
   - Expected: llm_send("fixture-requires-resume") equals `resumed-ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reuse a successful Claude session on the next public send")
step("Verify: should reuse a successful Claude session on the next public send")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
expect(llm_send("fixture-requires-resume")).to_equal("resumed-ok")
llm_clear()
```

</details>

#### should keep a failed Claude response from poisoning public session state

- should keep a failed Claude response from poisoning public session state
- Verify: should keep a failed Claude response from poisoning public session state
   - Expected: llm_history_len() equals `1`
   - Expected: llm_history_role(0) equals `user`
   - Expected: llm_history_content(0) equals `fixture-error-session`
   - Expected: llm_send("fixture-success") equals `fixture-ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should keep a failed Claude response from poisoning public session state")
step("Verify: should keep a failed Claude response from poisoning public session state")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
val failed = llm_chat("fixture-error-session")
expect(failed).to_start_with("ERROR: ")
expect(failed).to_contain("[REDACTED:")
expect(failed.contains("sk-ant-fixture-secret")).to_be(false)
expect(llm_history_len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(llm_history_role(0)).to_equal("user")
expect(llm_history_content(0)).to_equal("fixture-error-session")

llm_system("Be concise")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
llm_clear()
```

</details>

#### should clear history and provider session immediately

- should clear history and provider session immediately
- Verify: should clear history and provider session immediately
   - Expected: llm_chat("fixture-success") equals `fixture-ok`
   - Expected: llm_history_len() equals `2`
   - Expected: llm_history_len() equals `0`
   - Expected: llm_history_role(-1) equals ``
   - Expected: llm_history_role(0) equals ``
   - Expected: llm_history_role(999) equals ``
   - Expected: llm_history_content(-1) equals ``
   - Expected: llm_history_content(0) equals ``
   - Expected: llm_history_content(999) equals ``
   - Expected: llm_send("fixture-success") equals `fixture-ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should clear history and provider session immediately")
step("Verify: should clear history and provider session immediately")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_chat("fixture-success")).to_equal("fixture-ok")
expect(llm_history_len()).to_equal(2)  # oracle: 2 — named expected value from the requirement

llm_clear()
expect(llm_history_len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(llm_history_role(-1)).to_equal("")
expect(llm_history_role(0)).to_equal("")
expect(llm_history_role(999)).to_equal("")
expect(llm_history_content(-1)).to_equal("")
expect(llm_history_content(0)).to_equal("")
expect(llm_history_content(999)).to_equal("")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
```

</details>

#### should restore every safely observable public default

- should restore every safely observable public default
- Verify: should restore every safely observable public default
   - Expected: llm_chat("fixture-success") equals `fixture-ok`
   - Expected: llm_history_len() equals `2`
   - Expected: llm_provider() equals `claude_cli`
   - Expected: llm_model() equals ``
   - Expected: llm_history_len() equals `0`
   - Expected: llm_send("fixture-no-system") equals `no-system-ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should restore every safely observable public default")
step("Verify: should restore every safely observable public default")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_chat("fixture-success")).to_equal("fixture-ok")
expect(llm_history_len()).to_equal(2)  # oracle: 2 — named expected value from the requirement

llm_init_defaults()
expect(llm_provider()).to_equal("claude_cli")
expect(llm_model()).to_equal("")
expect(llm_history_len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
llm_set_cli_path(MOCK_CLAUDE)
expect(llm_send("fixture-no-system")).to_equal("no-system-ok")
llm_clear()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-LLM-CARET-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `40dde26bcff802deb180ce13cd2df311947cb383c2eb43953e83489d3c3f8219`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40dde26bcff802deb180ce13cd2df311947cb383c2eb43953e83489d3c3f8219`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40dde26bcff802deb180ce13cd2df311947cb383c2eb43953e83489d3c3f8219`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/llm_caret/provider_spec.spl
mirror: doc/06_spec/unit/app/llm_caret/provider_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_caret/provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_caret/provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_caret/provider_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should list all providers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/provider_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should list all providers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/provider_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include dummy' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/provider_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include dummy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/provider_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include claude_cli' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/provider_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include claude_cli' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/provider_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include opencode_cli' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/provider_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include claude_api' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/provider_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include openai' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
