# LLM Caret Provider Unit Spec

> Source-synchronized unit manual. The current self-hosted SSpec runner is
> blocked before trustworthy scenario execution, so this document records
> 36 active scenarios and 0 executed scenarios.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 36 | 36 | 0 | 0 | 0 |

**Executable source:** `test/01_unit/app/llm_caret/provider_spec.spl`

## Scope and Claim Boundary

These scenarios exercise provider registry/validation, pure error mapping,
public state, and the repository-local credential-free mock Claude process.
Credential-missing and model-missing cases fail before any network or model
call. No scenario invokes a paid provider, authenticates to a remote service,
loads a local model, or proves a live Claude/OpenCode installation. Successful
Claude/OpenAI/compatible/local response normalization still needs an injected
pure owner seam. With 0 executed scenarios, this manual makes no PASS claim.

## should list all providers

**Group:** Provider List

<details>
<summary>Executable SSpec</summary>

```simple
val providers = list_providers()
expect(providers.len()).to_equal(7)
```

</details>

## should include dummy

**Group:** Provider List

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("dummy")).to_be(true)
```

</details>

## should include claude_cli

**Group:** Provider List

<details>
<summary>Executable SSpec</summary>

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "claude_cli":
        found = true
expect(found).to_be(true)
```

</details>

## should include opencode_cli

**Group:** Provider List

<details>
<summary>Executable SSpec</summary>

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "opencode_cli":
        found = true
expect(found).to_be(true)
```

</details>

## should include claude_api

**Group:** Provider List

<details>
<summary>Executable SSpec</summary>

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "claude_api":
        found = true
expect(found).to_be(true)
```

</details>

## should include openai

**Group:** Provider List

<details>
<summary>Executable SSpec</summary>

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "openai":
        found = true
expect(found).to_be(true)
```

</details>

## should include openai_compat

**Group:** Provider List

<details>
<summary>Executable SSpec</summary>

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "openai_compat":
        found = true
expect(found).to_be(true)
```

</details>

## should include local_torch

**Group:** Provider List

<details>
<summary>Executable SSpec</summary>

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "local_torch":
        found = true
expect(found).to_be(true)
```

</details>

## should validate claude_cli

**Group:** Provider Validation

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("claude_cli")).to_be(true)
```

</details>

## should validate opencode_cli

**Group:** Provider Validation

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("opencode_cli")).to_be(true)
```

</details>

## should validate claude_api

**Group:** Provider Validation

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("claude_api")).to_be(true)
```

</details>

## should validate openai

**Group:** Provider Validation

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("openai")).to_be(true)
```

</details>

## should validate openai_compat

**Group:** Provider Validation

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("openai_compat")).to_be(true)
```

</details>

## should validate local_torch

**Group:** Provider Validation

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("local_torch")).to_be(true)
```

</details>

## should reject an unknown provider

**Group:** Provider Validation

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("unknown")).to_be(false)
```

</details>

## should reject an empty provider

**Group:** Provider Validation

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_valid_provider("")).to_be(false)
```

</details>

## should create an error response

**Group:** LLMResponse Error

<details>
<summary>Executable SSpec</summary>

```simple
val resp = new_llm_error("claude_cli", "connection refused")
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("connection refused")
expect(resp.provider).to_equal("claude_cli")
expect(resp.stop_reason).to_equal("error")
expect(resp.content).to_equal("")
```

</details>

## should always return hello without external configuration

**Group:** Dummy Provider

<details>
<summary>Executable SSpec</summary>

```simple
val resp = dispatch_send("dummy", "anything", "", "", "", "", "", "", 0, 0, "[]")
expect(resp.is_error).to_be(false)
expect(resp.content).to_equal("hello")
expect(resp.model).to_equal("dummy-hello")
```

</details>

## should reject Claude-only advanced arguments for another provider

**Group:** Dummy Provider

<details>
<summary>Executable SSpec</summary>

```simple
val resp = dispatch_send_advanced(
    "dummy", "anything", "", "", "", "", "", "", 0, 0, "[]",
    "{\"type\":\"object\"}", ["Read"], []
)
expect(resp.is_error).to_be(true)
expect(resp.provider).to_equal("dummy")
expect(resp.error).to_contain("require claude_cli")
```

</details>

## should reject unknown and misconfigured local providers

**Group:** Provider Dispatch Failures

<details>
<summary>Executable SSpec</summary>

```simple
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

## should reject remote providers without credentials before network access

**Group:** Provider Dispatch Failures

<details>
<summary>Executable SSpec</summary>

```simple
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

## should preserve Claude CLI fields through advanced dispatch

**Group:** Provider Dispatch Failures

<details>
<summary>Executable SSpec</summary>

```simple
val resp = dispatch_send_advanced(
    "claude_cli", "fixture-advanced", "sonnet", "", "",
    MOCK_CLAUDE, "", "", 0, 0, "[]",
    "{\"type\":\"object\"}", ["Read"], ["--fixture-extra"]
)
expect(resp.is_error).to_be(false)
expect(resp.provider).to_equal("claude_cli")
expect(resp.content).to_equal("advanced-ok")
expect(resp.model).to_equal("sonnet")
expect(resp.session_id).to_equal("advanced-session")
```

</details>

## should reject chat and direct send before initialization

**Group:** Uninitialized Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
expect(llm_history_len()).to_equal(0)
expect(llm_chat("not initialized")).to_contain(
    "call llm_init_defaults() or llm_init() first"
)
expect(llm_send("not initialized")).to_contain(
    "call llm_init_defaults() or llm_init() first"
)
expect(llm_history_len()).to_equal(0)
```

</details>

## should normalize a missing Claude API key through direct and public dispatch

**Group:** Production Provider Owners

1. Prepare provider dispatch inputs
2. Dispatch through the production owner
3. Check exact normalized response and ownership

<details>
<summary>Executable SSpec</summary>

```simple
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
expect(direct.input_tokens).to_equal(0)
expect(direct.output_tokens).to_equal(0)
expect(direct.error).to_equal("ANTHROPIC_API_KEY not set")
expect(direct.is_error).to_be(true)
expect(direct.raw).to_equal("")
expect(public).to_equal("ERROR: ANTHROPIC_API_KEY not set")
```

</details>

## should reset stale credentials and normalize a missing OpenAI API key

**Group:** Production Provider Owners

1. Prepare provider dispatch inputs
2. Dispatch through the production owner
3. Check exact normalized response and ownership

<details>
<summary>Executable SSpec</summary>

```simple
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
expect(direct.input_tokens).to_equal(0)
expect(direct.output_tokens).to_equal(0)
expect(direct.error).to_equal("OPENAI_API_KEY not set")
expect(direct.is_error).to_be(true)
expect(direct.raw).to_equal("")
expect(public).to_equal("ERROR: OPENAI_API_KEY not set")
```

</details>

## should normalize a missing local Torch model through direct and public dispatch

**Group:** Production Provider Owners

1. Prepare provider dispatch inputs
2. Dispatch through the production owner
3. Check exact normalized response and ownership

<details>
<summary>Executable SSpec</summary>

```simple
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
expect(direct.input_tokens).to_equal(0)
expect(direct.output_tokens).to_equal(0)
expect(direct.error).to_equal("model_path not configured")
expect(direct.is_error).to_be(true)
expect(direct.raw).to_equal("")
expect(public).to_equal("ERROR: model_path not configured")
llm_clear()
```

</details>

## should preserve dummy success and exact unknown-provider failures

**Group:** Production Provider Owners

1. Prepare provider dispatch inputs
2. Dispatch through the production owner
3. Check exact normalized response and ownership

<details>
<summary>Executable SSpec</summary>

```simple
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
expect(dummy.input_tokens).to_equal(0)
expect(dummy.output_tokens).to_equal(1)
expect(dummy.error).to_equal("")
expect(dummy.is_error).to_be(false)
expect(dummy.raw).to_equal("")
expect(public).to_equal("hello")
expect(unknown.provider).to_equal("unknown")
expect(unknown.session_id).to_equal("")
expect(unknown.stop_reason).to_equal("error")
expect(unknown.input_tokens).to_equal(0)
expect(unknown.output_tokens).to_equal(0)
expect(unknown.error).to_equal("unknown provider: unknown")
expect(unknown.is_error).to_be(true)
expect(unknown.raw).to_equal("")
llm_clear()
```

</details>

## should keep transport and parsing in each production provider owner

**Group:** Production Provider Owners

1. Prepare provider dispatch inputs
2. Dispatch through the production owner
3. Check exact normalized response and ownership

<details>
<summary>Executable SSpec</summary>

```simple
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

## should serialize public history with escaped message content

**Group:** Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
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

## should reject unsupported providers through both public send routes

**Group:** Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
llm_init("unsupported", "none")
val chat_response = llm_chat("hello")
expect(chat_response).to_equal(
    "ERROR: unknown provider: unsupported"
)
expect(llm_history_len()).to_equal(1)
expect(llm_history_role(0)).to_equal("user")
expect(llm_history_content(0)).to_equal("hello")

llm_init("unsupported", "none")
val send_response = llm_send("hello")
expect(send_response).to_equal(
    "ERROR: unknown provider: unsupported"
)
expect(llm_history_len()).to_equal(0)
```

</details>

## should keep API-only settings from altering Claude CLI requests

**Group:** Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
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

## should reset public conversation state on initialization

**Group:** Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_chat("fixture-success")).to_equal("fixture-ok")
expect(llm_history_len()).to_equal(2)

llm_system("stale system prompt")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
expect(llm_history_len()).to_equal(0)
expect(llm_send("fixture-no-system")).to_equal("no-system-ok")

llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
```

</details>

## should reuse a successful Claude session on the next public send

**Group:** Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
expect(llm_send("fixture-requires-resume")).to_equal("resumed-ok")
llm_clear()
```

</details>

## should keep a failed Claude response from poisoning public session state

**Group:** Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
val failed = llm_chat("fixture-error-session")
expect(failed).to_start_with("ERROR: ")
expect(failed).to_contain("[REDACTED:")
expect(failed.contains("sk-ant-fixture-secret")).to_be(false)
expect(llm_history_len()).to_equal(1)
expect(llm_history_role(0)).to_equal("user")
expect(llm_history_content(0)).to_equal("fixture-error-session")

llm_system("Be concise")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
llm_clear()
```

</details>

## should clear history and provider session immediately

**Group:** Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_chat("fixture-success")).to_equal("fixture-ok")
expect(llm_history_len()).to_equal(2)

llm_clear()
expect(llm_history_len()).to_equal(0)
expect(llm_history_role(-1)).to_equal("")
expect(llm_history_role(0)).to_equal("")
expect(llm_history_role(999)).to_equal("")
expect(llm_history_content(-1)).to_equal("")
expect(llm_history_content(0)).to_equal("")
expect(llm_history_content(999)).to_equal("")
expect(llm_send("fixture-success")).to_equal("fixture-ok")
```

</details>

## should restore every safely observable public default

**Group:** Public LLM State

<details>
<summary>Executable SSpec</summary>

```simple
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
expect(llm_chat("fixture-success")).to_equal("fixture-ok")
expect(llm_history_len()).to_equal(2)

llm_init_defaults()
expect(llm_provider()).to_equal("claude_cli")
expect(llm_model()).to_equal("")
expect(llm_history_len()).to_equal(0)
llm_set_cli_path(MOCK_CLAUDE)
expect(llm_send("fixture-no-system")).to_equal("no-system-ok")
llm_clear()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |
