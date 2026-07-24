# LLM Caret Main Unit Spec

> Source-synchronized unit manual. The current self-hosted SSpec runner is
> blocked before trustworthy scenario execution, so this document records
> 45 active scenarios and 0 executed scenarios.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 45 | 45 | 0 | 0 | 0 |

**Executable source:** `test/01_unit/app/llm_caret/main_spec.spl`

## should default to auto ui mode, claude_cli-less provider, no server

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
val a = parse_main_args([])
expect(a.provider).to_equal("")
expect(a.ui_mode).to_equal("auto")
expect(a.server_mode).to_be(false)
expect(a.help).to_be(false)
expect(a.unknown).to_equal("")
```

</details>

## should parse --provider and --model (space form)

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
val a = parse_main_args(["--provider", "claude_api", "--model", "claude-opus-4-20250514"])
expect(a.provider).to_equal("claude_api")
expect(a.model).to_equal("claude-opus-4-20250514")
```

</details>

## should parse --provider= and --model= (equals form)

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
val a = parse_main_args(["--provider=openai", "--model=gpt-4o"])
expect(a.provider).to_equal("openai")
expect(a.model).to_equal("gpt-4o")
```

</details>

## should parse --plain and --tui

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
expect(parse_main_args(["--plain"]).ui_mode).to_equal("plain")
expect(parse_main_args(["--tui"]).ui_mode).to_equal("tui")
```

</details>

## should parse --gui and one-shot --prompt

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
val a = parse_main_args(["--gui", "--prompt", "hi"])
expect(a.ui_mode).to_equal("gui")
expect(a.prompt).to_equal("hi")
```

</details>

## should parse Electron and pure-Simple Metal GUI modes

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
expect(parse_main_args(["--electron"]).ui_mode).to_equal("electron")
val metal = parse_main_args(["--metal-gui", "--prompt", "test"])
expect(metal.ui_mode).to_equal("metal_gui")
expect(metal.prompt).to_equal("test")
```

</details>

## should parse --server and --port

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
val a = parse_main_args(["--server", "--port", "9000"])
expect(a.server_mode).to_be(true)
expect(a.port).to_equal(9000)
```

</details>

## should parse --port= form

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
expect(parse_main_args(["--port=1234"]).port).to_equal(1234)
```

</details>

## should parse --resume, --config, --system, --workspace

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
val a = parse_main_args(["--resume", "sess-9", "--config", "cfg.sdn", "--system", "be nice", "--workspace", "/tmp/ws"])
expect(a.resume_id).to_equal("sess-9")
expect(a.config_path).to_equal("cfg.sdn")
expect(a.system_prompt).to_equal("be nice")
expect(a.workspace_root).to_equal("/tmp/ws")
```

</details>

## should parse --dangerously-allow-all

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
expect(parse_main_args(["--dangerously-allow-all"]).allow_all).to_be(true)
```

</details>

## should parse -h/--help

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
expect(parse_main_args(["-h"]).help).to_be(true)
expect(parse_main_args(["--help"]).help).to_be(true)
```

</details>

## should record the first unrecognized flag

**Group:** parse_main_args

<details>
<summary>Executable SSpec</summary>

```simple
val a = parse_main_args(["--bogus-flag", "--another"])
expect(a.unknown).to_equal("--bogus-flag")
```

</details>

## should round-trips the session id set by main_configure

**Group:** main_configure / main_session_id

<details>
<summary>Executable SSpec</summary>

```simple
main_configure("claude_cli", "m", "", "", "claude", "", "seeded-session", 0)
expect(main_session_id()).to_equal("seeded-session")
```

</details>

## should clear the provider session for a new conversation

**Group:** main_configure / main_session_id

<details>
<summary>Executable SSpec</summary>

```simple
main_configure("claude_cli", "sonnet", "", "", "claude", "", "provider-session", 0)
val new_id = _slash_on_new()
expect(new_id.starts_with("sess-")).to_be(true)
expect(main_session_id()).to_equal("")
```

</details>

## should refresh provider defaults and clear a foreign provider session

**Group:** main_configure / main_session_id

<details>
<summary>Executable SSpec</summary>

```simple
main_configure("claude_cli", "sonnet", "", "", "claude", "", "provider-session", 0)
val changed = _slash_on_provider("dummy")
expect(changed.accepted).to_be(true)
expect(changed.provider).to_equal("dummy")
expect(changed.model).to_equal("dummy-hello")
expect(main_session_id()).to_equal("")
```

</details>

## should restore the saved provider model and provider session by default

**Group:** resume backend resolution

<details>
<summary>Executable SSpec</summary>

```simple
val backend = resolve_resume_backend("", "", "claude_cli", "sonnet")
expect(backend.provider).to_equal("claude_cli")
expect(backend.model).to_equal("sonnet")
expect(backend.reuse_provider_session).to_be(true)
```

</details>

## should use the overridden provider default instead of the saved model

**Group:** resume backend resolution

<details>
<summary>Executable SSpec</summary>

```simple
val backend = resolve_resume_backend("dummy", "", "claude_cli", "sonnet")
expect(backend.provider).to_equal("dummy")
expect(backend.model).to_equal("dummy-hello")
expect(backend.reuse_provider_session).to_be(false)
```

</details>

## should normalize a legacy empty saved model before session reuse

**Group:** resume backend resolution

<details>
<summary>Executable SSpec</summary>

```simple
val backend = resolve_resume_backend("", "", "dummy", "")
expect(backend.model).to_equal("dummy-hello")
expect(backend.reuse_provider_session).to_be(true)
```

</details>

## should discard the provider session when the model is overridden

**Group:** resume backend resolution

<details>
<summary>Executable SSpec</summary>

```simple
val backend = resolve_resume_backend(
    "", "different-model", "claude_cli", "sonnet"
)
expect(backend.model).to_equal("different-model")
expect(backend.reuse_provider_session).to_be(false)
```

</details>

## should restore provider model messages and provider session atomically

**Group:** production session restoration

<details>
<summary>Executable SSpec</summary>

```simple
main_configure(
    "claude_cli", "sonnet", "", "", "claude", "",
    "old-provider-session", 0
)
val resumed = apply_resumed_session(Session(
    id: "saved-app-session",
    provider: "dummy",
    model: "",
    provider_session_id: "saved-provider-session",
    messages: [new_user_message("restored")],
    updated_at_ms: 0
))
expect(resumed.found).to_be(true)
expect(resumed.provider).to_equal("dummy")
expect(resumed.model).to_equal("dummy-hello")
expect(resumed.session_id).to_equal("saved-app-session")
expect(resumed.messages.len()).to_equal(1)
expect(main_session_id()).to_equal("saved-provider-session")
```

</details>

## should reject an invalid saved provider without mutating the session

**Group:** production session restoration

<details>
<summary>Executable SSpec</summary>

```simple
main_configure(
    "dummy", "dummy-hello", "", "", "", "",
    "keep-provider-session", 0
)
val rejected = apply_resumed_session(Session(
    id: "invalid-app-session",
    provider: "missing-provider",
    model: "bad-model",
    provider_session_id: "foreign-provider-session",
    messages: [],
    updated_at_ms: 0
))
expect(rejected.found).to_be(false)
expect(rejected.message).to_contain("unknown provider")
expect(main_session_id()).to_equal("keep-provider-session")
```

</details>

## should map a plain-text response with no tool_use blocks

**Group:** build_model_response

<details>
<summary>Executable SSpec</summary>

```simple
val mr = build_model_response(_llm_ok("hello there", "{}"))
expect(mr.text).to_equal("hello there")
expect(mr.tool_calls.len()).to_equal(0)
```

</details>

## should map an error response to an ERROR-prefixed text turn

**Group:** build_model_response

<details>
<summary>Executable SSpec</summary>

```simple
val mr = build_model_response(new_llm_error("test", "boom"))
expect(mr.text).to_contain("ERROR: boom")
expect(mr.tool_calls.len()).to_equal(0)
```

</details>

## should extract a tool_use block from the raw wire response

**Group:** build_model_response

<details>
<summary>Executable SSpec</summary>

```simple
val raw = "{\"type\":\"tool_use\",\"id\":\"t1\",\"name\":\"bash\",\"input\":{\"command\":\"echo hi\"}}"
val mr = build_model_response(_llm_ok("", raw))
expect(mr.tool_calls.len()).to_equal(1)
expect(mr.tool_calls[0].name).to_equal("bash")
expect(mr.tool_calls[0].id).to_equal("t1")
```

</details>

## should run a scripted 2-turn tool-call conversation to completion

**Group:** scripted plain-mode conversation (end-to-end via chat.run_agent_loop)

<details>
<summary>Executable SSpec</summary>

```simple
SCRIPT_TURN = 0
val p = default_policy(WS_ROOT)
val result = run_agent_loop(p, [new_user_message("do the thing")], _scripted_responder, 10)
expect(result.tool_calls_made).to_equal(1)
expect(result.final_text).to_equal("final answer")
expect(result.stopped_reason).to_equal("end_turn")
# the tool_result turn must be threaded into final_transcript (the
# M2 gap this campaign closed) - not just the initial + final text.
expect(result.final_transcript.len() > 2).to_be(true)
```

</details>

## should inspect a real tool envelope without echoing its input

**Group:** Hidden command inspection

<details>
<summary>Executable SSpec</summary>

```simple
val result = _slash_on_hidden_command(
    "debug-tool-call",
    "{\"type\":\"tool_use\",\"id\":\"call-1\",\"name\":\"bash\",\"input\":{\"command\":\"echo sk-ant-fixture-secret\"}}"
)
expect(result).to_contain("id=call-1")
expect(result).to_contain("name=bash")
expect(result).to_contain("input_bytes=")
expect(result.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

## should reject missing, malformed, and unsupported hidden input

**Group:** Hidden command inspection

<details>
<summary>Executable SSpec</summary>

```simple
expect(_slash_on_hidden_command("debug-tool-call", "")).to_contain(
    "Usage:"
)
expect(_slash_on_hidden_command(
    "debug-tool-call", "{\"type\":\"text\",\"text\":\"not a call\"}"
)).to_equal("No tool call envelope found.")
expect(_slash_on_hidden_command("other-hidden", "{}")).to_contain(
    "not implemented"
)
```

</details>

## should reject tool envelopes with incomplete public metadata

**Group:** Hidden command inspection

<details>
<summary>Executable SSpec</summary>

```simple
expect(_slash_on_hidden_command(
    "debug-tool-call",
    "{\"type\":\"tool_use\",\"name\":\"bash\",\"input\":{}}"
)).to_equal("Invalid tool call envelope.")
expect(_slash_on_hidden_command(
    "debug-tool-call",
    "{\"type\":\"tool_use\",\"id\":\"call-1\",\"input\":{}}"
)).to_equal("Invalid tool call envelope.")
```

</details>

## should summarize only the first tool envelope without leaking payloads

**Group:** Hidden command inspection

<details>
<summary>Executable SSpec</summary>

```simple
val result = _slash_on_hidden_command(
    "debug-tool-call",
    "{\"content\":[" +
    "{\"type\":\"tool_use\",\"id\":\"call-1\",\"name\":\"bash\"," +
    "\"input\":{\"command\":\"first-fixture-secret\"}}," +
    "{\"type\":\"tool_use\",\"id\":\"call-2\",\"name\":\"write_file\"," +
    "\"input\":{\"content\":\"second-fixture-secret\"}}]}"
)
expect(result).to_contain("id=call-1")
expect(result).to_contain("name=bash")
expect(result.contains("call-2")).to_be(false)
expect(result.contains("first-fixture-secret")).to_be(false)
expect(result.contains("second-fixture-secret")).to_be(false)
```

</details>

## should health and models routes return 200

**Group:** HTTP proxy pure core (proxy_handle)

<details>
<summary>Executable SSpec</summary>

```simple
expect(status_for_path("/v1/health")).to_equal(200)
expect(status_for_path("/v1/models")).to_equal(200)
```

</details>

## should report unknown routes return 404

**Group:** HTTP proxy pure core (proxy_handle)

<details>
<summary>Executable SSpec</summary>

```simple
expect(status_for_path("/nope")).to_equal(404)
```

</details>

## should GET /v1/health is routed through proxy_handle end to end

**Group:** HTTP proxy pure core (proxy_handle)

<details>
<summary>Executable SSpec</summary>

```simple
val (code, body) = proxy_handle("GET", "/v1/health", "", _fake_dispatch_ok)
expect(code).to_equal(200)
expect(body).to_contain("ok")
```

</details>

## should GET on an unknown path is a 404 through proxy_handle

**Group:** HTTP proxy pure core (proxy_handle)

<details>
<summary>Executable SSpec</summary>

```simple
val (code, body) = proxy_handle("GET", "/nope", "", _fake_dispatch_ok)
expect(code).to_equal(404)
```

</details>

## should chat completions with empty content is a 400

**Group:** HTTP proxy pure core (proxy_handle)

<details>
<summary>Executable SSpec</summary>

```simple
val (code, body) = proxy_handle("POST", "/v1/chat/completions", "", _fake_dispatch_ok)
expect(code).to_equal(400)
expect(body).to_contain("messages required")
```

</details>

## should chat completions dispatches and returns 200 on success

**Group:** HTTP proxy pure core (proxy_handle)

<details>
<summary>Executable SSpec</summary>

```simple
val body_in = "{\"content\":\"hi\"}"
val (code, body) = proxy_handle("POST", "/v1/chat/completions", body_in, _fake_dispatch_ok)
expect(code).to_equal(200)
expect(body).to_contain("echo: hi")
```

</details>

## should chat completions returns 502 when the backend errors

**Group:** HTTP proxy pure core (proxy_handle)

<details>
<summary>Executable SSpec</summary>

```simple
val body_in = "{\"content\":\"hi\"}"
val (code, body) = proxy_handle("POST", "/v1/chat/completions", body_in, _fake_dispatch_err)
expect(code).to_equal(502)
expect(body).to_contain("upstream down")
```

</details>

## should /v1/messages dispatches through the anthropic-shaped response

**Group:** HTTP proxy pure core (proxy_handle)

<details>
<summary>Executable SSpec</summary>

```simple
val body_in = "{\"content\":\"hi\"}"
val (code, body) = proxy_handle("POST", "/v1/messages", body_in, _fake_dispatch_ok)
expect(code).to_equal(200)
expect(body).to_contain("\"message\"")
```

</details>

## should bearer_ok always allows when no token is required

**Group:** Server hardening (guard_request)

<details>
<summary>Executable SSpec</summary>

```simple
expect(bearer_ok("", "")).to_be(true)
expect(bearer_ok("garbage", "")).to_be(true)
```

</details>

## should bearer_ok rejects a missing/garbage header when a token is required

**Group:** Server hardening (guard_request)

<details>
<summary>Executable SSpec</summary>

```simple
expect(bearer_ok("", "secret")).to_be(false)
expect(bearer_ok("Bearer wrong", "secret")).to_be(false)
```

</details>

## should bearer_ok accepts the exact configured token

**Group:** Server hardening (guard_request)

<details>
<summary>Executable SSpec</summary>

```simple
expect(bearer_ok("Bearer secret", "secret")).to_be(true)
```

</details>

## should guard_request returns 401 without a token when one is required

**Group:** Server hardening (guard_request)

<details>
<summary>Executable SSpec</summary>

```simple
rate_limit_reset()
val (allowed, code, body) = guard_request("", "{}", "secret", "client-a", 1000)
expect(allowed).to_be(false)
expect(code).to_equal(401)
```

</details>

## should guard_request allows a matching bearer token

**Group:** Server hardening (guard_request)

<details>
<summary>Executable SSpec</summary>

```simple
rate_limit_reset()
val (allowed, code, body) = guard_request("Bearer secret", "{}", "secret", "client-b", 1000)
expect(allowed).to_be(true)
```

</details>

## should guard_request rejects an oversized body with 413

**Group:** Server hardening (guard_request)

<details>
<summary>Executable SSpec</summary>

```simple
rate_limit_reset()
# Double up to exceed MAX_BODY_BYTES (1_000_000) in O(log n) instead
# of an O(n) append loop - a naive 100k-iteration `+=` loop over a
# megabyte string is needlessly slow under the interpreter.
var big = "0123456789"
while big.len() < 1000001:
    big = big + big
val (allowed, code, body) = guard_request("", big, "", "client-c", 1000)
expect(allowed).to_be(false)
expect(code).to_equal(413)
```

</details>

## should rate_limit_check allows the first N requests then rejects the N+1th

**Group:** Server hardening (guard_request)

<details>
<summary>Executable SSpec</summary>

```simple
rate_limit_reset()
var i = 0
var last_ok = true
while i < 60:
    last_ok = rate_limit_check("client-rl", 1000)
    i = i + 1
expect(last_ok).to_be(true)
val over_limit = rate_limit_check("client-rl", 1000)
expect(over_limit).to_be(false)
```

</details>

## should rate_limit_check resets after the window elapses

**Group:** Server hardening (guard_request)

<details>
<summary>Executable SSpec</summary>

```simple
rate_limit_reset()
var i = 0
while i < 60:
    rate_limit_check("client-window", 1000)
    i = i + 1
expect(rate_limit_check("client-window", 1000)).to_be(false)
# 60s+ later, same client should be allowed again
expect(rate_limit_check("client-window", 1000 + 60001)).to_be(true)
rate_limit_reset()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |
