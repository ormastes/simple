# LLM Caret OpenAI-Compatible Exchange

> Deterministic request and injected completion evidence for the shipped
> OpenAI-compatible provider boundary.

| Field | Value |
|---|---|
| Source | `test/01_unit/app/llm_caret/openai_compat_spec.spl` |
| Executable scenarios | 11 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | N/A; focused shipped-provider unit evidence |

## Scope and Claim Boundary

The scenarios call `build_compat_request` and `complete_compat_exchange`
directly. They cover exact default, override, and escaped bodies; optional
authorization; base-URL slash normalization; success, API-error, empty,
malformed, default-field, and injected HTTP-error completion behavior.

The fixture models exactly one injected transport return. It does not make a
network request and does not prove provider authentication, availability,
latency, or remote protocol compatibility. `compat_send` remains the production
owner that performs one `http_request_raw` call between the same build and
completion functions.

## Frozen Flow

1. **Build one OpenAI-compatible request**
2. **Complete the injected transport exchange**
3. **Check exact request response and error state**

The canonical fixture, runner, and checker are `setup_compat_cli_fixture`,
`run_compat_exchange`, and `check_compat_exchange`.

## Scenarios

1. should build and complete one deterministic compatible exchange
2. should omit optional body fields at their defaults
3. should include exact max-token and temperature overrides
4. should escape model quotes slashes and control characters
5. should include authorization only when an API key is present
6. should normalize absent single and repeated base URL slashes
7. should preserve exact successful response fields
8. should expose API error messages and preserve their raw body
9. should reject empty non-JSON and fieldless responses
10. should default finish reason and token counts for valid empty content
11. should preserve injected HTTP-error raw bodies

## Complete Executable SSpec

The folded helper and scenario source is synchronized exactly with the
executable spec.

<details>
<summary>Executable SSpec</summary>

```simple
class CompatCliFixture:
    baseUrl: text
    apiKey: text
    model: text
    messagesJson: text
    maxTokens: i64
    temperature: f64
    responseBody: text
    httpError: text

impl CompatCliFixture:
    static fn new() -> CompatCliFixture:
        CompatCliFixture(
            baseUrl: "http://127.0.0.1:11434",
            apiKey: "",
            model: "local-model",
            messagesJson: "[{\"role\":\"user\",\"content\":\"Hello\"}]",
            maxTokens: 0,
            temperature: -1.0,
            responseBody: "{\"content\":\"Hello back\",\"model\":\"local-model\",\"finish_reason\":\"stop\",\"prompt_tokens\":3,\"completion_tokens\":2}",
            httpError: ""
        )

struct CompatExchangeEvidence:
    request: CompatRequest
    response: CompatResponse

fn setup_compat_cli_fixture() -> CompatCliFixture:
    CompatCliFixture.new()

fn run_compat_exchange(fixture: CompatCliFixture) -> CompatExchangeEvidence:
    val request = build_compat_request(
        fixture.baseUrl,
        fixture.apiKey,
        fixture.model,
        fixture.messagesJson,
        fixture.maxTokens,
        fixture.temperature
    )
    val response = complete_compat_exchange(fixture.responseBody, fixture.httpError)
    CompatExchangeEvidence(request: request, response: response)

fn check_compat_exchange(evidence: CompatExchangeEvidence):
    expect(evidence.request.method).to_equal("POST")
    expect(evidence.request.url).to_equal("http://127.0.0.1:11434/v1/chat/completions")
    expect(evidence.request.headers).to_equal("Content-Type: application/json")
    expect(evidence.request.body).to_equal("{\"model\":\"local-model\",\"messages\":[{\"role\":\"user\",\"content\":\"Hello\"}]}")
    expect(evidence.response.content).to_equal("Hello back")
    expect(evidence.response.model).to_equal("local-model")
    expect(evidence.response.finish_reason).to_equal("stop")
    expect(evidence.response.prompt_tokens).to_equal(3)
    expect(evidence.response.completion_tokens).to_equal(2)
    expect(evidence.response.error).to_equal("")
    expect(evidence.response.is_error).to_equal(false)
    expect(evidence.response.raw).to_equal("{\"content\":\"Hello back\",\"model\":\"local-model\",\"finish_reason\":\"stop\",\"prompt_tokens\":3,\"completion_tokens\":2}")

describe "LLM Caret OpenAI-compatible exchange":
    describe "supporting injected CLI exchange":
        it "should build and complete one deterministic compatible exchange":
            step("Build one OpenAI-compatible request")
            val fixture = setup_compat_cli_fixture()
            step("Complete the injected transport exchange")
            val evidence = run_compat_exchange(fixture)
            step("Check exact request response and error state")
            check_compat_exchange(evidence)

    describe "supporting request body construction":
        it "should omit optional body fields at their defaults":
            step("Build one OpenAI-compatible request")
            val request = build_compat_request("http://localhost:8080", "", "m", "[]", 0, -1.0)
            step("Check exact request response and error state")
            expect(request.body).to_equal("{\"model\":\"m\",\"messages\":[]}")

        it "should include exact max-token and temperature overrides":
            step("Build one OpenAI-compatible request")
            val request = build_compat_request("http://localhost:8080", "", "m", "[]", 2048, 0.7)
            step("Check exact request response and error state")
            expect(request.body).to_equal("{\"model\":\"m\",\"messages\":[],\"max_tokens\":2048,\"temperature\":0.7}")

        it "should escape model quotes slashes and control characters":
            step("Build one OpenAI-compatible request")
            val request = build_compat_request("http://localhost:8080", "", "a\"b\\c\n\r\t", "[]", 0, -1.0)
            step("Check exact request response and error state")
            expect(request.body).to_equal("{\"model\":\"a\\\"b\\\\c\\n\\r\\t\",\"messages\":[]}")

    describe "supporting header and URL construction":
        it "should include authorization only when an API key is present":
            step("Build one OpenAI-compatible request")
            val anonymous = build_compat_request("http://localhost:8080", "", "m", "[]", 0, -1.0)
            val authorized = build_compat_request("http://localhost:8080", "secret", "m", "[]", 0, -1.0)
            step("Check exact request response and error state")
            expect(anonymous.headers).to_equal("Content-Type: application/json")
            expect(authorized.headers).to_equal("Authorization: Bearer secret\nContent-Type: application/json")

        it "should normalize absent single and repeated base URL slashes":
            step("Build one OpenAI-compatible request")
            val absent = build_compat_request("http://localhost:8080", "", "m", "[]", 0, -1.0)
            val single = build_compat_request("http://localhost:8080/", "", "m", "[]", 0, -1.0)
            val repeated = build_compat_request("http://localhost:8080///", "", "m", "[]", 0, -1.0)
            step("Check exact request response and error state")
            expect(absent.url).to_equal("http://localhost:8080/v1/chat/completions")
            expect(single.url).to_equal(absent.url)
            expect(repeated.url).to_equal(absent.url)

    describe "supporting completion parsing":
        it "should preserve exact successful response fields":
            step("Complete the injected transport exchange")
            val raw = "{\"content\":\"done\",\"model\":\"served-model\",\"finish_reason\":\"length\",\"prompt_tokens\":11,\"completion_tokens\":7}"
            val response = complete_compat_exchange(raw, "")
            step("Check exact request response and error state")
            expect(response.content).to_equal("done")
            expect(response.model).to_equal("served-model")
            expect(response.finish_reason).to_equal("length")
            expect(response.prompt_tokens).to_equal(11)
            expect(response.completion_tokens).to_equal(7)
            expect(response.is_error).to_equal(false)
            expect(response.raw).to_equal(raw)

        it "should expose API error messages and preserve their raw body":
            step("Complete the injected transport exchange")
            val raw = "{\"error\":{\"message\":\"model unavailable\",\"type\":\"server_error\"}}"
            val response = complete_compat_exchange(raw, "")
            step("Check exact request response and error state")
            expect(response.content).to_equal("")
            expect(response.finish_reason).to_equal("error")
            expect(response.error).to_equal("model unavailable")
            expect(response.is_error).to_equal(true)
            expect(response.raw).to_equal(raw)

        it "should reject empty non-JSON and fieldless responses":
            step("Complete the injected transport exchange")
            val empty = complete_compat_exchange("", "")
            val nonJson = complete_compat_exchange("not-json", "")
            val fieldless = complete_compat_exchange("{}", "")
            val wrongType = complete_compat_exchange("{\"content\":123}", "")
            step("Check exact request response and error state")
            expect(empty.error).to_equal("empty response")
            expect(empty.is_error).to_equal(true)
            expect(empty.raw).to_equal("")
            expect(nonJson.error).to_equal("malformed response")
            expect(nonJson.raw).to_equal("not-json")
            expect(fieldless.error).to_equal("malformed response")
            expect(fieldless.raw).to_equal("{}")
            expect(wrongType.error).to_equal("malformed response")
            expect(wrongType.raw).to_equal("{\"content\":123}")

        it "should default finish reason and token counts for valid empty content":
            step("Complete the injected transport exchange")
            val raw = "{\"content\":\"\"}"
            val response = complete_compat_exchange(raw, "")
            step("Check exact request response and error state")
            expect(response.content).to_equal("")
            expect(response.model).to_equal("")
            expect(response.finish_reason).to_equal("stop")
            expect(response.prompt_tokens).to_equal(0)
            expect(response.completion_tokens).to_equal(0)
            expect(response.error).to_equal("")
            expect(response.is_error).to_equal(false)
            expect(response.raw).to_equal(raw)

        it "should preserve injected HTTP-error raw bodies":
            step("Complete the injected transport exchange")
            val raw = "{\"proxy\":\"offline\"}"
            val response = complete_compat_exchange(raw, "connection refused")
            step("Check exact request response and error state")
            expect(response.content).to_equal("")
            expect(response.finish_reason).to_equal("error")
            expect(response.prompt_tokens).to_equal(0)
            expect(response.completion_tokens).to_equal(0)
            expect(response.error).to_equal("HTTP error: connection refused")
            expect(response.is_error).to_equal(true)
            expect(response.raw).to_equal(raw)
```

</details>
