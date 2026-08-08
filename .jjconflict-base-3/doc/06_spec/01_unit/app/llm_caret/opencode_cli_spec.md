# LLM Caret OpenCode CLI Owner

> Deterministic invocation, completion, local-fixture, and lifecycle-guard
> evidence for the shipped OpenCode CLI owner.

| Field | Value |
|---|---|
| Source | `test/01_unit/app/llm_caret/opencode_cli_spec.spl` |
| Executable scenarios | 15 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirements | REQ-001, REQ-002, REQ-003, NFR-001, NFR-002, NFR-003 |

## Scope and Claim Boundary

The scenarios call `build_opencode_args`, `build_opencode_invocation`,
`parse_opencode_response`, and `complete_opencode_process` directly. They
cover exact structured argv, the default executable path, shell-sensitive value
preservation, JSON field fallbacks, explicit plain-text fallback, empty and
malformed output, provider/process errors, raw-output preservation, and session
fallback behavior.

One scenario calls `opencode_cli_send` against the repository-local
credential-free fixture. The fixture validates exact argv and emits static JSON;
it does not invoke OpenCode, a provider, or a network endpoint. Spawn delegation
is checked statically because starting an asynchronous child cannot be observed
and reaped safely through this owner. Running/kill tests use only non-positive
PIDs, so no test signals a process.

No scenario claims OpenCode installation, authentication, provider or network
availability, remote protocol compatibility, positive spawn/running/kill
behavior, latency, RSS, or process supervision.

## Frozen Flow

1. **Prepare OpenCode CLI inputs**
2. **Run the production invocation or completion owner**
3. **Check exact process response and lifecycle effects**

## Scenarios

1. should build the exact default production invocation
2. should preserve shell-sensitive values as exact argv entries
3. should honor explicit format auto approval and nonempty extras
4. should parse content session and escaped JSON string values
5. should apply message then text parser fallbacks
6. should preserve a plain text response as the explicit raw fallback
7. should reject empty output while preserving its raw bytes
8. should reject malformed fieldless and wrong-type JSON
9. should expose a provider error string and session
10. should preserve success fields and use the requested session fallback
11. should prefer the provider session over the requested fallback
12. should preserve failed process diagnostics and raw stdout
13. should execute the credential-free fixture through the production send owner
14. should build then run once and complete while spawn reuses the builder
15. should reject invalid running and kill PIDs before signalling

## Complete Executable SSpec

The folded constant, helpers, and scenario source is synchronized exactly with
the executable spec.

<details>
<summary>Executable SSpec</summary>

```simple
val MOCK_OPENCODE_CLI = "test/fixtures/llm_caret/mock_opencode_cli.shs"

fn count_opencode_source_occurrences(source: text, needle: text) -> i64:
    var count = 0
    var position = 0
    while position + needle.len() <= source.len():
        if source.substring(position, position + needle.len()) == needle:
            count = count + 1
            position = position + needle.len()
        else:
            position = position + 1
    count

fn opencode_source_position_after(source: text, needle: text, start: i64) -> i64:
    if start < 0 or start >= source.len():
        return -1
    val relative: i64 = source.substring(start).find(needle) ?? -1
    if relative < 0:
        return -1
    start + relative

describe "LLM Caret OpenCode CLI owner":
    describe "invocation construction":
        it "should build the exact default production invocation":
            step("Prepare OpenCode CLI inputs")
            val expected = [
                "run", "--format", "json", "--model", "anthropic/claude",
                "--session", "session-1", "fix the test"
            ]
            step("Run the production invocation or completion owner")
            val invocation = build_opencode_invocation(
                "", "fix the test", "anthropic/claude", "session-1", "", []
            )
            step("Check exact process response and lifecycle effects")
            expect(invocation.path).to_equal("opencode")
            expect(invocation.args).to_equal(expected)

        it "should preserve shell-sensitive values as exact argv entries":
            step("Prepare OpenCode CLI inputs")
            val prompt = "line one; $(touch nope) \"quoted\"\nnext"
            val customPath = "tools/OpenCode CLI"
            step("Run the production invocation or completion owner")
            val invocation = build_opencode_invocation(
                customPath, prompt, "model with spaces", "session;2",
                "http://127.0.0.1:4096/path?q=a b",
                ["--dir", "workspace with spaces", "", "--label=a;b"]
            )
            step("Check exact process response and lifecycle effects")
            expect(invocation.path).to_equal(customPath)
            expect(invocation.args).to_equal([
                "run", "--format", "json", "--model", "model with spaces",
                "--session", "session;2", "--attach",
                "http://127.0.0.1:4096/path?q=a b", "--dir",
                "workspace with spaces", "--label=a;b", prompt
            ])
            expect(invocation.args[invocation.args.len() - 1]).to_equal(prompt)

        it "should honor explicit format auto approval and nonempty extras":
            step("Prepare OpenCode CLI inputs")
            val prompt = "continue"
            step("Run the production invocation or completion owner")
            val args = build_opencode_args(
                prompt, "", "", "stream-json", "", true,
                ["", "--dir", ".", ""]
            )
            step("Check exact process response and lifecycle effects")
            expect(args).to_equal([
                "run", "--format", "stream-json", "--auto", "--dir", ".", prompt
            ])

    describe "response parsing":
        it "should parse content session and escaped JSON string values":
            step("Prepare OpenCode CLI inputs")
            val raw = "{\"content\":\"line\\nquote\\\"slash\\\\\",\"sessionID\":\"session-out\"}"
            step("Run the production invocation or completion owner")
            val response = parse_opencode_response(raw, "anthropic/claude")
            step("Check exact process response and lifecycle effects")
            expect(response.content).to_equal("line\nquote\"slash\\")
            expect(response.model).to_equal("anthropic/claude")
            expect(response.session_id).to_equal("session-out")
            expect(response.stop_reason).to_equal("stop")
            expect(response.is_error).to_equal(false)
            expect(response.raw).to_equal(raw)

        it "should apply message then text parser fallbacks":
            step("Prepare OpenCode CLI inputs")
            val messageRaw = "{\"content\":\"\",\"message\":\"message fallback\"}"
            val textRaw = "{\"message\":\"\",\"text\":\"text fallback\"}"
            step("Run the production invocation or completion owner")
            val messageResponse = parse_opencode_response(messageRaw, "m")
            val textResponse = parse_opencode_response(textRaw, "m")
            step("Check exact process response and lifecycle effects")
            expect(messageResponse.content).to_equal("message fallback")
            expect(messageResponse.is_error).to_equal(false)
            expect(textResponse.content).to_equal("text fallback")
            expect(textResponse.is_error).to_equal(false)

        it "should preserve a plain text response as the explicit raw fallback":
            step("Prepare OpenCode CLI inputs")
            val raw = "  plain OpenCode response  "
            step("Run the production invocation or completion owner")
            val response = parse_opencode_response(raw, "m")
            step("Check exact process response and lifecycle effects")
            expect(response.content).to_equal("plain OpenCode response")
            expect(response.error).to_equal("")
            expect(response.is_error).to_equal(false)
            expect(response.raw).to_equal(raw)

        it "should reject empty output while preserving its raw bytes":
            step("Prepare OpenCode CLI inputs")
            val raw = " \n\t"
            step("Run the production invocation or completion owner")
            val response = parse_opencode_response(raw, "m")
            step("Check exact process response and lifecycle effects")
            expect(response.content).to_equal("")
            expect(response.stop_reason).to_equal("error")
            expect(response.error).to_equal("empty response")
            expect(response.is_error).to_equal(true)
            expect(response.raw).to_equal(raw)

        it "should reject malformed fieldless and wrong-type JSON":
            step("Prepare OpenCode CLI inputs")
            val malformedRaw = "{\"content\":\"unterminated}"
            val fieldlessRaw = "{}"
            val wrongTypeRaw = "{\"content\":123}"
            val arrayRaw = "[]"
            val trailingCommaRaw = "{\"content\":\"ok\",}"
            val missingCommaRaw = "{\"content\":\"ok\" \"sessionID\":\"s\"}"
            val invalidEscapeRaw = "{\"content\":\"bad\\q\"}"
            val trailingGarbageRaw = "{\"content\":\"ok\"} garbage}"
            step("Run the production invocation or completion owner")
            val malformed = parse_opencode_response(malformedRaw, "m")
            val fieldless = parse_opencode_response(fieldlessRaw, "m")
            val wrongType = parse_opencode_response(wrongTypeRaw, "m")
            val array = parse_opencode_response(arrayRaw, "m")
            val trailingComma = parse_opencode_response(trailingCommaRaw, "m")
            val missingComma = parse_opencode_response(missingCommaRaw, "m")
            val invalidEscape = parse_opencode_response(invalidEscapeRaw, "m")
            val trailingGarbage = parse_opencode_response(trailingGarbageRaw, "m")
            step("Check exact process response and lifecycle effects")
            expect(malformed.error).to_equal("malformed response")
            expect(malformed.raw).to_equal(malformedRaw)
            expect(fieldless.error).to_equal("malformed response")
            expect(fieldless.raw).to_equal(fieldlessRaw)
            expect(wrongType.error).to_equal("malformed response")
            expect(wrongType.raw).to_equal(wrongTypeRaw)
            expect(array.error).to_equal("malformed response")
            expect(array.raw).to_equal(arrayRaw)
            expect(trailingComma.error).to_equal("malformed response")
            expect(missingComma.error).to_equal("malformed response")
            expect(invalidEscape.error).to_equal("malformed response")
            expect(trailingGarbage.error).to_equal("malformed response")

        it "should expose a provider error string and session":
            step("Prepare OpenCode CLI inputs")
            val raw = "{\"error\":\"permission denied\",\"sessionID\":\"session-error\"}"
            step("Run the production invocation or completion owner")
            val response = parse_opencode_response(raw, "m")
            step("Check exact process response and lifecycle effects")
            expect(response.content).to_equal("")
            expect(response.session_id).to_equal("session-error")
            expect(response.stop_reason).to_equal("error")
            expect(response.error).to_equal("permission denied")
            expect(response.is_error).to_equal(true)
            expect(response.raw).to_equal(raw)

    describe "process completion":
        it "should preserve success fields and use the requested session fallback":
            step("Prepare OpenCode CLI inputs")
            val raw = "{\"message\":\"completed\"}"
            step("Run the production invocation or completion owner")
            val response = complete_opencode_process(
                "anthropic/claude", "session-in", raw, "warning", 0
            )
            step("Check exact process response and lifecycle effects")
            expect(response.content).to_equal("completed")
            expect(response.model).to_equal("anthropic/claude")
            expect(response.session_id).to_equal("session-in")
            expect(response.stop_reason).to_equal("stop")
            expect(response.error).to_equal("")
            expect(response.is_error).to_equal(false)
            expect(response.raw).to_equal(raw)

        it "should prefer the provider session over the requested fallback":
            step("Prepare OpenCode CLI inputs")
            val raw = "{\"content\":\"completed\",\"sessionID\":\"session-out\"}"
            step("Run the production invocation or completion owner")
            val response = complete_opencode_process(
                "anthropic/claude", "session-in", raw, "", 0
            )
            step("Check exact process response and lifecycle effects")
            expect(response.session_id).to_equal("session-out")
            expect(response.is_error).to_equal(false)
            expect(response.raw).to_equal(raw)

        it "should preserve failed process diagnostics and raw stdout":
            step("Prepare OpenCode CLI inputs")
            val stdout = "{\"partial\":\"response\"}"
            step("Run the production invocation or completion owner")
            val response = complete_opencode_process(
                "anthropic/claude", "session-in", stdout,
                " permission denied \n", 7
            )
            step("Check exact process response and lifecycle effects")
            expect(response.content).to_equal("")
            expect(response.model).to_equal("anthropic/claude")
            expect(response.session_id).to_equal("session-in")
            expect(response.stop_reason).to_equal("error")
            expect(response.error).to_equal(
                "opencode CLI exited with code 7: permission denied"
            )
            expect(response.is_error).to_equal(true)
            expect(response.raw).to_equal(stdout)

    describe "production delegation and lifecycle":
        it "should execute the credential-free fixture through the production send owner":
            step("Prepare OpenCode CLI inputs")
            val path = MOCK_OPENCODE_CLI
            step("Run the production invocation or completion owner")
            val response = opencode_cli_send(
                path, "fixture-success", "anthropic/claude", "session-in",
                "http://127.0.0.1:4096", ["--fixture-extra"]
            )
            step("Check exact process response and lifecycle effects")
            expect(response.content).to_equal("fixture-ok")
            expect(response.model).to_equal("anthropic/claude")
            expect(response.session_id).to_equal("session-out")
            expect(response.error).to_equal("")
            expect(response.is_error).to_equal(false)

        it "should build then run once and complete while spawn reuses the builder":
            step("Prepare OpenCode CLI inputs")
            val source = file_read("src/app/llm_caret/opencode_cli.spl")
            step("Run the production invocation or completion owner")
            val sendPosition: i64 = source.find("pub fn opencode_cli_send(") ?? -1
            val sendBuildPosition = opencode_source_position_after(
                source, "val invocation = build_opencode_invocation(", sendPosition
            )
            val runPosition = opencode_source_position_after(
                source, "val result = process_run(", sendBuildPosition
            )
            val completePosition = opencode_source_position_after(
                source, "complete_opencode_process(", runPosition
            )
            val spawnPosition: i64 = source.find("pub fn opencode_cli_spawn(") ?? -1
            val spawnBuildPosition = opencode_source_position_after(
                source, "val invocation = build_opencode_invocation(", spawnPosition
            )
            val spawnCallPosition = opencode_source_position_after(
                source, "val pid = process_spawn_async(", spawnBuildPosition
            )
            step("Check exact process response and lifecycle effects")
            expect(count_opencode_source_occurrences(source, "process_run(")).to_equal(1)
            expect(count_opencode_source_occurrences(source, "process_spawn_async(")).to_equal(1)
            expect(count_opencode_source_occurrences(source, "build_opencode_invocation(")).to_equal(3)
            expect(sendBuildPosition).to_be_greater_than(sendPosition)
            expect(runPosition).to_be_greater_than(sendBuildPosition)
            expect(completePosition).to_be_greater_than(runPosition)
            expect(spawnBuildPosition).to_be_greater_than(spawnPosition)
            expect(spawnCallPosition).to_be_greater_than(spawnBuildPosition)

        it "should reject invalid running and kill PIDs before signalling":
            step("Prepare OpenCode CLI inputs")
            val zeroPid: i64 = 0
            val negativePid: i64 = -9
            step("Run the production invocation or completion owner")
            val zeroKill = opencode_cli_kill(zeroPid)
            val negativeKill = opencode_cli_kill(negativePid)
            val zeroStatus = opencode_cli_running_status(zeroPid)
            val negativeStatus = opencode_cli_running_status(negativePid)
            step("Check exact process response and lifecycle effects")
            expect(zeroKill.status).to_equal("not_stopped")
            expect(zeroKill.reason).to_equal("invalid_pid")
            expect(zeroKill.pid).to_equal(zeroPid)
            expect(negativeKill.status).to_equal("not_stopped")
            expect(negativeKill.reason).to_equal("invalid_pid")
            expect(negativeKill.pid).to_equal(negativePid)
            expect(zeroStatus).to_equal("not_running")
            expect(negativeStatus).to_equal("not_running")
```

</details>
