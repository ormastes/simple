# primitive_api_spec

> Primitive HTTP routing and scoped authentication remain server-runtime independent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# primitive_api_spec

Primitive HTTP routing and scoped authentication remain server-runtime independent.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/primitive_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Primitive HTTP routing and scoped authentication remain server-runtime independent.

## Scenarios

### primitive LLM Caret API boundary

<details>
<summary>Advanced: routes room resources, streaming, task actions, profiles, and webhooks</summary>

#### routes room resources, streaming, task actions, profiles, and webhooks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes room resources, streaming, task actions, profiles, and webhooks
- Resolve room operations without depending on a socket implementation
   - Expected: send.matched is true
   - Expected: send.operation equals `message_send`
   - Expected: send.required_scope equals `room:write`
   - Expected: send.resource_id equals `r1`
- Classify SSE separately from ordinary JSON requests
   - Expected: events.operation equals `room_events`
   - Expected: events.streaming is true
- Resolve nested member, task-action, profile, and webhook routes
   - Expected: parse_api_route("DELETE", "/v1/rooms/r1/members/i2").child_id equals `i2`
   - Expected: parse_api_route("POST", "/v1/tasks/T-1:approve").operation equals `task_approve`
   - Expected: parse_api_route("GET", "/v1/profiles/i2").operation equals `profile_get`
   - Expected: parse_api_route("POST", "/v1/webhooks/slack").operation equals `webhook_receive`
   - Expected: parse_api_route("POST", "/v1/agent-bindings").operation equals `agent_binding_create`
   - Expected: parse_api_route("PATCH", "/v1/unknown").matched is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes room resources, streaming, task actions, profiles, and webhooks")
step("Resolve room operations without depending on a socket implementation")
val send = parse_api_route("POST", "/v1/rooms/r1/messages")
expect(send.matched).to_equal(true)
expect(send.operation).to_equal("message_send")
expect(send.required_scope).to_equal("room:write")
expect(send.resource_id).to_equal("r1")

step("Classify SSE separately from ordinary JSON requests")
val events = parse_api_route("GET", "/v1/rooms/r1/events?after_seq=3")
expect(events.operation).to_equal("room_events")
expect(events.streaming).to_equal(true)

step("Resolve nested member, task-action, profile, and webhook routes")
expect(parse_api_route("DELETE", "/v1/rooms/r1/members/i2").child_id).to_equal("i2")
expect(parse_api_route("POST", "/v1/tasks/T-1:approve").operation).to_equal("task_approve")
expect(parse_api_route("GET", "/v1/profiles/i2").operation).to_equal("profile_get")
expect(parse_api_route("POST", "/v1/webhooks/slack").operation).to_equal("webhook_receive")
expect(parse_api_route("POST", "/v1/agent-bindings").operation).to_equal("agent_binding_create")
expect(parse_api_route("PATCH", "/v1/unknown").matched).to_equal(false)
```

</details>


</details>

#### requires bounded idempotency keys for writes and builds escaped responses

- requires bounded idempotency keys for writes and builds escaped responses
- Require a stable request key for state-changing retry safety
   - Expected: idempotency_key_valid("POST", "request-123") is true
   - Expected: idempotency_key_valid("POST", "short") is false
   - Expected: idempotency_key_valid("GET", "") is true
- Escape error detail and identify accepted resources
   - Expected: failed.status equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires bounded idempotency keys for writes and builds escaped responses")
step("Require a stable request key for state-changing retry safety")
expect(idempotency_key_valid("POST", "request-123")).to_equal(true)
expect(idempotency_key_valid("POST", "short")).to_equal(false)
expect(idempotency_key_valid("GET", "")).to_equal(true)

step("Escape error detail and identify accepted resources")
val failed = error_response(400, "invalid_request", "bad \"name\"")
expect(failed.status).to_equal(400)
expect(failed.body).to_contain("bad \\\"name\\\"")
expect(accepted_response("message", "m1").body).to_contain("\"message_id\":\"m1\"")
```

</details>

#### parses bearer tokens and enforces expiry, workspace, and scope

- parses bearer tokens and enforces expiry, workspace, and scope
- Accept only the Bearer authorization scheme
   - Expected: bearer_token("Bearer local-token") equals `local-token`
   - Expected: bearer_token("Basic local-token") equals ``
- Authorize a current narrow token in its own workspace
   - Expected: authorize(principal, "room:read", "w1", 50).allowed is true
   - Expected: authorize(principal, "room:write", "w1", 50).status equals `403`
   - Expected: authorize(principal, "room:read", "w2", 50).error equals `workspace_access_denied`
   - Expected: authorize(principal, "room:read", "w1", 100).error equals `token_expired`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses bearer tokens and enforces expiry, workspace, and scope")
step("Accept only the Bearer authorization scheme")
expect(bearer_token("Bearer local-token")).to_equal("local-token")
expect(bearer_token("Basic local-token")).to_equal("")

step("Authorize a current narrow token in its own workspace")
val principal = AuthPrincipal(authenticated: true, identity_id: "i1", workspace_id: "w1",
    scopes: ["room:read"], expires_at: 100)
expect(authorize(principal, "room:read", "w1", 50).allowed).to_equal(true)
expect(authorize(principal, "room:write", "w1", 50).status).to_equal(403)
expect(authorize(principal, "room:read", "w2", 50).error).to_equal("workspace_access_denied")
expect(authorize(principal, "room:read", "w1", 100).error).to_equal("token_expired")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-002`
- `REQ-LLM-MSG-003`
- `REQ-LLM-MSG-009`
- `REQ-LLM-MSG-011`
- `REQ-LLM-MSG-015`
- `REQ-LLM-MSG-016`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e5287824272ee3026c0532207e6bd7155910ac5f691a3099ec686cf5489b9242`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5287824272ee3026c0532207e6bd7155910ac5f691a3099ec686cf5489b9242`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5287824272ee3026c0532207e6bd7155910ac5f691a3099ec686cf5489b9242`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/primitive_api_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/primitive_api_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/primitive_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/primitive_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/primitive_api_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/primitive_api_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 7 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/primitive_api_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes room resources, streaming, task actions, profiles, and webhooks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/primitive_api_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires bounded idempotency keys for writes and builds escaped responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/primitive_api_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bearer tokens and enforces expiry, workspace, and scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
