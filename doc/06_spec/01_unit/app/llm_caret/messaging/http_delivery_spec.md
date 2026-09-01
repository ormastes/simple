# http_delivery_spec

> HTTP delivery classification preserves retry and receipt truth.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# http_delivery_spec

HTTP delivery classification preserves retry and receipt truth.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/http_delivery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

HTTP delivery classification preserves retry and receipt truth.

## Scenarios

### LLM Caret HTTP transport delivery classification

#### accepts only successful remote API responses

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only successful remote API responses
   - Expected: delivered.accepted is true
   - Expected: delivered.retryable is false
   - Expected: delivered.permanent is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only successful remote API responses")
val delivered = classify_http_delivery(201, "created", "")
expect(delivered.accepted).to_equal(true)
expect(delivered.retryable).to_equal(false)
expect(delivered.permanent).to_equal(false)
```

</details>

#### retries rate limits, server failures, and connection failures

- retries rate limits, server failures, and connection failures
   - Expected: classify_http_delivery(429, "", "rate limited").retryable is true
   - Expected: classify_http_delivery(503, "", "").retryable is true
   - Expected: classify_http_delivery(0, "", "connection failed").retryable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("retries rate limits, server failures, and connection failures")
expect(classify_http_delivery(429, "", "rate limited").retryable).to_equal(true)
expect(classify_http_delivery(503, "", "").retryable).to_equal(true)
expect(classify_http_delivery(0, "", "connection failed").retryable).to_equal(true)
```

</details>

#### dead-letters non-retryable client failures

- dead-letters non-retryable client failures
   - Expected: rejected.accepted is false
   - Expected: rejected.retryable is false
   - Expected: rejected.permanent is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("dead-letters non-retryable client failures")
val rejected = classify_http_delivery(403, "forbidden", "")
expect(rejected.accepted).to_equal(false)
expect(rejected.retryable).to_equal(false)
expect(rejected.permanent).to_equal(true)
```

</details>

#### persists only a credential reference and materializes authorization in memory

- persists only a credential reference and materializes authorization in memory
   - Expected: request_template.accepted is true
   - Expected: request_template.headers.join(" | ") does not contain `resolved-secret`
   - Expected: request_template.credential_ref equals `secret://slack/development`
   - Expected: persisted.len() equals `1`
   - Expected: persisted[0].headers.join(" | ") does not contain `resolved-secret`
   - Expected: persisted[0].credential_ref equals `secret://slack/development`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("persists only a credential reference and materializes authorization in memory")
val prepared = ChatHttpRequest(accepted: true, method: "POST", url: "https://chat.example/send",
    headers: ["Authorization: Bearer resolved-secret", "Content-Type: application/json"],
    body: "{}", idempotency_key: "stable-delivery-key", error: "")
val request_template = credential_request_template(prepared, "secret://slack/development",
    "bearer", "resolved-secret")
expect(request_template.accepted).to_equal(true)
expect(request_template.headers.join(" | ").contains("resolved-secret")).to_equal(false)
expect(request_template.credential_ref).to_equal("secret://slack/development")
val materialized = materialize_credential_request(request_template, "resolved-secret")
expect(materialized.headers.join(" | ")).to_contain("Authorization: Bearer resolved-secret")
val store = PureSqlMessagingStore.open_memory()
expect(queue_prepared_transport_request(store, "delivery-safe", "message-safe", "binding-safe",
    prepared, "secret://slack/development", "bearer", "resolved-secret", 10).ok).to_equal(true)
val persisted = store.queued_transport_requests(10, 10)
expect(persisted.len()).to_equal(1)
expect(persisted[0].headers.join(" | ").contains("resolved-secret")).to_equal(false)
expect(persisted[0].credential_ref).to_equal("secret://slack/development")
```

</details>

#### replaces URL credentials before persistence

- replaces URL credentials before persistence
   - Expected: request_template.url_template does not contain `telegram-secret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("replaces URL credentials before persistence")
val prepared = ChatHttpRequest(accepted: true, method: "POST",
    url: "https://api.telegram.org/bottelegram-secret/sendMessage", headers: [], body: "{}",
    idempotency_key: "stable-telegram-key", error: "")
val request_template = credential_request_template(prepared, "secret://telegram/development",
    "url_token", "telegram-secret")
expect(request_template.url_template.contains("telegram-secret")).to_equal(false)
expect(request_template.url_template).to_contain("__LLM_CARET_CREDENTIAL__")
expect(materialize_credential_request(request_template, "telegram-secret").url).to_contain(
    "bottelegram-secret/sendMessage")
```

</details>

#### dead-letters a queued request when its process-scoped secret is unavailable

- dead-letters a queued request when its process-scoped secret is unavailable
   - Expected: store.enqueue_transport_request(queued, 10).ok is true
   - Expected: drained.0 equals `0`
   - Expected: drained.1 equals `1`
   - Expected: store.outbox_state("delivery-missing-secret") equals `dead_letter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("dead-letters a queued request when its process-scoped secret is unavailable")
val store = PureSqlMessagingStore.open_memory()
val queued = StoredTransportRequest(delivery_id: "delivery-missing-secret",
    message_id: "message-1", binding_id: "binding-1", method: "POST",
    url_template: "https://chat.example/send", headers: ["Content-Type: application/json"],
    body: "{}", credential_ref: "secret://test/definitely-unavailable-credential",
    credential_mode: "bearer", idempotency_key: "stable-missing-secret")
expect(store.enqueue_transport_request(queued, 10).ok).to_equal(true)
val drained = drain_transport_outbox(store, 10, 20, 1000, 1)
expect(drained.0).to_equal(0)
expect(drained.1).to_equal(1)
expect(store.outbox_state("delivery-missing-secret")).to_equal("dead_letter")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-003`
- `REQ-LLM-MSG-016`
- `REQ-LLM-MSG-017`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `97b7e154fbfeadd07f1ba20eb337479a7897335df61087dd69762bd10252dc13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97b7e154fbfeadd07f1ba20eb337479a7897335df61087dd69762bd10252dc13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97b7e154fbfeadd07f1ba20eb337479a7897335df61087dd69762bd10252dc13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/http_delivery_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/http_delivery_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/http_delivery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/http_delivery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/http_delivery_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/http_delivery_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/http_delivery_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only successful remote API responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/http_delivery_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retries rate limits, server failures, and connection failures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/http_delivery_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dead-letters non-retryable client failures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
