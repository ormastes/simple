# generic_http_transport_spec

> Generic HTTP transport authenticates webhooks and rejects replay attacks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# generic_http_transport_spec

Generic HTTP transport authenticates webhooks and rejects replay attacks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/generic_http_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Generic HTTP transport authenticates webhooks and rejects replay attacks.

## Scenarios

### generic HTTP chat transport

#### signs and verifies a bounded inbound webhook

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- signs and verifies a bounded inbound webhook
   - Expected: transport.connect("binding-1") equals `connected:generic_http:binding-1`
   - Expected: outbound.accepted is true
   - Expected: verified.accepted is true
   - Expected: verified.duplicate is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("signs and verifies a bounded inbound webhook")
var transport = GenericHttpTransport.new("https://example.invalid/hooks/chat",
    "0123456789abcdef0123456789abcdef")
expect(transport.connect("binding-1")).to_equal("connected:generic_http:binding-1")
val outbound = transport.prepare_outbound("binding-1", "event-1", "{\"body\":\"hello\"}", 1000000)
expect(outbound.accepted).to_equal(true)
expect(outbound.signature).to_start_with("v1=")
val verified = transport.verify_inbound("binding-1", outbound.event_id, outbound.body,
    outbound.timestamp_ms, outbound.signature, 1000100)
expect(verified.accepted).to_equal(true)
expect(verified.duplicate).to_equal(false)
```

</details>

#### rejects tampering stale timestamps and marks authenticated replay

- rejects tampering stale timestamps and marks authenticated replay
   - Expected: tampered.error equals `webhook_signature_invalid`
   - Expected: stale.error equals `webhook_timestamp_out_of_range`
   - Expected: first.accepted is true
   - Expected: replay.duplicate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects tampering stale timestamps and marks authenticated replay")
var transport = GenericHttpTransport.new("https://example.invalid/hooks/chat",
    "0123456789abcdef0123456789abcdef")
transport.connect("binding-1")
val envelope = transport.prepare_outbound("binding-1", "event-2", "payload", 2000000)
val tampered = transport.verify_inbound("binding-1", "event-2", "changed", 2000000,
    envelope.signature, 2000100)
expect(tampered.error).to_equal("webhook_signature_invalid")
val stale = transport.verify_inbound("binding-1", "event-2", "payload", 2000000,
    envelope.signature, 2400001)
expect(stale.error).to_equal("webhook_timestamp_out_of_range")
val first = transport.verify_inbound("binding-1", "event-2", "payload", 2000000,
    envelope.signature, 2000100)
val replay = transport.verify_inbound("binding-1", "event-2", "payload", 2000000,
    envelope.signature, 2000100)
expect(first.accepted).to_equal(true)
expect(replay.duplicate).to_equal(true)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-003`
- `REQ-LLM-MSG-009`
- `REQ-LLM-MSG-017`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08a60cd5968de7468fd5c871649a263afd47819c2f609e1aa8c127ede4b013fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08a60cd5968de7468fd5c871649a263afd47819c2f609e1aa8c127ede4b013fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08a60cd5968de7468fd5c871649a263afd47819c2f609e1aa8c127ede4b013fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/generic_http_transport_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/generic_http_transport_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/generic_http_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/generic_http_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/generic_http_transport_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/generic_http_transport_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signs and verifies a bounded inbound webhook' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/generic_http_transport_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects tampering stale timestamps and marks authenticated replay' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
