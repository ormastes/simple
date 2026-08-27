# Contract Persistence - File I/O

> Tests consumer-driven contract persistence including serialization to Pact-compatible JSON format, saving contracts to the filesystem, and mock Pact broker integration for contract publishing. Verifies the full contract lifecycle from creation through builder pattern to file output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract Persistence - File I/O

Tests consumer-driven contract persistence including serialization to Pact-compatible JSON format, saving contracts to the filesystem, and mock Pact broker integration for contract publishing. Verifies the full contract lifecycle from creation through builder pattern to file output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TEST-001 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/feature/usage/contract_persistence_feature_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests consumer-driven contract persistence including serialization to
Pact-compatible JSON format, saving contracts to the filesystem, and
mock Pact broker integration for contract publishing. Verifies the full
contract lifecycle from creation through builder pattern to file output.

## Syntax

```simple
use std.spec.step

val contract = ct.Contract__new("web-app", "user-api")
val json = contract.to_pact_json()
val result = contract.save("/tmp/contract-test.json")
```
Contract Persistence Feature Spec

Feature: Save contracts to files for later verification
Implements Pact-compatible contract persistence

## Scenarios

### Feature #2401: Contract Persistence - File I/O

#### Contract serialization

#### converts contract to valid JSON

- converts contract to valid JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts contract to valid JSON")
val contract = ct.Contract__new("web-app", "user-api")
val request = ct.HttpRequest__new("GET", "/users/1")
val response = ct.HttpResponse__new(200)
val interaction = ct.Interaction__new("get user", request, response)
contract.add_interaction(interaction)

val json = contract.to_pact_json()
check(json.contains("consumer"))
check(json.contains("provider"))
check(json.contains("interactions"))
```

</details>

#### includes all interaction details in JSON

- includes all interaction details in JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes all interaction details in JSON")
val contract = ct.Contract__new("app", "api")
val request = ct.HttpRequest__new("POST", "/data")
val response = ct.HttpResponse__new(201)
response.set_body("" + "{" + "\"status\": \"created\"" + "}")
val interaction = ct.Interaction__new("create resource", request, response)
contract.add_interaction(interaction)

val json = contract.to_pact_json()
check(json.contains("POST"))
check(json.contains("/data"))
check(json.contains("201"))
```

</details>

#### Contract file persistence

#### saves contract to file

- saves contract to file


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("saves contract to file")
val contract = ct.Contract__new("client", "provider")
val request = ct.HttpRequest__new("GET", "/api/data")
val response = ct.HttpResponse__new(200)
val interaction = ct.Interaction__new("fetch data", request, response)
contract.add_interaction(interaction)

val result = contract.save("/tmp/contract-test.json")
check(result.is_ok())
```

</details>

#### returns error when save fails

- returns error when save fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns error when save fails")
val contract = ct.Contract__new("client", "provider")
# Try to save to an invalid path
val result = contract.save("/root/invalid/path/contract.json")
# Should fail gracefully
# Either error or permission-based success
check(result.is_err() or result.is_ok())
```

</details>

#### Pact broker integration

#### enables contracts for broker publishing

- enables contracts for broker publishing


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("enables contracts for broker publishing")
val contract = ct.ContractBuilder__new("consumer", "provider")
    .given("ready")
    .upon_receiving("request")
    .with_request("GET", "/api")
    .will_respond_with()
    .status(200)
    .build()

val broker = ct.PactBroker__new("https://broker.example.com")
val result = broker.publish(contract, "1.0.0")
check(result.is_ok())
```

</details>

#### Usage examples

#### demonstrates saving contracts

- demonstrates saving contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("demonstrates saving contracts")
# ```simple
# # Create and save a contract
# val contract = ContractBuilder__new("web-app", "api")
# .given("user exists")
# .upon_receiving("get user")
# .with_request("GET", "/users/123")
# .will_respond_with()
# .status(200)
# .build()
#
# val result = contract.save("pacts/web-app-api.json")
# if result.is_ok():
# print("Contract saved successfully")
# else:
# print("Failed to save contract")
# ```
pass
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d17f3d48dbfe4d18a32505d20999ea04f002c14f0553f31666e181531f08fb69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d17f3d48dbfe4d18a32505d20999ea04f002c14f0553f31666e181531f08fb69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d17f3d48dbfe4d18a32505d20999ea04f002c14f0553f31666e181531f08fb69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/contract_persistence_feature_spec.spl
mirror: doc/06_spec/feature/usage/contract_persistence_feature_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/contract_persistence_feature_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/contract_persistence_feature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/contract_persistence_feature_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts contract to valid JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/contract_persistence_feature_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes all interaction details in JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/contract_persistence_feature_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'saves contract to file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
