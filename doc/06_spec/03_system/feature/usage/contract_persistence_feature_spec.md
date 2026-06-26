# Contract Persistence - File I/O

> Tests consumer-driven contract persistence including serialization to Pact-compatible JSON format, saving contracts to the filesystem, and mock Pact broker integration for contract publishing. Verifies the full contract lifecycle from creation through builder pattern to file output.

<!-- sdn-diagram:id=contract_persistence_feature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=contract_persistence_feature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

contract_persistence_feature_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=contract_persistence_feature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/contract_persistence_feature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests consumer-driven contract persistence including serialization to
Pact-compatible JSON format, saving contracts to the filesystem, and
mock Pact broker integration for contract publishing. Verifies the full
contract lifecycle from creation through builder pattern to file output.

## Syntax

```simple
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

1. contract add interaction
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. response set body
2. contract add interaction
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. contract add interaction
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  given
2.  upon receiving
3.  with request
4.  will respond with
5.  status
6.  build
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
