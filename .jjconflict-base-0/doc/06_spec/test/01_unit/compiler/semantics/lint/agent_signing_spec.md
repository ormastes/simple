# Agent Signing Specification

> Tests the agent signing mechanism for lint verification results. Each agent derives a private HMAC key from a master secret and its agent_id. Lint results are signed with this key and can be verified by any party that knows the master secret and the agent_id. Keys are never stored on disk.

<!-- sdn-diagram:id=agent_signing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_signing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_signing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_signing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Signing Specification

Tests the agent signing mechanism for lint verification results. Each agent derives a private HMAC key from a master secret and its agent_id. Lint results are signed with this key and can be verified by any party that knows the master secret and the agent_id. Keys are never stored on disk.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REQC-AC7 |
| Category | Compiler \| Semantics \| Lint \| Signing |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/semantics/lint/agent_signing_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the agent signing mechanism for lint verification results. Each agent
derives a private HMAC key from a master secret and its agent_id. Lint results
are signed with this key and can be verified by any party that knows the master
secret and the agent_id. Keys are never stored on disk.

## Key Concepts

| Concept | Description |
|---------|-------------|
| agent_id | Stable text identifier for an agent ("code", "test", "debug", …) |
| master_secret | SIMPLE_AGENT_MASTER_KEY env var — known to agent spawner |
| derived_key | hmac_sha256(master_secret, agent_id) — per-agent, not stored |
| SignedLintResult | Struct: agent_id, payload (SDN text), signature (HMAC-SHA256 hex) |
| sign_lint_result | Produces a SignedLintResult from agent_id + payload |
| verify_lint_result | Returns true iff signature matches recomputed HMAC |
| tampered | Any change to payload or signature makes verify_lint_result return false |

## Scenarios

### agent signing — sign_lint_result

#### when signing with a valid master secret and agent_id

#### produces a non-empty signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "REQC001\nREQC002")
expect(result.signature.len()).to_be_greater_than(0)
```

</details>

#### stores the agent_id in the signed result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "test", "REQC001")
expect(result.agent_id).to_equal("test")
```

</details>

#### stores the original payload in the signed result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val payload = "code: REQC001\nsite: my_fn"
val result = sign_lint_result_test(master, "code", payload)
expect(result.payload).to_equal(payload)
```

</details>

#### signature is a hex string (contains only hex chars or is non-empty)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "debug", "some warnings")
expect(result.signature.len()).to_be_greater_than(0)
```

</details>

### agent signing — verify_lint_result

#### when verifying an unmodified signed result

#### returns true for a freshly signed result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "REQC001")
expect(verify_lint_result_test(master, result)).to_equal(true)
```

</details>

#### returns true for an empty warning payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "")
expect(verify_lint_result_test(master, result)).to_equal(true)
```

</details>

#### returns true regardless of agent_id content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "ml-agent-7", "REQC002")
expect(verify_lint_result_test(master, result)).to_equal(true)
```

</details>

### agent signing — tampered result rejected

#### when the payload is tampered

#### returns false after payload modification

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "REQC001")
val tampered = SignedLintResultTest(
    agent_id: result.agent_id,
    payload: "REQC001\nREQC002",   # extra line injected
    signature: result.signature
)
expect(verify_lint_result_test(master, tampered)).to_equal(false)
```

</details>

#### when the signature is tampered

#### returns false after signature modification

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "REQC001")
val tampered = SignedLintResultTest(
    agent_id: result.agent_id,
    payload: result.payload,
    signature: "deadbeef00000000000000000000000000000000000000000000000000000000"
)
expect(verify_lint_result_test(master, tampered)).to_equal(false)
```

</details>

#### when the agent_id is tampered

#### returns false after agent_id modification

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "REQC001")
val tampered = SignedLintResultTest(
    agent_id: "debug",              # different agent
    payload: result.payload,
    signature: result.signature
)
expect(verify_lint_result_test(master, tampered)).to_equal(false)
```

</details>

#### when the master secret is wrong

#### returns false when verifying with a different master

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master1 = "correct-master-secret-32bytes!!!"
val master2 = "different-master-secret-32bytes!"
val result = sign_lint_result_test(master1, "code", "REQC001")
expect(verify_lint_result_test(master2, result)).to_equal(false)
```

</details>

### agent signing — per-agent key isolation

#### when two agents use the same master but different agent_ids

#### derived keys are different

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "shared-master-secret-32-bytes!!!"
val key_code = derive_agent_key_test(master, "code")
val key_test = derive_agent_key_test(master, "test")
expect(key_code).to_not_equal(key_test)
```

</details>

#### agent A signature is invalid when checked as agent B

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "shared-master-secret-32-bytes!!!"
val payload = "REQC001"
val result_a = sign_lint_result_test(master, "code", payload)
# Attempt to verify as if it was signed by "test" agent
val spoofed = SignedLintResultTest(
    agent_id: "test",
    payload: result_a.payload,
    signature: result_a.signature
)
expect(verify_lint_result_test(master, spoofed)).to_equal(false)
```

</details>

#### agent B can produce its own valid signature for the same payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "shared-master-secret-32-bytes!!!"
val payload = "REQC001"
val result_b = sign_lint_result_test(master, "test", payload)
expect(verify_lint_result_test(master, result_b)).to_equal(true)
```

</details>

#### when agent_id is the empty string

#### derived key is still deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "shared-master-secret-32-bytes!!!"
val key1 = derive_agent_key_test(master, "")
val key2 = derive_agent_key_test(master, "")
expect(key1).to_equal(key2)
```

</details>

#### empty agent_id key differs from non-empty agent_id key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = "shared-master-secret-32-bytes!!!"
val key_empty = derive_agent_key_test(master, "")
val key_code = derive_agent_key_test(master, "code")
expect(key_empty).to_not_equal(key_code)
```

</details>

### agent signing — serialize_warnings

#### empty warning list serializes to empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = serialize_warnings_test([])
expect(payload).to_equal("")
```

</details>

#### single warning serializes to text containing the code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = serialize_warnings_test(["REQC001"])
expect(payload).to_contain("REQC001")
```

</details>

#### multiple warnings serialize to text containing all codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = serialize_warnings_test(["REQC001", "REQC002"])
expect(payload).to_contain("REQC001")
expect(payload).to_contain("REQC002")
```

</details>

#### serialization is deterministic — same input, same output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = serialize_warnings_test(["REQC001", "REQC002"])
val p2 = serialize_warnings_test(["REQC001", "REQC002"])
expect(p1).to_equal(p2)
```

</details>

#### different inputs produce different serializations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = serialize_warnings_test(["REQC001"])
val p2 = serialize_warnings_test(["REQC002"])
expect(p1).to_not_equal(p2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
