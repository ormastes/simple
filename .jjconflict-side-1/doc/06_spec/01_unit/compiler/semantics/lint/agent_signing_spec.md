# Agent Signing Specification

> Tests the agent signing mechanism for lint verification results. Each agent derives a private HMAC key from a master secret and its agent_id. Lint results are signed with this key and can be verified by any party that knows the master secret and the agent_id. Keys are never stored on disk.

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
| Updated | 2026-08-26 |
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

- produces a non-empty signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a non-empty signature")
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "REQC001\nREQC002")
expect(result.signature.len()).to_be_greater_than(0)
```

</details>

#### stores the agent_id in the signed result

- stores the agent_id in the signed result
   - Expected: result.agent_id equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores the agent_id in the signed result")
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "test", "REQC001")
expect(result.agent_id).to_equal("test")
```

</details>

#### stores the original payload in the signed result

- stores the original payload in the signed result
   - Expected: result.payload equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores the original payload in the signed result")
val master = "test-master-secret-32-bytes-long!!"
val payload = "code: REQC001\nsite: my_fn"
val result = sign_lint_result_test(master, "code", payload)
expect(result.payload).to_equal(payload)
```

</details>

#### signature is a hex string (contains only hex chars or is non-empty)

- signature is a hex string (contains only hex chars or is non-empty)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signature is a hex string (contains only hex chars or is non-empty)")
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "debug", "some warnings")
expect(result.signature.len()).to_be_greater_than(0)
```

</details>

### agent signing — verify_lint_result

#### when verifying an unmodified signed result

#### returns true for a freshly signed result

- returns true for a freshly signed result
   - Expected: verify_lint_result_test(master, result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for a freshly signed result")
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "REQC001")
expect(verify_lint_result_test(master, result)).to_equal(true)
```

</details>

#### returns true for an empty warning payload

- returns true for an empty warning payload
   - Expected: verify_lint_result_test(master, result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for an empty warning payload")
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "code", "")
expect(verify_lint_result_test(master, result)).to_equal(true)
```

</details>

#### returns true regardless of agent_id content

- returns true regardless of agent_id content
   - Expected: verify_lint_result_test(master, result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true regardless of agent_id content")
val master = "test-master-secret-32-bytes-long!!"
val result = sign_lint_result_test(master, "ml-agent-7", "REQC002")
expect(verify_lint_result_test(master, result)).to_equal(true)
```

</details>

### agent signing — tampered result rejected

#### when the payload is tampered

#### returns false after payload modification

- returns false after payload modification
   - Expected: verify_lint_result_test(master, tampered) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false after payload modification")
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

- returns false after signature modification
   - Expected: verify_lint_result_test(master, tampered) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false after signature modification")
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

- returns false after agent_id modification
   - Expected: verify_lint_result_test(master, tampered) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false after agent_id modification")
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

- returns false when verifying with a different master
   - Expected: verify_lint_result_test(master2, result) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when verifying with a different master")
val master1 = "correct-master-secret-32bytes!!!"
val master2 = "different-master-secret-32bytes!"
val result = sign_lint_result_test(master1, "code", "REQC001")
expect(verify_lint_result_test(master2, result)).to_equal(false)
```

</details>

### agent signing — per-agent key isolation

#### when two agents use the same master but different agent_ids

#### derived keys are different

- derived keys are different


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derived keys are different")
val master = "shared-master-secret-32-bytes!!!"
val key_code = derive_agent_key_test(master, "code")
val key_test = derive_agent_key_test(master, "test")
expect(key_code).to_not_equal(key_test)
```

</details>

#### agent A signature is invalid when checked as agent B

- agent A signature is invalid when checked as agent B
   - Expected: verify_lint_result_test(master, spoofed) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agent A signature is invalid when checked as agent B")
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

- agent B can produce its own valid signature for the same payload
   - Expected: verify_lint_result_test(master, result_b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agent B can produce its own valid signature for the same payload")
val master = "shared-master-secret-32-bytes!!!"
val payload = "REQC001"
val result_b = sign_lint_result_test(master, "test", payload)
expect(verify_lint_result_test(master, result_b)).to_equal(true)
```

</details>

#### when agent_id is the empty string

#### derived key is still deterministic

- derived key is still deterministic
   - Expected: key1 equals `key2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derived key is still deterministic")
val master = "shared-master-secret-32-bytes!!!"
val key1 = derive_agent_key_test(master, "")
val key2 = derive_agent_key_test(master, "")
expect(key1).to_equal(key2)
```

</details>

#### empty agent_id key differs from non-empty agent_id key

- empty agent_id key differs from non-empty agent_id key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty agent_id key differs from non-empty agent_id key")
val master = "shared-master-secret-32-bytes!!!"
val key_empty = derive_agent_key_test(master, "")
val key_code = derive_agent_key_test(master, "code")
expect(key_empty).to_not_equal(key_code)
```

</details>

### agent signing — serialize_warnings

#### empty warning list serializes to empty string

- empty warning list serializes to empty string
   - Expected: payload equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty warning list serializes to empty string")
val payload = serialize_warnings_test([])
expect(payload).to_equal("")
```

</details>

#### single warning serializes to text containing the code

- single warning serializes to text containing the code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single warning serializes to text containing the code")
val payload = serialize_warnings_test(["REQC001"])
expect(payload).to_contain("REQC001")
```

</details>

#### multiple warnings serialize to text containing all codes

- multiple warnings serialize to text containing all codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple warnings serialize to text containing all codes")
val payload = serialize_warnings_test(["REQC001", "REQC002"])
expect(payload).to_contain("REQC001")
expect(payload).to_contain("REQC002")
```

</details>

#### serialization is deterministic — same input, same output

- serialization is deterministic — same input, same output
   - Expected: p1 equals `p2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serialization is deterministic — same input, same output")
val p1 = serialize_warnings_test(["REQC001", "REQC002"])
val p2 = serialize_warnings_test(["REQC001", "REQC002"])
expect(p1).to_equal(p2)
```

</details>

#### different inputs produce different serializations

- different inputs produce different serializations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different inputs produce different serializations")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `677f66fcf8ff0abb4956d71150f17c7d0dc36ca0d0486eea10687ea79dc44246`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `677f66fcf8ff0abb4956d71150f17c7d0dc36ca0d0486eea10687ea79dc44246`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `677f66fcf8ff0abb4956d71150f17c7d0dc36ca0d0486eea10687ea79dc44246`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/lint/agent_signing_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/lint/agent_signing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/lint/agent_signing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/lint/agent_signing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/lint/agent_signing_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a non-empty signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/agent_signing_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores the agent_id in the signed result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/agent_signing_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores the original payload in the signed result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
