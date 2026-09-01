# Capability Policy Specification

> Tests covering Default-deny policy, Explicit capability grant, Explicit deny overrides grant, Allow-all policy, parse_capability round-trips.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Policy Specification

## Scenarios

### Default-deny policy

#### blocks ungranted capabilities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocks ungranted capabilities
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks ungranted capabilities")
val policy = default_deny_policy()
val result = check_capability(policy, "file_read")
expect(result).to_equal(false)
```

</details>

#### blocks all capabilities when nothing is granted

- blocks all capabilities when nothing is granted
   - Expected: read is false
   - Expected: write is false
   - Expected: net is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks all capabilities when nothing is granted")
val policy = default_deny_policy()
val read = check_capability(policy, "file_read")
val write = check_capability(policy, "file_write")
val net = check_capability(policy, "network")
expect(read).to_equal(false)
expect(write).to_equal(false)
expect(net).to_equal(false)
```

</details>

### Explicit capability grant

#### passes after explicit grant

- passes after explicit grant
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes after explicit grant")
var policy = default_deny_policy()
policy = grant_capability(policy, "file_read")
val result = check_capability(policy, "file_read")
expect(result).to_equal(true)
```

</details>

#### only grants the specified capability

- only grants the specified capability
   - Expected: read is true
   - Expected: write is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only grants the specified capability")
var policy = default_deny_policy()
policy = grant_capability(policy, "file_read")
val read = check_capability(policy, "file_read")
val write = check_capability(policy, "file_write")
expect(read).to_equal(true)
expect(write).to_equal(false)
```

</details>

### Explicit deny overrides grant

#### deny overrides a previous grant

- deny overrides a previous grant
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deny overrides a previous grant")
var policy = default_deny_policy()
policy = grant_capability(policy, "network")
policy = deny_capability(policy, "network")
val result = check_capability(policy, "network")
expect(result).to_equal(false)
```

</details>

### Allow-all policy

#### passes everything

- passes everything
   - Expected: read is true
   - Expected: write is true
   - Expected: net is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes everything")
val policy = allow_all_policy()
val read = check_capability(policy, "file_read")
val write = check_capability(policy, "file_write")
val net = check_capability(policy, "network")
expect(read).to_equal(true)
expect(write).to_equal(true)
expect(net).to_equal(true)
```

</details>

### parse_capability round-trips

#### round-trips file_read

- round-trips file_read
   - Expected: name equals `file_read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips file_read")
val cap = parse_capability("file_read")
val name = capability_to_string(cap)
expect(name).to_equal("file_read")
```

</details>

#### round-trips file_write

- round-trips file_write
   - Expected: name equals `file_write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips file_write")
val cap = parse_capability("file_write")
val name = capability_to_string(cap)
expect(name).to_equal("file_write")
```

</details>

#### round-trips network

- round-trips network
   - Expected: name equals `network`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips network")
val cap = parse_capability("network")
val name = capability_to_string(cap)
expect(name).to_equal("network")
```

</details>

#### round-trips process_spawn

- round-trips process_spawn
   - Expected: name equals `process_spawn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips process_spawn")
val cap = parse_capability("process_spawn")
val name = capability_to_string(cap)
expect(name).to_equal("process_spawn")
```

</details>

#### round-trips env_access

- round-trips env_access
   - Expected: name equals `env_access`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips env_access")
val cap = parse_capability("env_access")
val name = capability_to_string(cap)
expect(name).to_equal("env_access")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/capability_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Default-deny policy, Explicit capability grant, Explicit deny overrides grant, Allow-all policy, parse_capability round-trips.
- Default-deny policy
- Explicit capability grant
- Explicit deny overrides grant
- Allow-all policy
- parse_capability round-trips

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `6ce6e15369411a8e8fde2da224c56f92d58d4f38a19b447175b41f8b86ff4108`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ce6e15369411a8e8fde2da224c56f92d58d4f38a19b447175b41f8b86ff4108`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ce6e15369411a8e8fde2da224c56f92d58d4f38a19b447175b41f8b86ff4108`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/capability_policy_spec.spl
mirror: doc/06_spec/unit/app/ui/capability_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/capability_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/capability_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/capability_policy_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks ungranted capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/capability_policy_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks all capabilities when nothing is granted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/capability_policy_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes after explicit grant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
