# Provider Exact Envelope Abi Specification

> Tests covering exact SPipe provider envelope ABI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Exact Envelope Abi Specification

## Scenarios

### exact SPipe provider envelope ABI

#### preserves the complete service through the production struct envelope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CANCELLED
```

</details>

#### preserves the complete service through a tuple envelope

- preserves the complete service through a tuple envelope


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves the complete service through a tuple envelope")
val returned = tuple_envelope(abi_service())
assert_service(returned.0)
assert_outcome(returned.1)
```

</details>

#### preserves separately returned state service and outcome

- preserves separately returned state service and outcome
   - Expected: returned.0.scope_digest equals `"sha256:" + "4" * 64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves separately returned state service and outcome")
val returned = split_tuple_envelope(abi_service())
expect(returned.0.scope_digest).to_equal("sha256:" + "4" * 64)
assert_service(returned.1)
assert_outcome(returned.2)
```

</details>

#### preserves the complete service through a class envelope

- preserves the complete service through a class envelope


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves the complete service through a class envelope")
val returned = class_envelope(abi_service())
assert_service(returned.service)
assert_outcome(returned.outcome)
```

</details>

#### preserves computed bindings through wire-shaped reconstruction

- preserves computed bindings through wire-shaped reconstruction
   - Expected: returned.service.state.initialized is true
   - Expected: returned.service.state.workspace equals `WS-REBUILT`
   - Expected: returned.service.state.snapshot_id equals `"spks1-" + "c" * 64`
   - Expected: returned.service.state.scope_digest equals `"sha256:" + "d" * 64`
   - Expected: returned.service.state.logical_root equals `"sha256:" + "e" * 64`
   - Expected: returned.service.state.provider_generation equals `31`
   - Expected: returned.service.receipt_authority.available() is true
   - Expected: returned.service.durable_lifecycle.available() is true
   - Expected: returned.service.replay.len() equals `1`
   - Expected: returned.service.candidates.len() equals `1`
   - Expected: returned.service.current_document_ids equals `["DOC-ABI"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves computed bindings through wire-shaped reconstruction")
val returned = initialize_like_wire(abi_service())
expect(returned.service.state.initialized).to_equal(true)
expect(returned.service.state.workspace).to_equal("WS-REBUILT")
expect(returned.service.state.snapshot_id).to_equal("spks1-" + "c" * 64)
expect(returned.service.state.scope_digest).to_equal("sha256:" + "d" * 64)
expect(returned.service.state.logical_root).to_equal("sha256:" + "e" * 64)
expect(returned.service.state.provider_generation).to_equal(31)
expect(returned.service.receipt_authority.available()).to_equal(true)
expect(returned.service.durable_lifecycle.available()).to_equal(true)
expect(returned.service.replay.len()).to_equal(1)
expect(returned.service.candidates.len()).to_equal(1)
expect(returned.service.current_document_ids).to_equal(["DOC-ABI"])
assert_outcome(returned.outcome)
```

</details>

#### preserves owner state when the sibling outcome is derived from it

- preserves owner state when the sibling outcome is derived from it
   - Expected: returned.service.state.workspace equals `WS-DERIVED`
   - Expected: returned.service.state.scope_digest equals `"sha256:" + "d" * 64`
   - Expected: returned.service.state.provider_generation equals `37`
   - Expected: returned.service.receipt_authority.available() is true
   - Expected: returned.service.candidates.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves owner state when the sibling outcome is derived from it")
val returned = initialize_like_wire_with_owner_derived_outcome(abi_service())
expect(returned.service.state.workspace).to_equal("WS-DERIVED")
expect(returned.service.state.scope_digest).to_equal("sha256:" + "d" * 64)
expect(returned.service.state.provider_generation).to_equal(37)
expect(returned.outcome.frame).to_equal(
    "WS-DERIVED|sha256:" + "d" * 64 + "|37")
expect(returned.service.receipt_authority.available()).to_equal(true)
expect(returned.service.candidates.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering exact SPipe provider envelope ABI.
- exact SPipe provider envelope ABI

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

- `REQ-SSPEC-APP`
- `REQ-CANCELLED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `74158b50e29d59e8da86653bdc0dfefa84af5273235f2a675794ce6d9e53efef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74158b50e29d59e8da86653bdc0dfefa84af5273235f2a675794ce6d9e53efef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74158b50e29d59e8da86653bdc0dfefa84af5273235f2a675794ce6d9e53efef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.spl
mirror: doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.spl:178:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'preserves the complete service through the production struct envelope' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the complete service through a tuple envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves separately returned state service and outcome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_exact_envelope_abi_spec.spl:203:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the complete service through a class envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
