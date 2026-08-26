# SPipe knowledge-compiler provider parity

> This executable manual owns the Wave 4 provider-parity acceptance surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe knowledge-compiler provider parity

This executable manual owns the Wave 4 provider-parity acceptance surface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This executable manual owns the Wave 4 provider-parity acceptance surface.
Every scenario invokes the same locked `check_spipe_provider_parity` gate.
The JavaScript provider and focused Simple/DBFS production fixtures execute.
The Node acceptance runner rejects a successful spec verdict unless the fixture
also emits exactly one `SPIPE_WAVE4_CONFORMANCE=` JSON record conforming to
`conformance_evidence_schema.json`. Simple and DBFS do not yet emit canonical five-field roots,
scores, statistics, explanations, and deltas for every applicable matrix row.
Until they do, the gate fails with `NOT-EVIDENCE`; source presence and a
narrower green fixture are never provider-parity evidence.

Fixture oracle:
`examples/05_stdlib/spipe/test/fixture/wave4_search/fixture_manifest.json`.

## Scenarios

### SPipe knowledge compiler provider parity

#### should return identical golden ordering and scores across fallback and Simple providers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-011, REQ-SPKC-012, REQ-SPKC-013
step("Search and trace artifacts")
check_spipe_provider_parity()
```

</details>

#### should keep exact identity dominant and break lexical ties by public document ID

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-011, REQ-SPKC-012
step("Search and trace artifacts")
check_spipe_provider_parity()
```

</details>

#### should reject phrase queries and apply metadata equality filters identically in version 1

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-011, REQ-SPKC-012
step("Search and trace artifacts")
check_spipe_provider_parity()
```

</details>

#### should return bounded canonical explanations for every ranked hit

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-013
step("Search and trace artifacts")
check_spipe_provider_parity()
```

</details>

#### should make mixed incremental deltas equal a clean rebuilt snapshot

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-012, REQ-SPKC-014
step("Search and trace artifacts")
check_spipe_provider_parity()
```

</details>

#### should degrade process and semantic provider failures without a false semantic pass

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-013, REQ-SPKC-015, REQ-SPKC-016, REQ-SPKC-017, REQ-SPKC-018
step("Search and trace artifacts")
check_spipe_provider_parity()
```

</details>

#### should reject every query and response resource boundary at limit plus one

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-011, REQ-SPKC-012, REQ-SPKC-013
step("Search and trace artifacts")
check_spipe_provider_parity()
```

</details>

#### should meet qualified warm-query and incremental-update latency gates

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-011, REQ-SPKC-012, REQ-SPKC-014
step("Search and trace artifacts")
check_spipe_provider_parity()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SPKC-011`
- `REQ-SPKC-012`
- `REQ-SPKC-013`
- `REQ-SPKC-014`
- `REQ-SPKC-015`
- `REQ-SPKC-016`
- `REQ-SPKC-017`
- `REQ-SPKC-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `75f64a5ca937bda5c25a33f0f620668f91e89a50a7a115e20c7825ac817fbede`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75f64a5ca937bda5c25a33f0f620668f91e89a50a7a115e20c7825ac817fbede`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75f64a5ca937bda5c25a33f0f620668f91e89a50a7a115e20c7825ac817fbede`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return identical golden ordering and scores across fallback and Simple providers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return identical golden ordering and scores across fallback and Simple providers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep exact identity dominant and break lexical ties by public document ID' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep exact identity dominant and break lexical ties by public document ID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject phrase queries and apply metadata equality filters identically in version 1' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject phrase queries and apply metadata equality filters identically in version 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return bounded canonical explanations for every ranked hit' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should make mixed incremental deltas equal a clean rebuilt snapshot' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should degrade process and semantic provider failures without a false semantic pass' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
