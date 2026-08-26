# SPipe Knowledge Compiler primary workflow

> This is an authored, deliberately failing design scaffold. It defines the five

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe Knowledge Compiler primary workflow

This is an authored, deliberately failing design scaffold. It defines the five

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and status
This is an authored, deliberately failing design scaffold. It defines the five
frozen operator flows and does not claim generated or runtime evidence.

## Requirement map
- Index: REQ-SPKC-001..005, 017..018, 028..029; NFR-SPKC-001..002, 009..010, 023.
- Browse: REQ-SPKC-006..009, 026, 030; NFR-SPKC-003..005, 011, 019.
- Search/trace: REQ-SPKC-017..018; NFR-SPKC-001..002.
- Refactor: REQ-SPKC-019..020, 029; NFR-SPKC-008..010.
- Audit/promotion: REQ-SPKC-021..025; NFR-SPKC-017..018, 024.
- Evidence/delivery: REQ-SPKC-027..030; NFR-SPKC-020..022, 025.

## Frozen workflow
Index canonical knowledge artifacts; Browse virtual knowledge views; Search and
trace artifacts; Apply a transactional refactor; Audit tree balance and
promotion candidates.

## Generation
After production oracles replace fail-fast helpers, run:
`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl --output doc/06_spec --no-index`.

## Scenarios

### SPipe Knowledge Compiler primary operator workflow

#### index canonical artifacts into an isolated deterministic snapshot

- Index canonical knowledge artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-017..018
# @req REQ-SPKC-001..005
# @req REQ-SPKC-006..009
# @req REQ-SPKC-019..020
# @req REQ-SPKC-021..025
# @req REQ-SPKC-027..030
# @req REQ-SPKC-029..005
# @req: REQ-SPKC-029, REQ-SPKC-029, REQ-SPKC-029, REQ-SPKC-029, REQ-SPKC-029, REQ-SPKC-029, REQ-SPKC-029
step("Index canonical knowledge artifacts")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
setup_spipe_knowledge_fixture()
check_spipe_knowledge_compiler()
```

</details>

#### browse bounded read-only projections without changing identity

- Browse virtual knowledge views


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-006, REQ-SPKC-007, REQ-SPKC-008, REQ-SPKC-009, REQ-SPKC-026, REQ-SPKC-030
step("Browse virtual knowledge views")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
check_spipe_virtual_view_safety()
```

</details>

#### explain accepted and candidate trace evidence separately

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-017, REQ-SPKC-018
step("Search and trace artifacts")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
check_spipe_provider_parity()
```

</details>

#### preserve exact old or new state across an approved refactor

- Apply a transactional refactor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-019, REQ-SPKC-020, REQ-SPKC-029
step("Apply a transactional refactor")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
check_spipe_refactor_recovery()
```

</details>

#### emit reviewable organization and promotion proposals

- Audit tree balance and promotion candidates


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-021, REQ-SPKC-022, REQ-SPKC-023, REQ-SPKC-024, REQ-SPKC-025
step("Audit tree balance and promotion candidates")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
fail("DESIGN-SCAFFOLD: connect tree and promotion production oracles")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SPKC-029`
- `REQ-SPKC-017..018`
- `REQ-SPKC-001..005`
- `REQ-SPKC-006..009`
- `REQ-SPKC-017..018;`
- `REQ-SPKC-019..020`
- `REQ-SPKC-021..025;`
- `REQ-SPKC-027..030;`
- `REQ-SPKC-021..025`
- `REQ-SPKC-027..030`
- `REQ-SPKC-029..005`
- `REQ-SPKC-006`
- `REQ-SPKC-007`
- `REQ-SPKC-008`
- `REQ-SPKC-009`
- `REQ-SPKC-026`
- `REQ-SPKC-030`
- `REQ-SPKC-017`
- `REQ-SPKC-018`
- `REQ-SPKC-019`
- `REQ-SPKC-020`
- `REQ-SPKC-021`
- `REQ-SPKC-022`
- `REQ-SPKC-023`
- `REQ-SPKC-024`
- `REQ-SPKC-025`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64ee67920de637dad533606f75f3e163ae9940dce2f812dc1d6a49025cb372f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64ee67920de637dad533606f75f3e163ae9940dce2f812dc1d6a49025cb372f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64ee67920de637dad533606f75f3e163ae9940dce2f812dc1d6a49025cb372f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->
