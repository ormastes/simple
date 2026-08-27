# generic_bytecode_spec

> Purpose: generic templates in SMF are observed two ways — production .smf

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# generic_bytecode_spec

Purpose: generic templates in SMF are observed two ways — production .smf

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/feature/usage/generic_bytecode_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: generic templates in SMF are observed two ways — production .smf
artifacts exist on disk for the async subtree, and generic functions
instantiate with independent type arguments at runtime. Audience: compiler
engineers maintaining SMF serialization of generic templates.

## Scenarios

### Generic Template Bytecode in SMF

#### compiled stdlib modules retain .smf bytecode artifacts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify: async stdlib subtree ships .smf bytecode
   - Expected: file_exists("src/lib/nogc_async_mut/actor_heap.smf") is true
   - Expected: file_exists("src/lib/nogc_async_mut/actor_scheduler.smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: async stdlib subtree ships .smf bytecode")
expect(file_exists("src/lib/nogc_async_mut/actor_heap.smf")).to_equal(true)  # oracle: module compiled to SMF
expect(file_exists("src/lib/nogc_async_mut/actor_scheduler.smf")).to_equal(true)  # oracle: scheduler compiled to SMF
```

</details>

#### a generic template instantiates independently per type argument

- Verify: one template serves i64 and text instantiations
   - Expected: pick_first(10, 20) equals `10`
   - Expected: pick_first("alpha", "beta") equals `alpha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: one template serves i64 and text instantiations")
expect(pick_first(10, 20)).to_equal(10)  # oracle: first argument wins for i64
expect(pick_first("alpha", "beta")).to_equal("alpha")  # oracle: first argument wins for text
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b984d9e416b421bb52905fbc8458cfab98b40907996be46ee597fe8697397198`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b984d9e416b421bb52905fbc8458cfab98b40907996be46ee597fe8697397198`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b984d9e416b421bb52905fbc8458cfab98b40907996be46ee597fe8697397198`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/feature/usage/generic_bytecode_spec.spl
mirror: doc/06_spec/feature/usage/generic_bytecode_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/generic_bytecode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/generic_bytecode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/generic_bytecode_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiled stdlib modules retain .smf bytecode artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/generic_bytecode_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a generic template instantiates independently per type argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
