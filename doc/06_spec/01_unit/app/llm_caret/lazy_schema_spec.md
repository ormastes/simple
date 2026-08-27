# Claude Full lazy schema

> Pure Simple coverage for deferred schema factory caching.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full lazy schema

Pure Simple coverage for deferred schema factory caching.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/lazy_schema_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for deferred schema factory caching.

## Scenarios

### Claude full lazy schema

#### defers schema creation until first read and reuses the cached value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defers schema creation until first read and reuses the cached value
- Create lazy schema without invoking factory
   - Expected: lazy.factoryCalls equals `0`
- Read schema once
   - Expected: first.value equals `{"type":"object"}`
   - Expected: first.state.cached equals `Some("{"type":"object"}")`
   - Expected: first.state.factoryCalls equals `1`
- Read schema again
   - Expected: second.value equals `{"type":"object"}`
   - Expected: second.state.factoryCalls equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defers schema creation until first read and reuses the cached value")
step("Create lazy schema without invoking factory")
val lazy = lazySchemaText(\: "{\"type\":\"object\"}")
expect(lazy.cached).to_be_nil()
expect(lazy.factoryCalls).to_equal(0)

step("Read schema once")
val first = lazy.read()
expect(first.value).to_equal("{\"type\":\"object\"}")
expect(first.state.cached).to_equal(Some("{\"type\":\"object\"}"))
expect(first.state.factoryCalls).to_equal(1)

step("Read schema again")
val second = first.state.read()
expect(second.value).to_equal("{\"type\":\"object\"}")
expect(second.state.factoryCalls).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `90597564a464798f27705ced3729025fd8e64314b345485ca70e519dd2a986a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90597564a464798f27705ced3729025fd8e64314b345485ca70e519dd2a986a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90597564a464798f27705ced3729025fd8e64314b345485ca70e519dd2a986a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/llm_caret/lazy_schema_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/lazy_schema_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/lazy_schema_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/lazy_schema_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/lazy_schema_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/lazy_schema_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defers schema creation until first read and reuses the cached value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
