# Claude Full SDK Core Schemas Slice

> Focused coverage for shared SDK envelope schema routes from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full SDK Core Schemas Slice

Focused coverage for shared SDK envelope schema routes from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for shared SDK envelope schema routes from
entrypoints/sdk/coreSchemas.ts.

## Scenarios

### Claude full SDK core schemas parity

#### should model primitive enum and usage schemas

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model primitive enum and usage schemas
- Check primitive schemas
   - Expected: modelUsageSchemaRoute(8, true) is true
   - Expected: modelUsageSchemaRoute(7, false) is false
   - Expected: apiKeySourceSchemaRoute("temporary") is true
   - Expected: apiKeySourceSchemaRoute("oauth") is true
   - Expected: apiKeySourceSchemaRoute("env") is false
   - Expected: permissionModeSchemaRoute("acceptEdits") is true
   - Expected: permissionModeSchemaRoute("dontAsk") is true
   - Expected: sdkStatusSchemaRoute("compacting") is true
   - Expected: sdkStatusSchemaRoute("null") is true
   - Expected: sdkStatusSchemaRoute("ready") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model primitive enum and usage schemas")
step("Check primitive schemas")
expect(modelUsageSchemaRoute(8, true)).to_equal(true)
expect(modelUsageSchemaRoute(7, false)).to_equal(false)
expect(apiKeySourceSchemaRoute("temporary")).to_equal(true)
expect(apiKeySourceSchemaRoute("oauth")).to_equal(true)
expect(apiKeySourceSchemaRoute("env")).to_equal(false)
expect(permissionModeSchemaRoute("acceptEdits")).to_equal(true)
expect(permissionModeSchemaRoute("dontAsk")).to_equal(true)
expect(sdkStatusSchemaRoute("compacting")).to_equal(true)
expect(sdkStatusSchemaRoute("null")).to_equal(true)
expect(sdkStatusSchemaRoute("ready")).to_equal(false)
```

</details>

#### should model SDK message envelope variants

- should model SDK message envelope variants
- Check message variants
   - Expected: sdkUserMessageSchemaRoute(false, false, false) is true
   - Expected: sdkUserMessageSchemaRoute(false, true, true) is false
   - Expected: sdkUserMessageSchemaRoute(true, true, true) is true
   - Expected: sdkAssistantMessageSchemaRoute(true, true, true, true) is true
   - Expected: sdkAssistantMessageSchemaRoute(true, false, true, true) is false
   - Expected: sdkResultMessageSchemaRoute("success", true, true, true, false) is true
   - Expected: sdkResultMessageSchemaRoute("success", true, false, true, false) is false
   - Expected: sdkResultMessageSchemaRoute("error", false, false, false, true) is true
   - Expected: sdkMessageSchemaRoute("assistant") is true
   - Expected: sdkMessageSchemaRoute("hook") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model SDK message envelope variants")
step("Check message variants")
expect(sdkUserMessageSchemaRoute(false, false, false)).to_equal(true)
expect(sdkUserMessageSchemaRoute(false, true, true)).to_equal(false)
expect(sdkUserMessageSchemaRoute(true, true, true)).to_equal(true)
expect(sdkAssistantMessageSchemaRoute(true, true, true, true)).to_equal(true)
expect(sdkAssistantMessageSchemaRoute(true, false, true, true)).to_equal(false)
expect(sdkResultMessageSchemaRoute("success", true, true, true, false)).to_equal(true)
expect(sdkResultMessageSchemaRoute("success", true, false, true, false)).to_equal(false)
expect(sdkResultMessageSchemaRoute("error", false, false, false, true)).to_equal(true)
expect(sdkMessageSchemaRoute("assistant")).to_equal(true)
expect(sdkMessageSchemaRoute("hook")).to_equal(false)
```

</details>

#### should model fast mode state schema

- should model fast mode state schema
- Check fast mode states
   - Expected: fastModeStateSchemaRoute("off") is true
   - Expected: fastModeStateSchemaRoute("cooldown") is true
   - Expected: fastModeStateSchemaRoute("on") is true
   - Expected: fastModeStateSchemaRoute("fast") is false
   - Expected: sdkCoreSchemasSourceLinesModeled() equals `1889`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model fast mode state schema")
step("Check fast mode states")
expect(fastModeStateSchemaRoute("off")).to_equal(true)
expect(fastModeStateSchemaRoute("cooldown")).to_equal(true)
expect(fastModeStateSchemaRoute("on")).to_equal(true)
expect(fastModeStateSchemaRoute("fast")).to_equal(false)
expect(sdkCoreSchemasSourceLinesModeled()).to_equal(1889)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `97aa6c6c4bb6f2915367bc69c80726a7c2d1188101009256c45a075d13bb0ec9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97aa6c6c4bb6f2915367bc69c80726a7c2d1188101009256c45a075d13bb0ec9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97aa6c6c4bb6f2915367bc69c80726a7c2d1188101009256c45a075d13bb0ec9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model primitive enum and usage schemas' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model primitive enum and usage schemas' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model SDK message envelope variants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model SDK message envelope variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model fast mode state schema' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/entrypoints/sdk/coreSchemas_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model fast mode state schema' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
