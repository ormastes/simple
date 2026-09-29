# Claude Full Ripgrep And Slow Operations

> Focused parity checks for `RipgrepTimeoutError` and `AntSlowLogger`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ripgrep And Slow Operations

Focused parity checks for `RipgrepTimeoutError` and `AntSlowLogger`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused parity checks for `RipgrepTimeoutError` and `AntSlowLogger`.

## Scenarios

### Claude full ripgrep and slow operations

#### preserves ripgrep timeout partial results

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves ripgrep timeout partial results
- Create the custom timeout error and inspect TS-compatible fields
   - Expected: err.name equals `RipgrepTimeoutError`
   - Expected: err.message equals `rg timed out`
   - Expected: err.partialResults equals `["one", "two"]`
   - Expected: isEagainError("spawn failed: os error 11") is true
   - Expected: isEagainError("Resource temporarily unavailable") is true
   - Expected: stripCR("a\r\nb") equals `a\nb`
   - Expected: ripgrepSourceLinesModeled() equals `679`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves ripgrep timeout partial results")
step("Create the custom timeout error and inspect TS-compatible fields")
val err = RipgrepTimeoutError.new("rg timed out", ["one", "two"])

expect(err.name).to_equal("RipgrepTimeoutError")
expect(err.message).to_equal("rg timed out")
expect(err.partialResults).to_equal(["one", "two"])
expect(isEagainError("spawn failed: os error 11")).to_equal(true)
expect(isEagainError("Resource temporarily unavailable")).to_equal(true)
expect(stripCR("a\r\nb")).to_equal("a\nb")
expect(ripgrepSourceLinesModeled()).to_equal(679)
```

</details>

#### logs ant slow operations only above threshold

- logs ant slow operations only above threshold
- Build a lazy template description after the operation crosses the threshold
   - Expected: logger.dispose(110.0) is false
   - Expected: logger.loggedOperations.len() equals `0`
   - Expected: logger.dispose(125.5) is true
   - Expected: logger.loggedOperations.len() equals `1`
   - Expected: logger.lastDurationMs() equals `25.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logs ant slow operations only above threshold")
step("Build a lazy template description after the operation crosses the threshold")
val logger = slowLoggingAnt(
    100.0,
    ["JSON.stringify(", ", ", ")"],
    [TemplateValue.object(2), TemplateValue.array(3)],
    "Error\n    at slowOperations.ts:101:1\n    at caller.ts:42:7",
    20.0,
)

expect(logger.dispose(110.0)).to_equal(false)
expect(logger.loggedOperations.len()).to_equal(0)
expect(logger.dispose(125.5)).to_equal(true)
expect(logger.loggedOperations.len()).to_equal(1)
expect(logger.lastDescription()).to_contain("JSON.stringify(Object{2 keys}, Array[3])")
expect(logger.lastDescription()).to_contain("caller.ts:42:7")
expect(logger.lastDurationMs()).to_equal(25.5)
```

</details>

#### keeps threshold and external logger behavior simple

- keeps threshold and external logger behavior simple
- Resolve thresholds and verify external mode does not record a slow operation
   - Expected: slowOperationThresholdMs("5", "production", "external") equals `5.0`
   - Expected: slowOperationThresholdMs("-1", "development", "external") equals `20.0`
   - Expected: slowOperationThresholdMs("", "production", "ant") equals `300.0`
   - Expected: renderTemplateValue(TemplateValue.string("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz")) equals `abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxy... (full value in folded executable source)`
   - Expected: noop.dispose(999.0) is false
   - Expected: noop.disposed is true
   - Expected: slowOperationsSourceLinesModeled() equals `286`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps threshold and external logger behavior simple")
step("Resolve thresholds and verify external mode does not record a slow operation")
expect(slowOperationThresholdMs("5", "production", "external")).to_equal(5.0)
expect(slowOperationThresholdMs("-1", "development", "external")).to_equal(20.0)
expect(slowOperationThresholdMs("", "production", "ant")).to_equal(300.0)
expect(renderTemplateValue(TemplateValue.string("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"))).to_equal("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzab...")
val noop = slowLoggingExternal()
expect(noop.dispose(999.0)).to_equal(false)
expect(noop.disposed).to_equal(true)
expect(slowOperationsSourceLinesModeled()).to_equal(286)
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

- Canonical SPipe generation for source `cb763560797b565e37e552cd6eca5439cc99e2237a500c536f309d75fb86f9cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb763560797b565e37e552cd6eca5439cc99e2237a500c536f309d75fb86f9cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb763560797b565e37e552cd6eca5439cc99e2237a500c536f309d75fb86f9cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves ripgrep timeout partial results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'logs ant slow operations only above threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps threshold and external logger behavior simple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
