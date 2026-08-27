# Claude Full permission denial tracking

> Pure Simple coverage for permission classifier denial counters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full permission denial tracking

Pure Simple coverage for permission classifier denial counters.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for permission classifier denial counters.

## Scenarios

### Claude full permission denial tracking

#### starts with zero counters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with zero counters
- Check initial state
   - Expected: state.consecutiveDenials equals `0`
   - Expected: state.totalDenials equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts with zero counters")
step("Check initial state")
val state = createDenialTrackingState()
expect(state.consecutiveDenials).to_equal(0)
expect(state.totalDenials).to_equal(0)
```

</details>

#### records denials by incrementing both counters

- records denials by incrementing both counters
- Check denial increment
   - Expected: state.consecutiveDenials equals `1`
   - Expected: state.totalDenials equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records denials by incrementing both counters")
step("Check denial increment")
val state = recordDenial(createDenialTrackingState())
expect(state.consecutiveDenials).to_equal(1)
expect(state.totalDenials).to_equal(1)
```

</details>

#### records success by resetting consecutive denials only

- records success by resetting consecutive denials only
- Check success reset
   - Expected: reset.consecutiveDenials equals `0`
   - Expected: reset.totalDenials equals `5`
   - Expected: unchanged.consecutiveDenials equals `0`
   - Expected: unchanged.totalDenials equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records success by resetting consecutive denials only")
step("Check success reset")
val denied = DenialTrackingState.new(2, 5)
val reset = recordSuccess(denied)
expect(reset.consecutiveDenials).to_equal(0)
expect(reset.totalDenials).to_equal(5)

val unchanged = recordSuccess(DenialTrackingState.new(0, 5))
expect(unchanged.consecutiveDenials).to_equal(0)
expect(unchanged.totalDenials).to_equal(5)
```

</details>

#### falls back when denial limits are reached

- falls back when denial limits are reached
- Check fallback limits
   - Expected: denialMaxConsecutive() equals `3`
   - Expected: denialMaxTotal() equals `20`
   - Expected: shouldFallbackToPrompting(DenialTrackingState.new(2, 19)) is false
   - Expected: shouldFallbackToPrompting(DenialTrackingState.new(3, 0)) is true
   - Expected: shouldFallbackToPrompting(DenialTrackingState.new(0, 20)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls back when denial limits are reached")
step("Check fallback limits")
expect(denialMaxConsecutive()).to_equal(3)
expect(denialMaxTotal()).to_equal(20)
expect(shouldFallbackToPrompting(DenialTrackingState.new(2, 19))).to_equal(false)
expect(shouldFallbackToPrompting(DenialTrackingState.new(3, 0))).to_equal(true)
expect(shouldFallbackToPrompting(DenialTrackingState.new(0, 20))).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `317353f63689cdcfcab0497309bfdc501e4edd2f350341d788fc039f559a2b34`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `317353f63689cdcfcab0497309bfdc501e4edd2f350341d788fc039f559a2b34`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `317353f63689cdcfcab0497309bfdc501e4edd2f350341d788fc039f559a2b34`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with zero counters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records denials by incrementing both counters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/permissions/denialTracking_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records success by resetting consecutive denials only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
