# Claude Full UUID utils

> Pure Simple coverage for UUID validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full UUID utils

Pure Simple coverage for UUID validation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/uuid_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for UUID validation.

## Scenarios

### Claude full UUID utils

#### accepts lower and upper case UUIDs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts lower and upper case UUIDs
- Check valid UUIDs
   - Expected: validateUuid(UuidCandidate.textValue("550e8400-e29b-41d4-a716-446655440000")) equals `Some("550e8400-e29b-41d4-a716-446655440000")`
   - Expected: validateUuid(UuidCandidate.textValue("550E8400-E29B-41D4-A716-446655440000")) equals `Some("550E8400-E29B-41D4-A716-446655440000")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts lower and upper case UUIDs")
step("Check valid UUIDs")
expect(validateUuid(UuidCandidate.textValue("550e8400-e29b-41d4-a716-446655440000"))).to_equal(Some("550e8400-e29b-41d4-a716-446655440000"))
expect(validateUuid(UuidCandidate.textValue("550E8400-E29B-41D4-A716-446655440000"))).to_equal(Some("550E8400-E29B-41D4-A716-446655440000"))
```

</details>

#### rejects malformed lengths and separators

- rejects malformed lengths and separators
- Check shape failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects malformed lengths and separators")
step("Check shape failures")
expect(validateUuid(UuidCandidate.textValue("550e8400e29b41d4a716446655440000"))).to_be_nil()
expect(validateUuid(UuidCandidate.textValue("550e8400_e29b-41d4-a716-446655440000"))).to_be_nil()
expect(validateUuid(UuidCandidate.textValue("550e8400-e29b-41d4-a716-4466554400000"))).to_be_nil()
```

</details>

#### rejects non-hex characters

- rejects non-hex characters
- Check hex failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects non-hex characters")
step("Check hex failures")
expect(validateUuid(UuidCandidate.textValue("550e8400-e29b-41d4-a716-44665544000g"))).to_be_nil()
expect(validateUuid(UuidCandidate.textValue("zzzzzzzz-e29b-41d4-a716-446655440000"))).to_be_nil()
```

</details>

#### rejects non-text values

- rejects non-text values
- Check unknown input guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects non-text values")
step("Check unknown input guard")
expect(validateUuid(UuidCandidate.nonText("nil"))).to_be_nil()
expect(validateUuid(UuidCandidate.nonText("number"))).to_be_nil()
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

- Canonical SPipe generation for source `e9dcb638dfabcbcb6f177554cb32068644e572c712f81c94feaf16079b20172c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9dcb638dfabcbcb6f177554cb32068644e572c712f81c94feaf16079b20172c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9dcb638dfabcbcb6f177554cb32068644e572c712f81c94feaf16079b20172c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/uuid_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/uuid_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/uuid_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/uuid_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/uuid_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts lower and upper case UUIDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/uuid_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed lengths and separators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/uuid_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-hex characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
