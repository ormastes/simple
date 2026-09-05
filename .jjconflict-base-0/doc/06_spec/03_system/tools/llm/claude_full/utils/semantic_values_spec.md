# Claude Full semantic values

> Pure Simple coverage for semantic boolean and number preprocessing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full semantic values

Pure Simple coverage for semantic boolean and number preprocessing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/semantic_values_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for semantic boolean and number preprocessing.

## Scenarios

### Claude full semantic values

#### coerces only literal boolean strings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- coerces only literal boolean strings
- Check semantic boolean preprocessing
   - Expected: semanticBoolean(SemanticValue.textValue("true")).boolValue is true
   - Expected: falseValue.kind equals `bool`
   - Expected: falseValue.boolValue is false
   - Expected: semanticBoolean(SemanticValue.textValue("TRUE")).kind equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("coerces only literal boolean strings")
step("Check semantic boolean preprocessing")
expect(semanticBoolean(SemanticValue.textValue("true")).boolValue).to_equal(true)
val falseValue = semanticBoolean(SemanticValue.textValue("false"))
expect(falseValue.kind).to_equal("bool")
expect(falseValue.boolValue).to_equal(false)
expect(semanticBoolean(SemanticValue.textValue("TRUE")).kind).to_equal("text")
```

</details>

#### leaves non-string boolean inputs unchanged

- leaves non-string boolean inputs unchanged
- Check bool pass-through
   - Expected: processed.kind equals `bool`
   - Expected: processed.boolValue is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves non-string boolean inputs unchanged")
step("Check bool pass-through")
val original = SemanticValue.boolValue(false)
val processed = semanticBoolean(original)
expect(processed.kind).to_equal("bool")
expect(processed.boolValue).to_equal(false)
```

</details>

#### coerces valid decimal number strings

- coerces valid decimal number strings
- Check semantic number preprocessing
   - Expected: semanticNumber(SemanticValue.textValue("30")).numberValue equals `30.0`
   - Expected: semanticNumber(SemanticValue.textValue("-5")).numberValue equals `-5.0`
   - Expected: semanticNumber(SemanticValue.textValue("3.14")).numberValue equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("coerces valid decimal number strings")
step("Check semantic number preprocessing")
expect(semanticNumber(SemanticValue.textValue("30")).numberValue).to_equal(30.0)
expect(semanticNumber(SemanticValue.textValue("-5")).numberValue).to_equal(-5.0)
expect(semanticNumber(SemanticValue.textValue("3.14")).numberValue).to_equal(3.14)
```

</details>

#### leaves invalid number strings unchanged

- leaves invalid number strings unchanged
- Check invalid number pass-through
   - Expected: semanticNumber(SemanticValue.textValue("")).kind equals `text`
   - Expected: semanticNumber(SemanticValue.textValue("3.")).kind equals `text`
   - Expected: semanticNumber(SemanticValue.textValue("3.1.4")).kind equals `text`
   - Expected: semanticNumber(SemanticValue.nilValue()).kind equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves invalid number strings unchanged")
step("Check invalid number pass-through")
expect(semanticNumber(SemanticValue.textValue("")).kind).to_equal("text")
expect(semanticNumber(SemanticValue.textValue("3.")).kind).to_equal("text")
expect(semanticNumber(SemanticValue.textValue("3.1.4")).kind).to_equal("text")
expect(semanticNumber(SemanticValue.nilValue()).kind).to_equal("nil")
```

</details>

#### leaves overflow-sized decimal strings unchanged

- leaves overflow-sized decimal strings unchanged
- Check finite number guard
   - Expected: semanticNumber(SemanticValue.textValue(tooLarge)).kind equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves overflow-sized decimal strings unchanged")
step("Check finite number guard")
val tooLarge = "9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"
expect(semanticNumber(SemanticValue.textValue(tooLarge)).kind).to_equal("text")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37174b6dcca22641a4fd7d64f0fc1c502c9ea4bfcdf0edd6b6a16a6023dd06f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37174b6dcca22641a4fd7d64f0fc1c502c9ea4bfcdf0edd6b6a16a6023dd06f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37174b6dcca22641a4fd7d64f0fc1c502c9ea4bfcdf0edd6b6a16a6023dd06f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/semantic_values_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/semantic_values_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/semantic_values_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/semantic_values_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/semantic_values_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/semantic_values_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'coerces only literal boolean strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/semantic_values_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves non-string boolean inputs unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/semantic_values_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'coerces valid decimal number strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
