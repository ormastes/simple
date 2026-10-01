# Claude Full env validation

> Pure Simple coverage for bounded integer env parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full env validation

Pure Simple coverage for bounded integer env parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/env_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for bounded integer env parsing.

## Scenarios

### Claude full env validation

#### uses the default when the env value is absent or empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the default when the env value is absent or empty
- Check absent and empty values
   - Expected: validateBoundedIntEnvVar("TEST_LIMIT", nil, 8, 20).effective equals `8`
   - Expected: validateBoundedIntEnvVar("TEST_LIMIT", nil, 8, 20).status equals `valid`
   - Expected: validateBoundedIntEnvVar("TEST_LIMIT", Some(""), 8, 20).effective equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses the default when the env value is absent or empty")
step("Check absent and empty values")
expect(validateBoundedIntEnvVar("TEST_LIMIT", nil, 8, 20).effective).to_equal(8)
expect(validateBoundedIntEnvVar("TEST_LIMIT", nil, 8, 20).status).to_equal("valid")
expect(validateBoundedIntEnvVar("TEST_LIMIT", Some(""), 8, 20).effective).to_equal(8)
expect(validateBoundedIntEnvVar("TEST_LIMIT", Some(""), 8, 20).message).to_be_nil()
expect(validateBoundedIntEnvVar("TEST_LIMIT", Some(""), 8, 20).debugMessage).to_be_nil()
```

</details>

#### accepts positive integer prefixes

- accepts positive integer prefixes
- Check parseInt-style prefix parsing
   - Expected: clean.effective equals `12`
   - Expected: clean.status equals `valid`
   - Expected: prefixed.effective equals `15`
   - Expected: prefixed.status equals `valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts positive integer prefixes")
step("Check parseInt-style prefix parsing")
val clean = validateBoundedIntEnvVar("TEST_LIMIT", Some("12"), 8, 20)
expect(clean.effective).to_equal(12)
expect(clean.status).to_equal("valid")
expect(clean.message).to_be_nil()

val prefixed = validateBoundedIntEnvVar("TEST_LIMIT", Some("  +15ms"), 8, 20)
expect(prefixed.effective).to_equal(15)
expect(prefixed.status).to_equal("valid")
```

</details>

#### rejects invalid and non-positive values

- rejects invalid and non-positive values
- Check invalid fallback
   - Expected: invalid.effective equals `8`
   - Expected: invalid.status equals `invalid`
   - Expected: invalid.message equals `Some("Invalid value "abc" (using default: 8)")`
   - Expected: invalid.debugMessage equals `Some("TEST_LIMIT Invalid value "abc" (using default: 8)")`
   - Expected: zero.effective equals `8`
   - Expected: zero.status equals `invalid`
   - Expected: negative.effective equals `8`
   - Expected: negative.status equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid and non-positive values")
step("Check invalid fallback")
val invalid = validateBoundedIntEnvVar("TEST_LIMIT", Some("abc"), 8, 20)
expect(invalid.effective).to_equal(8)
expect(invalid.status).to_equal("invalid")
expect(invalid.message).to_equal(Some("Invalid value \"abc\" (using default: 8)"))
expect(invalid.debugMessage).to_equal(Some("TEST_LIMIT Invalid value \"abc\" (using default: 8)"))

val zero = validateBoundedIntEnvVar("TEST_LIMIT", Some("0"), 8, 20)
expect(zero.effective).to_equal(8)
expect(zero.status).to_equal("invalid")

val negative = validateBoundedIntEnvVar("TEST_LIMIT", Some("-4"), 8, 20)
expect(negative.effective).to_equal(8)
expect(negative.status).to_equal("invalid")
```

</details>

#### caps values above the upper limit

- caps values above the upper limit
- Check capping
   - Expected: capped.effective equals `20`
   - Expected: capped.status equals `capped`
   - Expected: capped.message equals `Some("Capped from 40 to 20")`
   - Expected: capped.debugMessage equals `Some("TEST_LIMIT Capped from 40 to 20")`
   - Expected: huge.effective equals `20`
   - Expected: huge.status equals `capped`
   - Expected: huge.message equals `Some("Capped from 1e+21 to 20")`
   - Expected: belowScientific.message equals `Some("Capped from 100000000000000000000 to 20")`
   - Expected: roundedBelowScientific.message equals `Some("Capped from 150000000000000000000 to 20")`
   - Expected: maxI64Overflow.message equals `Some("Capped from 9223372036854776000 to 20")`
   - Expected: sameDoubleBucket.message equals `Some("Capped from 9223372036854776000 to 20")`
   - Expected: u64Max.message equals `Some("Capped from 18446744073709552000 to 20")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("caps values above the upper limit")
step("Check capping")
val capped = validateBoundedIntEnvVar("TEST_LIMIT", Some("40"), 8, 20)
expect(capped.effective).to_equal(20)
expect(capped.status).to_equal("capped")
expect(capped.message).to_equal(Some("Capped from 40 to 20"))
expect(capped.debugMessage).to_equal(Some("TEST_LIMIT Capped from 40 to 20"))

val huge = validateBoundedIntEnvVar("TEST_LIMIT", Some("999999999999999999999"), 8, 20)
expect(huge.effective).to_equal(20)
expect(huge.status).to_equal("capped")
expect(huge.message).to_equal(Some("Capped from 1e+21 to 20"))

val belowScientific = validateBoundedIntEnvVar("TEST_LIMIT", Some("100000000000000000000"), 8, 20)
expect(belowScientific.message).to_equal(Some("Capped from 100000000000000000000 to 20"))

val roundedBelowScientific = validateBoundedIntEnvVar("TEST_LIMIT", Some("149999999999999999999"), 8, 20)
expect(roundedBelowScientific.message).to_equal(Some("Capped from 150000000000000000000 to 20"))

val maxI64Overflow = validateBoundedIntEnvVar("TEST_LIMIT", Some("9223372036854775808"), 8, 20)
expect(maxI64Overflow.message).to_equal(Some("Capped from 9223372036854776000 to 20"))

val sameDoubleBucket = validateBoundedIntEnvVar("TEST_LIMIT", Some("9223372036854776808"), 8, 20)
expect(sameDoubleBucket.message).to_equal(Some("Capped from 9223372036854776000 to 20"))

val u64Max = validateBoundedIntEnvVar("TEST_LIMIT", Some("18446744073709551615"), 8, 20)
expect(u64Max.message).to_equal(Some("Capped from 18446744073709552000 to 20"))
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

- Canonical SPipe generation for source `c3f8a6f737b7b097692f68011ba5e351cc388c71c250e2a51722f4d200e86c8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3f8a6f737b7b097692f68011ba5e351cc388c71c250e2a51722f4d200e86c8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3f8a6f737b7b097692f68011ba5e351cc388c71c250e2a51722f4d200e86c8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/env_validation_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/env_validation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/env_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/env_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/env_validation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/env_validation_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the default when the env value is absent or empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/env_validation_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts positive integer prefixes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/env_validation_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid and non-positive values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
