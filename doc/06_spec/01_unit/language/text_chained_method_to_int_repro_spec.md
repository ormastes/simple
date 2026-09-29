# Text Chained Method To Int Repro Specification

> Tests covering chained text method to numeric conversion (interpreter).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Chained Method To Int Repro Specification

## Scenarios

### chained text method to numeric conversion (interpreter)

#### parses a trimmed text chained directly into to_i64()

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a trimmed text chained directly into to_i64()
   - Expected: chained equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("parses a trimmed text chained directly into to_i64()")
val s: text = "  42  "
val chained = s.trim().to_i64() ?? -1
expect(chained).to_equal(42)
```

</details>

#### parses a substring chained directly into to_int()

- parses a substring chained directly into to_int()
   - Expected: chained equals `800`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("parses a substring chained directly into to_int()")
val arg: text = "--timeout=800"
val chained = arg.substring(10).to_int() ?? -1
expect(chained).to_equal(800)
```

</details>

#### matches the split (intermediate val) form for both cases

- matches the split (intermediate val) form for both cases
   - Expected: t.to_i64() ?? -1 equals `s.trim().to_i64() ?? -1`
   - Expected: sub.to_int() ?? -1 equals `arg.substring(10).to_int() ?? -1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("matches the split (intermediate val) form for both cases")
val s: text = "  42  "
val t = s.trim()
expect(t.to_i64() ?? -1).to_equal(s.trim().to_i64() ?? -1)

val arg: text = "--timeout=800"
val sub = arg.substring(10)
expect(sub.to_int() ?? -1).to_equal(arg.substring(10).to_int() ?? -1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/text_chained_method_to_int_repro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering chained text method to numeric conversion (interpreter).
- chained text method to numeric conversion (interpreter)

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

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a7c170f4b47d38ca2da1802d223c8d0358ac53a7f7dedb5f852776bc77b4395a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7c170f4b47d38ca2da1802d223c8d0358ac53a7f7dedb5f852776bc77b4395a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7c170f4b47d38ca2da1802d223c8d0358ac53a7f7dedb5f852776bc77b4395a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/language/text_chained_method_to_int_repro_spec.spl
mirror: doc/06_spec/01_unit/language/text_chained_method_to_int_repro_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/text_chained_method_to_int_repro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/text_chained_method_to_int_repro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/text_chained_method_to_int_repro_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/text_chained_method_to_int_repro_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a trimmed text chained directly into to_i64()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/text_chained_method_to_int_repro_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a substring chained directly into to_int()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/text_chained_method_to_int_repro_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the split (intermediate val) form for both cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
