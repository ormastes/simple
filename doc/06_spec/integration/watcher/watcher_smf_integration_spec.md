# Watcher Smf Integration Specification

> Tests covering Watcher SMF Integration, compile and cache, options mismatch detection, recompilation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Watcher Smf Integration Specification

## Scenarios

### Watcher SMF Integration

### compile and cache

<details>
<summary>Advanced: stores options hash in SMF</summary>

#### stores options hash in SMF _(slow)_

- stores options hash in SMF
   - Expected: smf_compile_log_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores options hash in SMF")
smf_int_reset()
smf_int_compile("src/main.spl", "build/smf/main.smf", 99999)
val idx = smf_find("build/smf/main.smf")
expect(idx).to_be_greater_than(-1)
expect(smf_compile_log_len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: verifies matching options</summary>

#### verifies matching options _(slow)_

- verifies matching options
   - Expected: status equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verifies matching options")
smf_int_reset()
smf_int_compile("src/main.spl", "build/smf/main.smf", 99999)
val status = smf_int_check("build/smf/main.smf", 99999)
expect(status).to_equal(0)
```

</details>


</details>

### options mismatch detection

<details>
<summary>Advanced: detects backend change</summary>

#### detects backend change _(slow)_

- detects backend change
   - Expected: status equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects backend change")
smf_int_reset()
smf_int_compile("src/main.spl", "build/smf/main.smf", 11111)
val status = smf_int_check("build/smf/main.smf", 22222)
expect(status).to_equal(2)
```

</details>


</details>

<details>
<summary>Advanced: detects missing SMF</summary>

#### detects missing SMF _(slow)_

- detects missing SMF
   - Expected: status equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects missing SMF")
smf_int_reset()
val status = smf_int_check("build/smf/main.smf", 11111)
expect(status).to_equal(3)
```

</details>


</details>

### recompilation

<details>
<summary>Advanced: recompiles when options change</summary>

#### recompiles when options change _(slow)_

- recompiles when options change
   - Expected: smf_compile_log_len() equals `1`
   - Expected: status equals `2`
   - Expected: smf_compile_log_len() equals `2`
   - Expected: status2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recompiles when options change")
smf_int_reset()
smf_int_compile("src/main.spl", "build/smf/main.smf", 11111)
expect(smf_compile_log_len()).to_equal(1)
val status = smf_int_check("build/smf/main.smf", 22222)
expect(status).to_equal(2)
smf_int_compile("src/main.spl", "build/smf/main.smf", 22222)
expect(smf_compile_log_len()).to_equal(2)
val status2 = smf_int_check("build/smf/main.smf", 22222)
expect(status2).to_equal(0)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Active |
| Source | `test/integration/watcher/watcher_smf_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Watcher SMF Integration, compile and cache, options mismatch detection, recompilation.
- Watcher SMF Integration
- compile and cache
- options mismatch detection
- recompilation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f8b70fa1b1488aeff0424236b67b54cc17df6ca89093e5dea52008fdfef7ee8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8b70fa1b1488aeff0424236b67b54cc17df6ca89093e5dea52008fdfef7ee8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8b70fa1b1488aeff0424236b67b54cc17df6ca89093e5dea52008fdfef7ee8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/watcher/watcher_smf_integration_spec.spl
mirror: doc/06_spec/integration/watcher/watcher_smf_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/watcher/watcher_smf_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/watcher/watcher_smf_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/watcher/watcher_smf_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/watcher/watcher_smf_integration_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores options hash in SMF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/watcher/watcher_smf_integration_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies matching options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/watcher/watcher_smf_integration_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects backend change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
