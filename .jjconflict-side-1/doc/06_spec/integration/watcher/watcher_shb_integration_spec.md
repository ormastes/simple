# Watcher Shb Integration Specification

> Tests covering Watcher SHB Integration, fresh SHB cache hit, stale SHB detection, batch processing, dependency invalidation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Watcher Shb Integration Specification

## Scenarios

### Watcher SHB Integration

### fresh SHB cache hit

<details>
<summary>Advanced: skips recompilation for unchanged files</summary>

#### skips recompilation for unchanged files _(slow)_

- skips recompilation for unchanged files
   - Expected: int_compile_log_len() equals `1`
   - Expected: status equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("skips recompilation for unchanged files")
int_reset()
int_add_source("src/main.spl", 12345)
int_compile_shb("src/main.spl")
expect(int_compile_log_len()).to_equal(1)
val status = int_check_freshness("src/main.spl")
expect(status).to_equal(0)
```

</details>


</details>

### stale SHB detection

<details>
<summary>Advanced: detects missing SHB</summary>

#### detects missing SHB _(slow)_

- detects missing SHB
   - Expected: status equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects missing SHB")
int_reset()
int_add_source("src/main.spl", 12345)
val status = int_check_freshness("src/main.spl")
expect(status).to_equal(3)
```

</details>


</details>

### batch processing

<details>
<summary>Advanced: processes multiple files</summary>

#### processes multiple files _(slow)_

- processes multiple files
   - Expected: int_compile_log_len() equals `3`
   - Expected: int_shb_paths_len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("processes multiple files")
int_reset()
int_add_source("src/a.spl", 100)
int_add_source("src/b.spl", 200)
int_add_source("src/c.spl", 300)
int_compile_shb("src/a.spl")
int_compile_shb("src/b.spl")
int_compile_shb("src/c.spl")
expect(int_compile_log_len()).to_equal(3)
expect(int_shb_paths_len()).to_equal(3)
```

</details>


</details>

### dependency invalidation

<details>
<summary>Advanced: detects when dependency interface changes</summary>

#### detects when dependency interface changes _(slow)_

- detects when dependency interface changes
   - Expected: new_dep_hash != dep_hash is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects when dependency interface changes")
int_reset()
int_add_source("src/dep.spl", 100)
int_add_source("src/main.spl", 200)
val dep_hash = int_compile_shb("src/dep.spl")
int_compile_shb("src/main.spl")
int_add_source("src/dep.spl", 999)
val new_dep_hash = int_compile_shb("src/dep.spl")
expect(new_dep_hash != dep_hash).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Active |
| Source | `test/integration/watcher/watcher_shb_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Watcher SHB Integration, fresh SHB cache hit, stale SHB detection, batch processing, dependency invalidation.
- Watcher SHB Integration
- fresh SHB cache hit
- stale SHB detection
- batch processing
- dependency invalidation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
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

- Canonical SPipe generation for source `70b52a1e949c28a4de63aee6be527c5a64d0e794f8a0898f1e9f0681304b4c9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70b52a1e949c28a4de63aee6be527c5a64d0e794f8a0898f1e9f0681304b4c9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70b52a1e949c28a4de63aee6be527c5a64d0e794f8a0898f1e9f0681304b4c9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/watcher/watcher_shb_integration_spec.spl
mirror: doc/06_spec/integration/watcher/watcher_shb_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/watcher/watcher_shb_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/watcher/watcher_shb_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/watcher/watcher_shb_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/watcher/watcher_shb_integration_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips recompilation for unchanged files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/watcher/watcher_shb_integration_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects missing SHB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/watcher/watcher_shb_integration_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'processes multiple files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
