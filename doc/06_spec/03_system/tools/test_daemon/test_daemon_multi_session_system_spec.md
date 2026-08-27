# Test Daemon Multi Session System Specification

> Tests covering Multi-session coordination portable smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Daemon Multi Session System Specification

## Scenarios

### Multi-session coordination portable smoke

#### keeps session kinds distinct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps session kinds distinct
   - Expected: qemu_kind equals `qemu`
   - Expected: container_kind equals `container`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps session kinds distinct")
val qemu_kind = "qemu"
val container_kind = "container"
expect(qemu_kind).to_equal("qemu")
expect(container_kind).to_equal("container")
```

</details>

#### records reuse policies

- records reuse policies


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records reuse policies")
val shared_read_only = "shared_read_only"
val fresh_per_test = "fresh_per_test"
expect(shared_read_only).to_contain("shared")
expect(fresh_per_test).to_contain("fresh")
```

</details>

#### records multi-architecture keys

- records multi-architecture keys
   - Expected: targets.len() equals `3`
   - Expected: targets[1] equals `riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records multi-architecture keys")
val targets = ["arm64", "riscv64", "x86_64"]
expect(targets.len()).to_equal(3)
expect(targets[1]).to_equal("riscv64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Multi-session coordination portable smoke.
- Multi-session coordination portable smoke

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

- Canonical SPipe generation for source `195761583ff78d067ab85da6e6f111839996ca1b5e9883f0054ea39ab7fab11f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `195761583ff78d067ab85da6e6f111839996ca1b5e9883f0054ea39ab7fab11f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `195761583ff78d067ab85da6e6f111839996ca1b5e9883f0054ea39ab7fab11f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl
mirror: doc/06_spec/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps session kinds distinct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records reuse policies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records multi-architecture keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
