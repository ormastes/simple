# Log Policy Specification

> Tests covering baremetal log policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Policy Specification

## Scenarios

### baremetal log policy

#### defaults compile logging to debug and runtime logging to info

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults compile logging to debug and runtime logging to info
   - Expected: policy.compile_level equals `1`
   - Expected: policy.runtime_level equals `2`
   - Expected: baremetal_compile_log_allows(policy, 1) is true
   - Expected: baremetal_runtime_log_allows(policy, 1) is false
   - Expected: baremetal_runtime_log_allows(policy, 3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults compile logging to debug and runtime logging to info")
val policy = BaremetalLogPolicy.default_debug()
expect(policy.compile_level).to_equal(1)
expect(policy.runtime_level).to_equal(2)
expect(baremetal_compile_log_allows(policy, 1)).to_equal(true)
expect(baremetal_runtime_log_allows(policy, 1)).to_equal(false)
expect(baremetal_runtime_log_allows(policy, 3)).to_equal(true)
```

</details>

#### keeps AOP call and assignment logging independently switchable

- keeps AOP call and assignment logging independently switchable
   - Expected: baremetal_aop_function_calls_enabled(policy) is true
   - Expected: baremetal_aop_variable_assignments_enabled(policy) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps AOP call and assignment logging independently switchable")
val policy = BaremetalLogPolicy.with_aop(true, false)
expect(baremetal_aop_function_calls_enabled(policy)).to_equal(true)
expect(baremetal_aop_variable_assignments_enabled(policy)).to_equal(false)
```

</details>

#### honors compile-time off for AOP logging

- honors compile-time off for AOP logging
   - Expected: baremetal_aop_function_calls_enabled(policy) is false
   - Expected: baremetal_aop_variable_assignments_enabled(policy) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("honors compile-time off for AOP logging")
val policy = baremetal_log_policy_with_compile_level(BaremetalLogPolicy.with_aop(true, true), 5)
expect(baremetal_aop_function_calls_enabled(policy)).to_equal(false)
expect(baremetal_aop_variable_assignments_enabled(policy)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/os/baremetal/feature/log_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering baremetal log policy.
- baremetal log policy

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

- Canonical SPipe generation for source `e9d197a39343eedf6e3bc8b0f5e3b1e5389310cd2c3832de6df7dd44b527fdc1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9d197a39343eedf6e3bc8b0f5e3b1e5389310cd2c3832de6df7dd44b527fdc1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9d197a39343eedf6e3bc8b0f5e3b1e5389310cd2c3832de6df7dd44b527fdc1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/baremetal/feature/log_policy_spec.spl
mirror: doc/06_spec/03_system/os/baremetal/feature/log_policy_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/baremetal/feature/log_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/baremetal/feature/log_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/baremetal/feature/log_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/baremetal/feature/log_policy_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults compile logging to debug and runtime logging to info' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/baremetal/feature/log_policy_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps AOP call and assignment logging independently switchable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/baremetal/feature/log_policy_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'honors compile-time off for AOP logging' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
