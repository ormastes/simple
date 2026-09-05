# Mem Extern Parity Specification

> Tests covering memory introspection extern parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mem Extern Parity Specification

## Scenarios

### memory introspection extern parity

#### rt_mem_profile_abi_version is callable and returns the current ABI version

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_mem_profile_abi_version is callable and returns the current ABI version
   - Expected: v equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_mem_profile_abi_version is callable and returns the current ABI version")
val v = rt_mem_profile_abi_version()
expect(v).to_equal(1)
```

</details>

#### rt_mem_profile_features is callable and returns a non-negative bitmask

- rt_mem_profile_features is callable and returns a non-negative bitmask
   - Expected: f >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_mem_profile_features is callable and returns a non-negative bitmask")
val f = rt_mem_profile_features()
expect(f >= 0).to_equal(true)
```

</details>

#### rt_mem_attr_enabled is callable and returns 0 or 1

- rt_mem_attr_enabled is callable and returns 0 or 1
   - Expected: e == 0 or e == 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_mem_attr_enabled is callable and returns 0 or 1")
val e = rt_mem_attr_enabled()
expect(e == 0 or e == 1).to_equal(true)
```

</details>

#### rt_mem_guard_stats is callable and returns a non-negative sampled count

- rt_mem_guard_stats is callable and returns a non-negative sampled count
   - Expected: g >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_mem_guard_stats is callable and returns a non-negative sampled count")
val g = rt_mem_guard_stats()
expect(g >= 0).to_equal(true)
```

</details>

#### rt_mem_harden_check is callable and returns a non-negative tamper count

- rt_mem_harden_check is callable and returns a non-negative tamper count
   - Expected: h >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_mem_harden_check is callable and returns a non-negative tamper count")
val h = rt_mem_harden_check()
expect(h >= 0).to_equal(true)
```

</details>

#### rt_mem_attr_set_owner is callable with a text owner label and does not crash

- rt_mem_attr_set_owner is callable with a text owner label and does not crash
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_mem_attr_set_owner is callable with a text owner label and does not crash")
rt_mem_attr_set_owner("mem_extern_parity_spec")
expect(true).to_equal(true)
```

</details>

#### rt_mem_attr_report_print is callable and does not crash

- rt_mem_attr_report_print is callable and does not crash
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_mem_attr_report_print is callable and does not crash")
rt_mem_attr_report_print(4)
expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/mem_extern_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering memory introspection extern parity.
- memory introspection extern parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb7bc937b3a7444e21951df4b06286b366b246de2006a92935aa77df59fc029d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb7bc937b3a7444e21951df4b06286b366b246de2006a92935aa77df59fc029d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb7bc937b3a7444e21951df4b06286b366b246de2006a92935aa77df59fc029d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/runtime/mem_extern_parity_spec.spl
mirror: doc/06_spec/01_unit/runtime/mem_extern_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/mem_extern_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/mem_extern_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/mem_extern_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/runtime/mem_extern_parity_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_mem_profile_abi_version is callable and returns the current ABI version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/mem_extern_parity_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_mem_profile_features is callable and returns a non-negative bitmask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/mem_extern_parity_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_mem_attr_enabled is callable and returns 0 or 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
