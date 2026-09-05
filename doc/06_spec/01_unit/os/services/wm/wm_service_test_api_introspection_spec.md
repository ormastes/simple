# Wm Service Test Api Introspection Specification

> Tests covering WmService COMP_TEST_API_REQ introspection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Service Test Api Introspection Specification

## Scenarios

### WmService COMP_TEST_API_REQ introspection

#### replies with the live owned-window count, not STATUS_INVALID

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- replies with the live owned-window count, not STATUS_INVALID
   - Expected: action.kind equals `test_api`
   - Expected: action.x equals `2`
   - Expected: action.width equals `2`
   - Expected: action.src_port equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("replies with the live owned-window count, not STATUS_INVALID")
val wm = WmService.new()
wm.register_window_owner_with_identity(WindowId(value: 11), 40, 1234, "app.a")
wm.register_window_owner_with_identity(WindowId(value: 22), 41, 5678, "app.b")
val action = wm.parse_test_api_req(41, 0, 0)
expect(action.kind).to_equal("test_api")
expect(action.x).to_equal(2)
expect(action.width).to_equal(2)
expect(action.src_port).to_equal(41)
```

</details>

#### reports zero windows for a fresh service with no ownership

- reports zero windows for a fresh service with no ownership
   - Expected: action.kind equals `test_api`
   - Expected: action.x equals `0`
   - Expected: action.y equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports zero windows for a fresh service with no ownership")
val wm = WmService.new()
val action = wm.parse_test_api_req(7, 0, 0)
expect(action.kind).to_equal("test_api")
expect(action.x).to_equal(0)
expect(action.y).to_equal(0)
```

</details>

#### tracks the owned-window count as windows register and unregister

- tracks the owned-window count as windows register and unregister
   - Expected: after_one.x equals `1`
   - Expected: after_remove.x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("tracks the owned-window count as windows register and unregister")
val wm = WmService.new()
wm.register_window_owner_with_identity(WindowId(value: 100), 50, 9000, "app.c")
val after_one = wm.parse_test_api_req(50, 0, 0)
expect(after_one.x).to_equal(1)
wm.remove_owner(100)
val after_remove = wm.parse_test_api_req(50, 0, 0)
expect(after_remove.x).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/wm/wm_service_test_api_introspection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WmService COMP_TEST_API_REQ introspection.
- WmService COMP_TEST_API_REQ introspection

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `880ead988d442fcae299645cd419adc8f9b7f6b112e88a1175c7466f884d6f67`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `880ead988d442fcae299645cd419adc8f9b7f6b112e88a1175c7466f884d6f67`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `880ead988d442fcae299645cd419adc8f9b7f6b112e88a1175c7466f884d6f67`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/services/wm/wm_service_test_api_introspection_spec.spl
mirror: doc/06_spec/01_unit/os/services/wm/wm_service_test_api_introspection_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/wm/wm_service_test_api_introspection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/wm/wm_service_test_api_introspection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/wm/wm_service_test_api_introspection_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/wm/wm_service_test_api_introspection_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replies with the live owned-window count, not STATUS_INVALID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/wm/wm_service_test_api_introspection_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports zero windows for a fresh service with no ownership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/wm/wm_service_test_api_introspection_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks the owned-window count as windows register and unregister' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
