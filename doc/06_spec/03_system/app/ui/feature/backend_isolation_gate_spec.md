# Backend Isolation Gate Specification

> Tests covering UI backend-isolation enforcement gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Isolation Gate Specification

## Scenarios

### UI backend-isolation enforcement gate

#### has a gate script

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has a gate script
   - Expected: file_exists("scripts/check/check-ui-backend-isolation.shs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a gate script")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(file_exists("scripts/check/check-ui-backend-isolation.shs")).to_equal(true)
```

</details>

#### scans the app/example/UI-tier roots for rt_* and backend-class violations

- scans the app/example/UI-tier roots for rt_* and backend-class violations
   - Expected: source contains `rt_[a-z0-9_]+`
   - Expected: source contains `MetalBackend|VulkanBackend|DirectXBackend|SoftwareBackend`
   - Expected: source contains `src/app examples src/lib/*/ui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scans the app/example/UI-tier roots for rt_* and backend-class violations")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = read_file("scripts/check/check-ui-backend-isolation.shs")
expect(source.contains("rt_[a-z0-9_]+")).to_equal(true)
expect(source.contains("MetalBackend|VulkanBackend|DirectXBackend|SoftwareBackend")).to_equal(true)
expect(source.contains("src/app examples src/lib/*/ui")).to_equal(true)
```

</details>

#### excludes the allowlisted backend-implementation directories

- excludes the allowlisted backend-implementation directories
   - Expected: source contains `src/app/interpreter/ffi/**`
   - Expected: source contains `src/lib/nogc_sync_mut/ui/**`
   - Expected: source contains `vendor/**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes the allowlisted backend-implementation directories")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = read_file("scripts/check/check-ui-backend-isolation.shs")
expect(source.contains("src/app/interpreter/ffi/**")).to_equal(true)
expect(source.contains("src/lib/nogc_sync_mut/ui/**")).to_equal(true)
expect(source.contains("vendor/**")).to_equal(true)
```

</details>

#### supports a baseline ratchet with an update flag

- supports a baseline ratchet with an update flag
   - Expected: source contains `ui_backend_isolation_baseline.txt`
   - Expected: source contains `--update-baseline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports a baseline ratchet with an update flag")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = read_file("scripts/check/check-ui-backend-isolation.shs")
expect(source.contains("ui_backend_isolation_baseline.txt")).to_equal(true)
expect(source.contains("--update-baseline")).to_equal(true)
```

</details>

#### supports a --scan-dir override for isolated testing

- supports a --scan-dir override for isolated testing
   - Expected: source contains `--scan-dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports a --scan-dir override for isolated testing")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = read_file("scripts/check/check-ui-backend-isolation.shs")
expect(source.contains("--scan-dir")).to_equal(true)
```

</details>

#### reports machine-readable key=value status lines

- reports machine-readable key=value status lines
   - Expected: source contains `ui_backend_isolation_new=`
   - Expected: source contains `ui_backend_isolation_ok=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports machine-readable key=value status lines")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = read_file("scripts/check/check-ui-backend-isolation.shs")
expect(source.contains("ui_backend_isolation_new=")).to_equal(true)
expect(source.contains("ui_backend_isolation_ok=")).to_equal(true)
```

</details>

#### has a committed baseline capturing the current fix-wave debt

- has a committed baseline capturing the current fix-wave debt
   - Expected: file_exists("scripts/check/ui_backend_isolation_baseline.txt") is true
   - Expected: baseline contains `RT:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a committed baseline capturing the current fix-wave debt")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(file_exists("scripts/check/ui_backend_isolation_baseline.txt")).to_equal(true)
val baseline = read_file("scripts/check/ui_backend_isolation_baseline.txt")
expect(baseline.contains("RT:")).to_equal(true)
```

</details>

#### keeps host winit operations in the canonical runtime facade only

- keeps host winit operations in the canonical runtime facade only
   - Expected: file_exists("src/lib/common/ui/host_winit_surface.spl") is false
   - Expected: owner contains `fn winit_window_set_fullscreen`
   - Expected: owner contains `fn winit_window_is_fullscreen`
   - Expected: owner contains `fn winit_window_get_size`
   - Expected: owner contains `fn winit_window_scale_factor`
   - Expected: owner contains `fn winit_window_get_position`
   - Expected: owner contains `fn winit_window_set_position`
   - Expected: owner contains `fn winit_event_window_position`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps host winit operations in the canonical runtime facade only")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(file_exists("src/lib/common/ui/host_winit_surface.spl")).to_equal(false)
val owner = read_file("src/lib/nogc_sync_mut/io/window_winit.spl")
expect(owner.contains("fn winit_window_set_fullscreen")).to_equal(true)
expect(owner.contains("fn winit_window_is_fullscreen")).to_equal(true)
expect(owner.contains("fn winit_window_get_size")).to_equal(true)
expect(owner.contains("fn winit_window_scale_factor")).to_equal(true)
expect(owner.contains("fn winit_window_get_position")).to_equal(true)
expect(owner.contains("fn winit_window_set_position")).to_equal(true)
expect(owner.contains("fn winit_event_window_position")).to_equal(true)
```

</details>

#### routes the check worker probe through the canonical file facade

- routes the check worker probe through the canonical file facade
   - Expected: source contains `use std.nogc_sync_mut.io.file_ops.{file_exists}`
   - Expected: source contains `if file_exists(candidate):`
   - Expected: source does not contain `rt_file_exists`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes the check worker probe through the canonical file facade")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = read_file("src/app/cli/check_entry.spl")
expect(source.contains("use std.nogc_sync_mut.io.file_ops.{file_exists}")).to_equal(true)
expect(source.contains("if file_exists(candidate):")).to_equal(true)
expect(source.contains("rt_file_exists")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/ui/feature/backend_isolation_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UI backend-isolation enforcement gate.
- UI backend-isolation enforcement gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `afb6da8a31b82d7aa44884686cc7c7209fb9b45ad5e11a41d335a4aeefb6df18`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afb6da8a31b82d7aa44884686cc7c7209fb9b45ad5e11a41d335a4aeefb6df18`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afb6da8a31b82d7aa44884686cc7c7209fb9b45ad5e11a41d335a4aeefb6df18`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/ui/feature/backend_isolation_gate_spec.spl
mirror: doc/06_spec/03_system/app/ui/feature/backend_isolation_gate_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/app/ui/feature/backend_isolation_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui/feature/backend_isolation_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui/feature/backend_isolation_gate_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
