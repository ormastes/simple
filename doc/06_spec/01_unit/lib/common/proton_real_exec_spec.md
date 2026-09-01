# proton_real_exec_spec

> Proton real execution via pressure-vessel container dispatch (AC-1, AC-10).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# proton_real_exec_spec

Proton real execution via pressure-vessel container dispatch (AC-1, AC-10).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/proton_real_exec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proton real execution via pressure-vessel container dispatch (AC-1, AC-10).

## Scenarios

### Proton real execution via pressure-vessel

#### dry_run=true still returns dry-run-ready (regression)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dry_run=true still returns dry-run-ready (regression)
   - Expected: handoff.ok is true
   - Expected: handoff.status equals `dry-run-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dry_run=true still returns dry-run-ready (regression)")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, true)
expect(handoff.ok).to_equal(true)
expect(handoff.status).to_equal("dry-run-ready")
```

</details>

#### dry_run=false no longer returns execution-not-implemented

- dry_run=false no longer returns execution-not-implemented
   - Expected: handoff.error equals ``
   - Expected: handoff.status != "blocked" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dry_run=false no longer returns execution-not-implemented")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.error).to_equal("")
expect(handoff.status != "blocked").to_equal(true)
```

</details>

#### dry_run=false returns exec-dispatched status

- dry_run=false returns exec-dispatched status
   - Expected: handoff.ok is true
   - Expected: handoff.status equals `exec-dispatched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dry_run=false returns exec-dispatched status")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.ok).to_equal(true)
expect(handoff.status).to_equal("exec-dispatched")
```

</details>

#### dry_run=false launch_command contains wine64

- dry_run=false launch_command contains wine64


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dry_run=false launch_command contains wine64")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.launch_command).to_contain("wine64")
expect(handoff.launch_command).to_contain("hl2.exe")
```

</details>

#### container_profile contains namespace facets

- container_profile contains namespace facets


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("container_profile contains namespace facets")
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", [])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.container_profile).to_contain("ns-pid")
expect(handoff.container_profile).to_contain("ns-fs")
expect(handoff.container_profile).to_contain("ns-capability")
```

</details>

#### invalid plan returns error for both dry_run modes

- invalid plan returns error for both dry_run modes
   - Expected: dry.ok is false
   - Expected: dry.status equals `blocked`
   - Expected: real.ok is false
   - Expected: real.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invalid plan returns error for both dry_run modes")
val request = proton_session_request_new("", "steamapps/compatdata/480/pfx", "hl2.exe", [])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val dry = proton_session_launch_handoff(plan, true)
expect(dry.ok).to_equal(false)
expect(dry.status).to_equal("blocked")
val real = proton_session_launch_handoff(plan, false)
expect(real.ok).to_equal(false)
expect(real.status).to_equal("blocked")
```

</details>

#### missing compat_prefix returns error

- missing compat_prefix returns error
   - Expected: handoff.ok is false
   - Expected: handoff.error equals `missing-compat-prefix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("missing compat_prefix returns error")
val request = proton_session_request_new("480", "", "hl2.exe", [])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.ok).to_equal(false)
expect(handoff.error).to_equal("missing-compat-prefix")
```

</details>

#### pressure_vessel_exec_wine composes wine command

- pressure_vessel_exec_wine composes wine command
   - Expected: container.is_ok is true
   - Expected: result.is_ok is true
   - Expected: result.status equals `exec-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pressure_vessel_exec_wine composes wine command")
val container = pressure_vessel_create("/tmp/rootfs", true)
expect(container.is_ok).to_equal(true)
val result = pressure_vessel_exec_wine(container.container_id, "game.exe")
expect(result.is_ok).to_equal(true)
expect(result.status).to_equal("exec-ready")
pressure_vessel_destroy(container.container_id)
```

</details>

#### pressure_vessel_exec_wine fails with empty executable

- pressure_vessel_exec_wine fails with empty executable
   - Expected: result.is_ok is false
   - Expected: result.error equals `missing-executable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pressure_vessel_exec_wine fails with empty executable")
val container = pressure_vessel_create("/tmp/rootfs", true)
val result = pressure_vessel_exec_wine(container.container_id, "")
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("missing-executable")
pressure_vessel_destroy(container.container_id)
```

</details>

#### pressure_vessel_setup_wine_prefix succeeds with valid path

- pressure_vessel_setup_wine_prefix succeeds with valid path
   - Expected: result.is_ok is true
   - Expected: result.status equals `prefix-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pressure_vessel_setup_wine_prefix succeeds with valid path")
val container = pressure_vessel_create("/tmp/rootfs", true)
val result = pressure_vessel_setup_wine_prefix(container.container_id, "/tmp/wine-prefix")
expect(result.is_ok).to_equal(true)
expect(result.status).to_equal("prefix-ready")
pressure_vessel_destroy(container.container_id)
```

</details>

#### pressure_vessel_setup_wine_prefix fails with empty path

- pressure_vessel_setup_wine_prefix fails with empty path
   - Expected: result.is_ok is false
   - Expected: result.error equals `missing-prefix-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pressure_vessel_setup_wine_prefix fails with empty path")
val container = pressure_vessel_create("/tmp/rootfs", true)
val result = pressure_vessel_setup_wine_prefix(container.container_id, "")
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("missing-prefix-path")
pressure_vessel_destroy(container.container_id)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee9d8d1fb64781ea54212881efe94b8f9f8a57e9f8e09049db89ba3cc5e6fe43`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee9d8d1fb64781ea54212881efe94b8f9f8a57e9f8e09049db89ba3cc5e6fe43`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee9d8d1fb64781ea54212881efe94b8f9f8a57e9f8e09049db89ba3cc5e6fe43`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/proton_real_exec_spec.spl
mirror: doc/06_spec/01_unit/lib/common/proton_real_exec_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/proton_real_exec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/proton_real_exec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/proton_real_exec_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pressure_vessel_exec_wine composes wine command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/proton_real_exec_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pressure_vessel_exec_wine fails with empty executable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/proton_real_exec_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pressure_vessel_setup_wine_prefix succeeds with valid path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
