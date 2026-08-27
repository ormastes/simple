# Simpleos Wine Process Thunk Load Bind Specification

> Tests covering SimpleOS Wine thunk load binding, REQ-023: thunk planning requires module-loaded bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Thunk Load Bind Specification

## Scenarios

### SimpleOS Wine thunk load binding

### REQ-023: thunk planning requires module-loaded bindings

#### include module-load evidence in import thunk patch planning

- include module-load evidence in import thunk patch planning
   - Expected: result.ok is true
   - Expected: result.patch_count equals `3`
   - Expected: result.status equals `thunk-patch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-023
# @req REQ-SSPEC-SYSTEM
step("include module-load evidence in import thunk patch planning")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.patch_count).to_equal(3)  # oracle: result.patch_count must equal 3 — authoritative contract constant
expect(result.evidence).to_contain("import-module-loaded")
expect(result.evidence).to_contain("import-thunk-records-planned")
expect(result.evidence).to_contain("import-thunk-records-bounded")
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.status).to_equal("thunk-patch-planned")
```

</details>

#### block thunk planning before load-and-bind passes

- block thunk planning before load-and-bind passes
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("block thunk planning before load-and-bind passes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.status).to_equal("blocked")
```

</details>

#### require PEB/TEB VM byte-write readback before import thunk planning

- require PEB/TEB VM byte-write readback before import thunk planning
   - Expected: result.ok is true
   - Expected: result.patch_count equals `3`
   - Expected: result.status equals `thunk-patch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("require PEB/TEB VM byte-write readback before import thunk planning")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_plan_import_thunk_patches_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, vm_writes)

expect(result.ok).to_equal(true)
expect(result.patch_count).to_equal(3)  # oracle: result.patch_count must equal 3 — authoritative contract constant
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("tls-callback-dispatch-empty")
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.status).to_equal("thunk-patch-planned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine thunk load binding, REQ-023: thunk planning requires module-loaded bindings.
- SimpleOS Wine thunk load binding
- REQ-023: thunk planning requires module-loaded bindings

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
- `REQ-023`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `198bf776b8d77492a5d100967e6513b351a59b9afed299e8ee3542118851fa95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `198bf776b8d77492a5d100967e6513b351a59b9afed299e8ee3542118851fa95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `198bf776b8d77492a5d100967e6513b351a59b9afed299e8ee3542118851fa95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
