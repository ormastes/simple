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

#### should include module-load evidence in import thunk patch planning

- should include module-load evidence in import thunk patch planning
   - Expected: result.ok is true
   - Expected: result.patch_count equals `3`
   - Expected: result.status equals `thunk-patch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-023
# @req REQ-SSPEC-SYSTEM
step("should include module-load evidence in import thunk patch planning")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.patch_count).to_equal(3)
expect(result.evidence).to_contain("import-module-loaded")
expect(result.evidence).to_contain("import-thunk-records-planned")
expect(result.evidence).to_contain("import-thunk-records-bounded")
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.status).to_equal("thunk-patch-planned")
```

</details>

#### should block thunk planning before load-and-bind passes

- should block thunk planning before load-and-bind passes
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should block thunk planning before load-and-bind passes")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.status).to_equal("blocked")
```

</details>

#### should require PEB/TEB VM byte-write readback before import thunk planning

- should require PEB/TEB VM byte-write readback before import thunk planning
   - Expected: result.ok is true
   - Expected: result.patch_count equals `3`
   - Expected: result.status equals `thunk-patch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require PEB/TEB VM byte-write readback before import thunk planning")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_plan_import_thunk_patches_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, vm_writes)

expect(result.ok).to_equal(true)
expect(result.patch_count).to_equal(3)
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
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl` |
| Updated | 2026-08-27 |
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

- Canonical SPipe generation for source `e544d42dc4078583ee40be6b8706a49605b7ede6c8dc9c3c8f6ef6542d10a44f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e544d42dc4078583ee40be6b8706a49605b7ede6c8dc9c3c8f6ef6542d10a44f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e544d42dc4078583ee40be6b8706a49605b7ede6c8dc9c3c8f6ef6542d10a44f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include module-load evidence in import thunk patch planning' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include module-load evidence in import thunk patch planning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should block thunk planning before load-and-bind passes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should block thunk planning before load-and-bind passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before import thunk planning' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before import thunk planning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
