# Wine Process Session Thunk Load Bind Specification

> Tests covering Wine process session thunk load binding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Thunk Load Bind Specification

## Scenarios

### Wine process session thunk load binding

#### requires module-load evidence before planning import thunk patches

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires module-load evidence before planning import thunk patches
   - Expected: result.ok is true
   - Expected: result.dll_name equals `kernel32.dll`
   - Expected: result.patch_count equals `3`
   - Expected: result.status equals `thunk-patch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires module-load evidence before planning import thunk patches")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.patch_count).to_equal(3)
expect(result.evidence).to_contain("import-module-loaded")
expect(result.evidence).to_contain("import-module-loader-sequence")
expect(result.evidence).to_contain("import-thunk-records-planned")
expect(result.evidence).to_contain("import-thunk-records-bounded")
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.status).to_equal("thunk-patch-planned")
```

</details>

#### propagates load-and-bind rejection before thunk planning

- propagates load-and-bind rejection before thunk planning
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates load-and-bind rejection before thunk planning")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.status).to_equal("blocked")
```

</details>

#### plans import thunk patches only after PEB/TEB VM byte-write readback

- plans import thunk patches only after PEB/TEB VM byte-write readback
   - Expected: result.ok is true
   - Expected: result.patch_count equals `3`
   - Expected: result.status equals `thunk-patch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("plans import thunk patches only after PEB/TEB VM byte-write readback")
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

#### blocks import thunk planning when PEB/TEB VM byte writes are not ready

- blocks import thunk planning when PEB/TEB VM byte writes are not ready
   - Expected: result.ok is false
   - Expected: result.error equals `peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blocks import thunk planning when PEB/TEB VM byte writes are not ready")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_plan_import_thunk_patches_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.status).to_equal("rejected")
expect(result.evidence).to_contain("full-image-handoff-blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session thunk load binding.
- Wine process session thunk load binding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `a57896f68ec93fe9edf2eff08500ad02560a030a66f7c715888bfd2938ade860`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a57896f68ec93fe9edf2eff08500ad02560a030a66f7c715888bfd2938ade860`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a57896f68ec93fe9edf2eff08500ad02560a030a66f7c715888bfd2938ade860`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires module-load evidence before planning import thunk patches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates load-and-bind rejection before thunk planning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans import thunk patches only after PEB/TEB VM byte-write readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
