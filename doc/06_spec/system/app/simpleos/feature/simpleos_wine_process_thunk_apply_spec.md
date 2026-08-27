# Simpleos Wine Process Thunk Apply Specification

> Tests covering SimpleOS Wine thunk patch apply, REQ-025: bounded import thunk byte patching.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Thunk Apply Specification

## Scenarios

### SimpleOS Wine thunk patch apply

### REQ-025: bounded import thunk byte patching

#### modeled KERNEL32 procedure addresses land in known thunk slots

- apply modeled KERNEL32 thunk patches to the known hello.exe fixture image
   - Expected: result.ok is true
   - Expected: result.patched_count equals `3`
   - Expected: _read_u64_le(result.patched_image, get_std_handle_offset) equals `0x120000 + 5`
   - Expected: _read_u64_le(result.patched_image, write_file_offset) equals `0x120000 + 6`
   - Expected: _read_u64_le(result.patched_image, exit_process_offset) equals `0x120000 + 7`
   - Expected: result.status equals `thunk-patches-applied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-025
# @req REQ-SSPEC-SYSTEM
step("apply modeled KERNEL32 thunk patches to the known hello.exe fixture image")
# evidence(binary_layout): patched thunk-slot bytes read back as u64 LE below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 8)
val get_std_handle_offset = pe_rva_to_file_offset(result.patched_image, 0x2060)
val write_file_offset = pe_rva_to_file_offset(result.patched_image, 0x2068)
val exit_process_offset = pe_rva_to_file_offset(result.patched_image, 0x2070)
expect(result.ok).to_equal(true)
expect(result.patched_count).to_equal(3)  # oracle: exactly three KERNEL32 imports (GetStdHandle, WriteFile, ExitProcess) are modeled by the fixture
expect(_read_u64_le(result.patched_image, get_std_handle_offset)).to_equal(0x120000 + 5)
expect(_read_u64_le(result.patched_image, write_file_offset)).to_equal(0x120000 + 6)
expect(_read_u64_le(result.patched_image, exit_process_offset)).to_equal(0x120000 + 7)
expect(result.evidence).to_contain("import-thunk-bytes-written")
expect(result.status).to_equal("thunk-patches-applied")
```

</details>

#### thunk byte patching is rejected before record planning passes

- request thunk patches with an invalid symbol limit of 0
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.patched_image.len() equals `0`
   - Expected: result.patched_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-025
# @req REQ-SSPEC-SYSTEM
step("request thunk patches with an invalid symbol limit of 0")
# evidence(protocol_json): result.ok/error/patched_count fields asserted below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.patched_image.len()).to_equal(0)  # oracle: a rejected patch leaves the image untouched, zero bytes patched
expect(result.patched_count).to_equal(0)  # oracle: a rejected patch patches nothing
expect(result.evidence).to_contain("thunk-patches-blocked")
expect(result.evidence).to_contain("no-thunk-bytes-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

#### patched image bytes are prepared before known-console dispatch

- prepare the patched console image with full CPU execution evidence
   - Expected: result.ok is true
   - Expected: _read_u64_le(result.patched_image, get_std_handle_offset) equals `0x120000 + 5`
   - Expected: result.status equals `patched-image-preflight-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-025
# @req REQ-SSPEC-SYSTEM
step("prepare the patched console image with full CPU execution evidence")
# evidence(binary_layout): patched thunk-slot u64 read back below is the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
val get_std_handle_offset = pe_rva_to_file_offset(result.patched_image, 0x2060)
expect(result.ok).to_equal(true)
expect(_read_u64_le(result.patched_image, get_std_handle_offset)).to_equal(0x120000 + 5)
expect(result.evidence).to_contain("import-thunk-bytes-written")
expect(result.status).to_equal("patched-image-preflight-ready")
```

</details>

#### patched image preflight is blocked before CPU evidence is complete

- request patched image preparation with empty CPU evidence text
   - Expected: result.ok is false
   - Expected: result.error equals `missing-thread-context`
   - Expected: result.patched_image.len() equals `0`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-025
# @req REQ-SSPEC-SYSTEM
step("request patched image preparation with empty CPU evidence text")
# evidence(protocol_json): blocked result error/status/evidence fields asserted below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, "")

expect(result.ok).to_equal(false)
expect(result.error).to_equal("missing-thread-context")
expect(result.patched_image.len()).to_equal(0)  # oracle: a rejected patch leaves the image untouched, zero bytes patched
expect(result.evidence).to_contain("patched-image-preflight-blocked")
expect(result.evidence).to_contain("no-thunk-bytes-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

#### patched image preflight is blocked when record planning rejects

- request patched image preparation with an invalid symbol limit of 0
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.patched_image.len() equals `0`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-025
# @req REQ-SSPEC-SYSTEM
step("request patched image preparation with an invalid symbol limit of 0")
# evidence(protocol_json): blocked result error/status/evidence fields asserted below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 0, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))

expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.patched_image.len()).to_equal(0)  # oracle: a rejected patch leaves the image untouched, zero bytes patched
expect(result.evidence).to_contain("patched-image-preflight-blocked")
expect(result.evidence).to_contain("no-thunk-bytes-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_thunk_apply_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine thunk patch apply, REQ-025: bounded import thunk byte patching.
- SimpleOS Wine thunk patch apply
- REQ-025: bounded import thunk byte patching

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-025`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a12568581977db20b4da6dbe75a30310a48cb482549b32dfe2f4b514a1cc29cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a12568581977db20b4da6dbe75a30310a48cb482549b32dfe2f4b514a1cc29cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a12568581977db20b4da6dbe75a30310a48cb482549b32dfe2f4b514a1cc29cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/system/app/simpleos/feature/simpleos_wine_process_thunk_apply_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_thunk_apply_spec.md (current)
findings: 3 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_thunk_apply_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_thunk_apply_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_thunk_apply_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
<!-- sspec-maintain:scorecard:end -->
