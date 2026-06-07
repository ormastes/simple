# Wine Process Session Thunk Apply Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_thunk_apply_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_thunk_apply_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_thunk_apply_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_thunk_apply_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Thunk Apply Specification

## Scenarios

### Wine process session thunk patch apply

#### writes modeled KERNEL32 procedure addresses into bounded thunk slots

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 8)
val get_std_handle_offset = pe_rva_to_file_offset(result.patched_image, 0x2060)
val write_file_offset = pe_rva_to_file_offset(result.patched_image, 0x2068)
val exit_process_offset = pe_rva_to_file_offset(result.patched_image, 0x2070)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.patched_count).to_equal(3)
expect(_read_u64_le(result.patched_image, get_std_handle_offset)).to_equal(0x120000 + 5)
expect(_read_u64_le(result.patched_image, write_file_offset)).to_equal(0x120000 + 6)
expect(_read_u64_le(result.patched_image, exit_process_offset)).to_equal(0x120000 + 7)
expect(result.evidence).to_contain("import-thunk-bytes-written")
expect(result.status).to_equal("thunk-patches-applied")
```

</details>

#### keeps thunk byte patching behind record planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.patched_image.len()).to_equal(0)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("thunk-patches-blocked")
expect(result.evidence).to_contain("no-thunk-bytes-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

#### prepares a patched image before known-console dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
val get_std_handle_offset = pe_rva_to_file_offset(result.patched_image, 0x2060)
expect(result.ok).to_equal(true)
expect(_read_u64_le(result.patched_image, get_std_handle_offset)).to_equal(0x120000 + 5)
expect(result.evidence).to_contain("import-thunk-bytes-written")
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.status).to_equal("patched-image-preflight-ready")
```

</details>

#### blocks patched image preflight without image bytes before CPU evidence is complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, "")

expect(result.ok).to_equal(false)
expect(result.error).to_equal("missing-thread-context")
expect(result.patched_image.len()).to_equal(0)
expect(result.evidence).to_contain("patched-image-preflight-blocked")
expect(result.evidence).to_contain("no-thunk-bytes-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

#### blocks patched image preflight without image bytes when record planning rejects

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 0, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))

expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.patched_image.len()).to_equal(0)
expect(result.evidence).to_contain("patched-image-preflight-blocked")
expect(result.evidence).to_contain("no-thunk-bytes-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_thunk_apply_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session thunk patch apply

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
