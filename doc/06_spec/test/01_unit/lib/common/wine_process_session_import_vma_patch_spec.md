# Wine Process Session Import Vma Patch Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_import_vma_patch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_import_vma_patch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_import_vma_patch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_import_vma_patch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Import Vma Patch Specification

## Scenarios

### Wine process session import descriptor VMA patching

#### applies descriptor-qualified modeled procedure addresses through a VMA write window

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.patched_count).to_equal(4)
expect(result.mapped_base).to_equal(0x400000)
expect(result.patched_image[0x260] as i64).to_equal(0x80)
expect(result.patched_image[0x270] as i64).to_equal(0x05)
expect(result.patched_image[0x272] as i64).to_equal(0x12)
expect(result.patched_image[0x390] as i64).to_equal(0xf0)
expect(result.patched_image[0x3a0] as i64).to_equal(0x06)
expect(result.patched_image[0x3a1] as i64).to_equal(0x10)
expect(result.patched_image[0x3a2] as i64).to_equal(0x12)
expect(result.evidence).to_contain("import-descriptor-iat-rvas-recorded")
expect(result.evidence).to_contain("process-vma-write-enabled")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("multi-dll-import-thunks-applied")
expect(result.status).to_equal("import-descriptor-vma-thunk-patches-applied")
```

</details>

#### keeps VMA patching behind modeled import resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.patched_count).to_equal(0)
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_import_vma_patch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session import descriptor VMA patching

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
