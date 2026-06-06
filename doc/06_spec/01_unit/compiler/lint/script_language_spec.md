# Script Language Specification

> <details>

<!-- sdn-diagram:id=script_language_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=script_language_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

script_language_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=script_language_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Script Language Specification

## Scenarios

### script language lint

#### flags Python automation scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "#!/usr/bin/env python3\nprint('smoke')\n"
expect(count_rule(source, "scripts/smoke/tool_smoke.py", "simple_script_required")).to_equal(1)
```

</details>

#### flags Python calls embedded in repository shell scripts

1. "print
   - Expected: count_rule(source, "scripts/check/example.shs", "simple_script_required") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "#!/bin/sh\n" +
    "python3 - \"$input\" <<'PY'\n" +
    "print('helper')\n" +
    "PY\n"
expect(count_rule(source, "scripts/check/example.shs", "simple_script_required")).to_equal(1)
```

</details>

#### does not flag vendored Python scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "print('generated')\n"
expect(count_rule(source, "src/app/vscode_extension/node_modules/tool.py", "simple_script_required")).to_equal(0)
```

</details>

#### allows Python tkinter comparison benchmark baseline

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("tools/gui_perf_bench/bench_python.py")
expect(count_rule(source, "tools/gui_perf_bench/bench_python.py", "simple_script_required")).to_equal(0)
```

</details>

#### allows shell invocation of the Python benchmark baseline

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("tools/gui_perf_bench/run_all_benchmarks.sh")
expect(count_rule(source, "tools/gui_perf_bench/run_all_benchmarks.sh", "simple_script_required")).to_equal(0)
```

</details>

#### allows cross-language benchmark Python baselines

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-cross-language-perf.shs")
expect(count_rule(source, "scripts/check/check-cross-language-perf.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated Simple smoke scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/smoke/simple_lsp_protocol_smoke.spl")
expect(count_rule(source, "scripts/smoke/simple_lsp_protocol_smoke.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated Neovim plugin smoke scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/smoke/nvim_plugin_smoke.spl")
expect(count_rule(source, "scripts/smoke/nvim_plugin_smoke.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated Simple audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/diagnostic_code_audit.spl")
expect(count_rule(source, "scripts/audit/diagnostic_code_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated diagnostic catalog audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/diagnostic_catalog_audit.spl")
expect(count_rule(source, "scripts/audit/diagnostic_catalog_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated noalloc reachable import audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/noalloc_reachable_imports.spl")
expect(count_rule(source, "scripts/audit/noalloc_reachable_imports.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated fast duplicate audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/fast_duplicate_check.spl")
expect(count_rule(source, "scripts/audit/fast_duplicate_check.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated API consistency audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/api_consistency_audit.spl")
expect(count_rule(source, "scripts/audit/api_consistency_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated repo hygiene audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/repo_hygiene_audit.spl")
expect(count_rule(source, "scripts/audit/repo_hygiene_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated naming consistency audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/naming_consistency_audit.spl")
expect(count_rule(source, "scripts/audit/naming_consistency_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated runtime backend boundary audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/runtime_backend_boundaries.spl")
expect(count_rule(source, "scripts/audit/runtime_backend_boundaries.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated OS hardening runtime evidence scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/os_harden_runtime_evidence.spl")
expect(count_rule(source, "scripts/audit/os_harden_runtime_evidence.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated OS hardening audit scripts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/audit/os_harden_audit.spl")
expect(count_rule(source, "scripts/audit/os_harden_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated iOS MDI probe helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/ios_mdi_probe_server.spl")
expect(count_rule(source, "scripts/check/ios_mdi_probe_server.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Tauri mobile setup after simulator selection migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("tools/tauri-shell/scripts/mobile-setup.shs")
expect(count_rule(source, "tools/tauri-shell/scripts/mobile-setup.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple iPhone simulator selector

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/first_available_iphone_simulator.spl")
expect(count_rule(source, "scripts/check/first_available_iphone_simulator.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag FAT32 VFAT preparation after seed migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/perf/prepare-fat32-4k-vfat.shs")
expect(count_rule(source, "scripts/perf/prepare-fat32-4k-vfat.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple FAT32 VFAT seed helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/perf/seed_fat32_4k_vfat.spl")
expect(count_rule(source, "scripts/perf/seed_fat32_4k_vfat.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag hosted WM capture evidence after PPM validation migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-hosted-wm-capture-evidence.shs")
expect(count_rule(source, "scripts/check/check-hosted-wm-capture-evidence.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple hosted WM PPM validation helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/validate_hosted_wm_capture_ppm.spl")
expect(count_rule(source, "scripts/check/validate_hosted_wm_capture_ppm.spl", "simple_script_required")).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not flag SimpleOS hardening evidence matrix after PPM anchor migration</summary>

#### does not flag SimpleOS hardening evidence matrix after PPM anchor migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-simpleos-hardening-evidence-matrix.shs")
expect(count_rule(source, "scripts/check/check-simpleos-hardening-evidence-matrix.shs", "simple_script_required")).to_equal(0)
```

</details>


</details>

#### does not flag SimpleOS hardening PPM anchor helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/validate_simpleos_hardening_qemu_mdi_ppm.spl")
expect(count_rule(source, "scripts/check/validate_simpleos_hardening_qemu_mdi_ppm.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag MCP native smoke after JSON validation migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-mcp-native-smoke.shs")
expect(count_rule(source, "scripts/check/check-mcp-native-smoke.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple MCP native smoke validator

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/validate_mcp_native_smoke.spl")
expect(count_rule(source, "scripts/check/validate_mcp_native_smoke.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag macOS GUI live-window evidence after BMP metrics migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-macos-gui-live-window-evidence.shs")
expect(count_rule(source, "scripts/check/check-macos-gui-live-window-evidence.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple macOS GUI live-window BMP metrics helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/measure_macos_gui_live_window_bmp.spl")
expect(count_rule(source, "scripts/check/measure_macos_gui_live_window_bmp.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Tauri capture-all after simulator selection migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("tools/tauri-shell/capture-all.command")
expect(count_rule(source, "tools/tauri-shell/capture-all.command", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag mold installer after GitHub CLI download migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/setup/install-mold.shs")
expect(count_rule(source, "scripts/setup/install-mold.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib runtime shim check after native smoke migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-scilib-runtime-shims.shs")
expect(count_rule(source, "scripts/check/check-scilib-runtime-shims.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib runtime C smoke helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/runtime/scilib/runtime_shim_smoke.c")
expect(count_rule(source, "src/runtime/scilib/runtime_shim_smoke.c", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator gates after libtorch probe migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-scilib-accelerator-gates.shs")
expect(count_rule(source, "scripts/check/check-scilib-accelerator-gates.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator perf after native smoke migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-scilib-accelerator-perf.shs")
expect(count_rule(source, "scripts/check/check-scilib-accelerator-perf.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator perf C smoke helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/runtime/scilib/accelerator_perf_smoke.c")
expect(count_rule(source, "src/runtime/scilib/accelerator_perf_smoke.c", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator perf CUDA helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/runtime/scilib/accelerator_perf_smoke_cuda.inc")
expect(count_rule(source, "src/runtime/scilib/accelerator_perf_smoke_cuda.inc", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator perf Torch helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/runtime/scilib/accelerator_perf_smoke_torch.inc")
expect(count_rule(source, "src/runtime/scilib/accelerator_perf_smoke_torch.inc", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag OS disk image builder after native migration

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/os/make_os_disk.shs")
expect(count_rule(source, "scripts/os/make_os_disk.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag native OS disk image builder helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/os/make_os_disk.c")
expect(count_rule(source, "scripts/os/make_os_disk.c", "simple_script_required")).to_equal(0)
```

</details>

### primitive API severity

#### promotes primitive_api to deny by default

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/90.tools/lint/main_part1.spl")
expect(source.contains("levels[\"primitive_api\"] = \"deny\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/script_language_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- script language lint
- primitive API severity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
