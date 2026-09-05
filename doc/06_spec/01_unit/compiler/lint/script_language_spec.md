# Script Language Specification

> Tests covering script language lint, primitive API severity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Script Language Specification

## Scenarios

### script language lint

#### flags Python automation scripts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags Python automation scripts
   - Expected: count_rule(source, "scripts/smoke/tool_smoke.py", "simple_script_required") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags Python automation scripts")
val source = "#!/usr/bin/env python3\nprint('smoke')\n"
expect(count_rule(source, "scripts/smoke/tool_smoke.py", "simple_script_required")).to_equal(1)
```

</details>

#### flags Python calls embedded in repository shell scripts

- flags Python calls embedded in repository shell scripts
   - Expected: count_rule(source, "scripts/check/example.shs", "simple_script_required") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags Python calls embedded in repository shell scripts")
val source =
    "#!/bin/sh\n" +
    "python3 - \"$input\" <<'PY'\n" +
    "print('helper')\n" +
    "PY\n"
expect(count_rule(source, "scripts/check/example.shs", "simple_script_required")).to_equal(1)
```

</details>

#### does not flag vendored Python scripts

- does not flag vendored Python scripts
   - Expected: count_rule(source, "src/app/vscode_extension/node_modules/tool.py", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag vendored Python scripts")
val source = "print('generated')\n"
expect(count_rule(source, "src/app/vscode_extension/node_modules/tool.py", "simple_script_required")).to_equal(0)
```

</details>

#### allows Python tkinter comparison benchmark baseline

- allows Python tkinter comparison benchmark baseline
   - Expected: count_rule(source, "tools/gui_perf_bench/bench_python.py", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows Python tkinter comparison benchmark baseline")
val source = rt_file_read_text("tools/gui_perf_bench/bench_python.py")
expect(count_rule(source, "tools/gui_perf_bench/bench_python.py", "simple_script_required")).to_equal(0)
```

</details>

#### allows shell invocation of the Python benchmark baseline

- allows shell invocation of the Python benchmark baseline
   - Expected: count_rule(source, "tools/gui_perf_bench/run_all_benchmarks.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows shell invocation of the Python benchmark baseline")
val source = rt_file_read_text("tools/gui_perf_bench/run_all_benchmarks.shs")
expect(count_rule(source, "tools/gui_perf_bench/run_all_benchmarks.shs", "simple_script_required")).to_equal(0)
```

</details>

#### allows cross-language benchmark Python baselines

- allows cross-language benchmark Python baselines
   - Expected: count_rule(source, "scripts/check/check-cross-language-perf.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows cross-language benchmark Python baselines")
val source = rt_file_read_text("scripts/check/check-cross-language-perf.shs")
expect(count_rule(source, "scripts/check/check-cross-language-perf.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated Simple smoke scripts

- does not flag migrated Simple smoke scripts
   - Expected: count_rule(source, "scripts/smoke/simple_lsp_protocol_smoke.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated Simple smoke scripts")
val source = rt_file_read_text("scripts/smoke/simple_lsp_protocol_smoke.spl")
expect(count_rule(source, "scripts/smoke/simple_lsp_protocol_smoke.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated Neovim plugin smoke scripts

- does not flag migrated Neovim plugin smoke scripts
   - Expected: count_rule(source, "scripts/smoke/nvim_plugin_smoke.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated Neovim plugin smoke scripts")
val source = rt_file_read_text("scripts/smoke/nvim_plugin_smoke.spl")
expect(count_rule(source, "scripts/smoke/nvim_plugin_smoke.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated Simple audit scripts

- does not flag migrated Simple audit scripts
   - Expected: count_rule(source, "scripts/audit/diagnostic_code_audit.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated Simple audit scripts")
val source = rt_file_read_text("scripts/audit/diagnostic_code_audit.spl")
expect(count_rule(source, "scripts/audit/diagnostic_code_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated diagnostic catalog audit scripts

- does not flag migrated diagnostic catalog audit scripts
   - Expected: count_rule(source, "scripts/audit/diagnostic_catalog_audit.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated diagnostic catalog audit scripts")
val source = rt_file_read_text("scripts/audit/diagnostic_catalog_audit.spl")
expect(count_rule(source, "scripts/audit/diagnostic_catalog_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated noalloc reachable import audit scripts

- does not flag migrated noalloc reachable import audit scripts
   - Expected: count_rule(source, "scripts/audit/noalloc_reachable_imports.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated noalloc reachable import audit scripts")
val source = rt_file_read_text("scripts/audit/noalloc_reachable_imports.spl")
expect(count_rule(source, "scripts/audit/noalloc_reachable_imports.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated fast duplicate audit scripts

- does not flag migrated fast duplicate audit scripts
   - Expected: count_rule(source, "scripts/audit/fast_duplicate_check.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated fast duplicate audit scripts")
val source = rt_file_read_text("scripts/audit/fast_duplicate_check.spl")
expect(count_rule(source, "scripts/audit/fast_duplicate_check.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated API consistency audit scripts

- does not flag migrated API consistency audit scripts
   - Expected: count_rule(source, "scripts/audit/api_consistency_audit.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated API consistency audit scripts")
val source = rt_file_read_text("scripts/audit/api_consistency_audit.spl")
expect(count_rule(source, "scripts/audit/api_consistency_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated repo hygiene audit scripts

- does not flag migrated repo hygiene audit scripts
   - Expected: count_rule(source, "scripts/audit/repo_hygiene_audit.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated repo hygiene audit scripts")
val source = rt_file_read_text("scripts/audit/repo_hygiene_audit.spl")
expect(count_rule(source, "scripts/audit/repo_hygiene_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated naming consistency audit scripts

- does not flag migrated naming consistency audit scripts
   - Expected: count_rule(source, "scripts/audit/naming_consistency_audit.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated naming consistency audit scripts")
val source = rt_file_read_text("scripts/audit/naming_consistency_audit.spl")
expect(count_rule(source, "scripts/audit/naming_consistency_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated runtime backend boundary audit scripts

- does not flag migrated runtime backend boundary audit scripts
   - Expected: count_rule(source, "scripts/audit/runtime_backend_boundaries.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated runtime backend boundary audit scripts")
val source = rt_file_read_text("scripts/audit/runtime_backend_boundaries.spl")
expect(count_rule(source, "scripts/audit/runtime_backend_boundaries.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated OS hardening runtime evidence scripts

- does not flag migrated OS hardening runtime evidence scripts
   - Expected: count_rule(source, "scripts/audit/os_harden_runtime_evidence.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated OS hardening runtime evidence scripts")
val source = rt_file_read_text("scripts/audit/os_harden_runtime_evidence.spl")
expect(count_rule(source, "scripts/audit/os_harden_runtime_evidence.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated OS hardening audit scripts

- does not flag migrated OS hardening audit scripts
   - Expected: count_rule(source, "scripts/audit/os_harden_audit.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated OS hardening audit scripts")
val source = rt_file_read_text("scripts/audit/os_harden_audit.spl")
expect(count_rule(source, "scripts/audit/os_harden_audit.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag migrated iOS MDI probe helper

- does not flag migrated iOS MDI probe helper
   - Expected: count_rule(source, "scripts/check/ios_mdi_probe_server.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag migrated iOS MDI probe helper")
val source = rt_file_read_text("scripts/check/ios_mdi_probe_server.spl")
expect(count_rule(source, "scripts/check/ios_mdi_probe_server.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Tauri mobile setup after simulator selection migration

- does not flag Tauri mobile setup after simulator selection migration
   - Expected: count_rule(source, "tools/tauri-shell/scripts/mobile-setup.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag Tauri mobile setup after simulator selection migration")
val source = rt_file_read_text("tools/tauri-shell/scripts/mobile-setup.shs")
expect(count_rule(source, "tools/tauri-shell/scripts/mobile-setup.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple iPhone simulator selector

- does not flag Simple iPhone simulator selector
   - Expected: count_rule(source, "scripts/check/first_available_iphone_simulator.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag Simple iPhone simulator selector")
val source = rt_file_read_text("scripts/check/first_available_iphone_simulator.spl")
expect(count_rule(source, "scripts/check/first_available_iphone_simulator.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag FAT32 VFAT preparation after seed migration

- does not flag FAT32 VFAT preparation after seed migration
   - Expected: count_rule(source, "scripts/perf/prepare-fat32-4k-vfat.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag FAT32 VFAT preparation after seed migration")
val source = rt_file_read_text("scripts/perf/prepare-fat32-4k-vfat.shs")
expect(count_rule(source, "scripts/perf/prepare-fat32-4k-vfat.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple FAT32 VFAT seed helper

- does not flag Simple FAT32 VFAT seed helper
   - Expected: count_rule(source, "scripts/perf/seed_fat32_4k_vfat.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag Simple FAT32 VFAT seed helper")
val source = rt_file_read_text("scripts/perf/seed_fat32_4k_vfat.spl")
expect(count_rule(source, "scripts/perf/seed_fat32_4k_vfat.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag hosted WM capture evidence after PPM validation migration

- does not flag hosted WM capture evidence after PPM validation migration
   - Expected: count_rule(source, "scripts/check/check-hosted-wm-capture-evidence.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag hosted WM capture evidence after PPM validation migration")
val source = rt_file_read_text("scripts/check/check-hosted-wm-capture-evidence.shs")
expect(count_rule(source, "scripts/check/check-hosted-wm-capture-evidence.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple hosted WM PPM validation helper

- does not flag Simple hosted WM PPM validation helper
   - Expected: count_rule(source, "scripts/check/validate_hosted_wm_capture_ppm.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag Simple hosted WM PPM validation helper")
val source = rt_file_read_text("scripts/check/validate_hosted_wm_capture_ppm.spl")
expect(count_rule(source, "scripts/check/validate_hosted_wm_capture_ppm.spl", "simple_script_required")).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not flag SimpleOS hardening evidence matrix after PPM anchor migration</summary>

#### does not flag SimpleOS hardening evidence matrix after PPM anchor migration

- does not flag SimpleOS hardening evidence matrix after PPM anchor migration
   - Expected: count_rule(source, "scripts/check/check-simpleos-hardening-evidence-matrix.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SimpleOS hardening evidence matrix after PPM anchor migration")
val source = rt_file_read_text("scripts/check/check-simpleos-hardening-evidence-matrix.shs")
expect(count_rule(source, "scripts/check/check-simpleos-hardening-evidence-matrix.shs", "simple_script_required")).to_equal(0)
```

</details>


</details>

#### does not flag SimpleOS hardening PPM anchor helper

- does not flag SimpleOS hardening PPM anchor helper
   - Expected: count_rule(source, "scripts/check/validate_simpleos_hardening_qemu_mdi_ppm.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SimpleOS hardening PPM anchor helper")
val source = rt_file_read_text("scripts/check/validate_simpleos_hardening_qemu_mdi_ppm.spl")
expect(count_rule(source, "scripts/check/validate_simpleos_hardening_qemu_mdi_ppm.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag MCP native smoke after JSON validation migration

- does not flag MCP native smoke after JSON validation migration
   - Expected: count_rule(source, "scripts/check/check-mcp-native-smoke.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag MCP native smoke after JSON validation migration")
val source = rt_file_read_text("scripts/check/check-mcp-native-smoke.shs")
expect(count_rule(source, "scripts/check/check-mcp-native-smoke.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple MCP native smoke validator

- does not flag Simple MCP native smoke validator
   - Expected: count_rule(source, "scripts/check/validate_mcp_native_smoke.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag Simple MCP native smoke validator")
val source = rt_file_read_text("scripts/check/validate_mcp_native_smoke.spl")
expect(count_rule(source, "scripts/check/validate_mcp_native_smoke.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag macOS GUI live-window evidence after BMP metrics migration

- does not flag macOS GUI live-window evidence after BMP metrics migration
   - Expected: count_rule(source, "scripts/check/check-macos-gui-live-window-evidence.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag macOS GUI live-window evidence after BMP metrics migration")
val source = rt_file_read_text("scripts/check/check-macos-gui-live-window-evidence.shs")
expect(count_rule(source, "scripts/check/check-macos-gui-live-window-evidence.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Simple macOS GUI live-window BMP metrics helper

- does not flag Simple macOS GUI live-window BMP metrics helper
   - Expected: count_rule(source, "scripts/check/measure_macos_gui_live_window_bmp.spl", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag Simple macOS GUI live-window BMP metrics helper")
val source = rt_file_read_text("scripts/check/measure_macos_gui_live_window_bmp.spl")
expect(count_rule(source, "scripts/check/measure_macos_gui_live_window_bmp.spl", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag Tauri capture-all after simulator selection migration

- does not flag Tauri capture-all after simulator selection migration
   - Expected: count_rule(source, "tools/tauri-shell/capture-all.command", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag Tauri capture-all after simulator selection migration")
val source = rt_file_read_text("tools/tauri-shell/capture-all.command")
expect(count_rule(source, "tools/tauri-shell/capture-all.command", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag mold installer after GitHub CLI download migration

- does not flag mold installer after GitHub CLI download migration
   - Expected: count_rule(source, "scripts/setup/install-mold.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag mold installer after GitHub CLI download migration")
val source = rt_file_read_text("scripts/setup/install-mold.shs")
expect(count_rule(source, "scripts/setup/install-mold.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib runtime shim check after native smoke migration

- does not flag SciLib runtime shim check after native smoke migration
   - Expected: count_rule(source, "scripts/check/check-scilib-runtime-shims.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SciLib runtime shim check after native smoke migration")
val source = rt_file_read_text("scripts/check/check-scilib-runtime-shims.shs")
expect(count_rule(source, "scripts/check/check-scilib-runtime-shims.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib runtime C smoke helper

- does not flag SciLib runtime C smoke helper
   - Expected: count_rule(source, "src/runtime/scilib/runtime_shim_smoke.c", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SciLib runtime C smoke helper")
val source = rt_file_read_text("src/runtime/scilib/runtime_shim_smoke.c")
expect(count_rule(source, "src/runtime/scilib/runtime_shim_smoke.c", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator gates after libtorch probe migration

- does not flag SciLib accelerator gates after libtorch probe migration
   - Expected: count_rule(source, "scripts/check/check-scilib-accelerator-gates.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SciLib accelerator gates after libtorch probe migration")
val source = rt_file_read_text("scripts/check/check-scilib-accelerator-gates.shs")
expect(count_rule(source, "scripts/check/check-scilib-accelerator-gates.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator perf after native smoke migration

- does not flag SciLib accelerator perf after native smoke migration
   - Expected: count_rule(source, "scripts/check/check-scilib-accelerator-perf.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SciLib accelerator perf after native smoke migration")
val source = rt_file_read_text("scripts/check/check-scilib-accelerator-perf.shs")
expect(count_rule(source, "scripts/check/check-scilib-accelerator-perf.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator perf C smoke helper

- does not flag SciLib accelerator perf C smoke helper
   - Expected: count_rule(source, "src/runtime/scilib/accelerator_perf_smoke.c", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SciLib accelerator perf C smoke helper")
val source = rt_file_read_text("src/runtime/scilib/accelerator_perf_smoke.c")
expect(count_rule(source, "src/runtime/scilib/accelerator_perf_smoke.c", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator perf CUDA helper

- does not flag SciLib accelerator perf CUDA helper
   - Expected: count_rule(source, "src/runtime/scilib/accelerator_perf_smoke_cuda.inc", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SciLib accelerator perf CUDA helper")
val source = rt_file_read_text("src/runtime/scilib/accelerator_perf_smoke_cuda.inc")
expect(count_rule(source, "src/runtime/scilib/accelerator_perf_smoke_cuda.inc", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag SciLib accelerator perf Torch helper

- does not flag SciLib accelerator perf Torch helper
   - Expected: count_rule(source, "src/runtime/scilib/accelerator_perf_smoke_torch.inc", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag SciLib accelerator perf Torch helper")
val source = rt_file_read_text("src/runtime/scilib/accelerator_perf_smoke_torch.inc")
expect(count_rule(source, "src/runtime/scilib/accelerator_perf_smoke_torch.inc", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag OS disk image builder after native migration

- does not flag OS disk image builder after native migration
   - Expected: count_rule(source, "scripts/os/make_os_disk.shs", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag OS disk image builder after native migration")
val source = rt_file_read_text("scripts/os/make_os_disk.shs")
expect(count_rule(source, "scripts/os/make_os_disk.shs", "simple_script_required")).to_equal(0)
```

</details>

#### does not flag native OS disk image builder helper

- does not flag native OS disk image builder helper
   - Expected: count_rule(source, "scripts/os/make_os_disk.c", "simple_script_required") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag native OS disk image builder helper")
val source = rt_file_read_text("scripts/os/make_os_disk.c")
expect(count_rule(source, "scripts/os/make_os_disk.c", "simple_script_required")).to_equal(0)
```

</details>

### primitive API severity

#### promotes primitive_api to deny by default

- promotes primitive_api to deny by default
   - Expected: source contains `levels["primitive_api"] = "deny"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("promotes primitive_api to deny by default")
val source = rt_file_read_text("src/compiler/90.tools/lint/_LintMain/config_and_model.spl")
expect(source.contains("levels[\"primitive_api\"] = \"deny\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/script_language_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering script language lint, primitive API severity.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c020bd5f4528036eec4db49937385212c2ba3025e7d411f7da6edc01811dcb7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c020bd5f4528036eec4db49937385212c2ba3025e7d411f7da6edc01811dcb7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c020bd5f4528036eec4db49937385212c2ba3025e7d411f7da6edc01811dcb7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/lint/script_language_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/script_language_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/lint/script_language_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/script_language_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/script_language_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/lint/script_language_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 42 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/script_language_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags Python automation scripts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/script_language_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags Python calls embedded in repository shell scripts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/script_language_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag vendored Python scripts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
