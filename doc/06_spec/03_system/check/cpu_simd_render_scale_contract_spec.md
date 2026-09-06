# CPU SIMD Render Scale Contract

> The scale wrapper is the focused evidence gate for CPU-SIMD rendering at 4K and 8K. This spec keeps the wrapper honest without running full 8K inside the test: the source check guards the report fields, and the executable check overrides dimensions to a tiny fixture while preserving the same code path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU SIMD Render Scale Contract

The scale wrapper is the focused evidence gate for CPU-SIMD rendering at 4K and 8K. This spec keeps the wrapper honest without running full 8K inside the test: the source check guards the report fields, and the executable check overrides dimensions to a tiny fixture while preserving the same code path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | REQ-CPU-SIMD-SCALE-001 through REQ-CPU-SIMD-SCALE-013 |
| Plan | doc/07_guide/platform/gui_perf_benchmark_comparison.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/cpu_simd_render_scale_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The scale wrapper is the focused evidence gate for CPU-SIMD rendering at 4K and
8K. This spec keeps the wrapper honest without running full 8K inside the test:
the source check guards the report fields, and the executable check overrides
dimensions to a tiny fixture while preserving the same code path.

## Requirements

**Requirements:** REQ-CPU-SIMD-SCALE-001 through REQ-CPU-SIMD-SCALE-013

- REQ-CPU-SIMD-SCALE-001: The scale wrapper emits CPU-SIMD and software p50/p95
  frame timing fields for the 4K and 8K rows.
- REQ-CPU-SIMD-SCALE-002: The scale wrapper emits a neutral p50 ratio field so
  reports can compare CPU-SIMD against the scalar software baseline without
  inventing a pass threshold.
- REQ-CPU-SIMD-SCALE-003: The wrapper emits `gui_perf_cpu_base_compare_*`
  fields for the focused CPU-SIMD vs scalar software baseline row.
- REQ-CPU-SIMD-SCALE-004: The wrapper remains runnable at small overridden
  dimensions for fast contract verification.
- REQ-CPU-SIMD-SCALE-005: The executable contract records native mode,
  default 300dpi retina density, and sample count so reports cannot pass with
  interpreter fallback or DPI drift.
- REQ-CPU-SIMD-SCALE-006: The wrapper records the CPU-SIMD/scalar run order so
  benchmark scheduling is explicit and can be reversed for follow-up evidence.
- REQ-CPU-SIMD-SCALE-007: The wrapper reports whether the selected production
  binary links the Engine2D SIMD row externs and can require that in strict mode.
- REQ-CPU-SIMD-SCALE-008: The wrapper reports whether runtime sources changed
  after the selected production binary and can require freshness in strict mode.
- REQ-CPU-SIMD-SCALE-009: The wrapper can require the canonical Engine2D SIMD
  arch matrix and expose x86_64, AArch64, and RISC-V target-binary pass fields
  without rerunning render benchmarks.
- REQ-CPU-SIMD-SCALE-010: CPU-SIMD rows require positive provider/native hits,
  while scalar software rows require zero SIMD hits.
- REQ-CPU-SIMD-SCALE-011: Native CLI dimensions, DPI, and sample counts retain
  their parsed values when narrowed to `i32`.
- REQ-CPU-SIMD-SCALE-012: Strict architecture evidence rejects any missing
  x86_64, AArch64, or RISC-V target result.
- REQ-CPU-SIMD-SCALE-013: Strict native-probe mode rejects a missing artifact.

## Plan

**Plan:** doc/07_guide/platform/gui_perf_benchmark_comparison.md

1. Inspect the scale wrapper for retained timing and ratio fields.
2. Run the wrapper with tiny overridden dimensions.
3. Confirm the no-reduction, checksum parity, and comparison fields are present.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper uses the same `backend_measurement_software_export.spl` harness for
CPU-SIMD and scalar rows. The harness passes the configured backend through the
canonical Simple Web renderer before comparing checksum and timing metadata.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_render_scale_contract_spec.spl --mode=interpreter --clean
```

The strict architecture rejection scenarios share this executable helper:

```simple
use std.spec.step

fn _arch_matrix_result(name: text, x86: text, aarch64: text, riscv64: text) -> (text, i64):
    val root = "build/test-cpu-simd-render-scale-arch-matrix-" + name
    val env_path = root + "/evidence.env"
    val command =
        "rm -rf " + root + " && mkdir -p " + root +
        " && printf '%s\\n' " +
        "'cpu_simd_engine2d_arch_matrix_status=pass' " +
        "'cpu_simd_engine2d_arch_matrix_x86_64_target_binary_status=" + x86 + "' " +
        "'cpu_simd_engine2d_arch_matrix_aarch64_target_binary_status=" + aarch64 + "' " +
        "'cpu_simd_engine2d_arch_matrix_riscv64_target_binary_status=" + riscv64 + "' > " + env_path +
        " && CPU_SIMD_RENDER_SCALE_ARCH_MATRIX_ONLY=1" +
        " CPU_SIMD_RENDER_SCALE_REQUIRE_ARCH_MATRIX=1" +
        " CPU_SIMD_RENDER_SCALE_ARCH_MATRIX_ENV=" + env_path +
        " sh scripts/check/check-cpu-simd-render-scale-contract.shs > " + root + "/stdout.txt"
    val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
    (file_read(root + "/stdout.txt"), code)
```

## Scenarios

### CPU SIMD render scale contract

#### exports software baseline timing comparison fields through a real run

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- run the software exporter on both backends and require timing, ratio and parity fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CPU-SIMD-SCALE-001
# @req REQ-CPU-SIMD-SCALE-002
# @req REQ-CPU-SIMD-SCALE-003
# @req REQ-CPU-SIMD-SCALE-010
# @req REQ-SSPEC-SYSTEM
step("run the software exporter on both backends and require timing, ratio and parity fields")
val simd_out = _run_export("cpu_simd")
val soft_out = _run_export("software")
for out in [simd_out, soft_out]:
    expect(out).to_contain("p50_frame_us: ")  # oracle: timing fields are measured, not absent
    expect(out).to_contain("p95_frame_us: ")  # oracle: p95 tail timing is recorded
# REQ-001..003 are asserted on the contract gate output in the
# "runs small dimensions and keeps comparison fields" scenario below.
```

</details>

#### external cpu drawing baseline comparison records benchmark scope

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- run the external benchmark runner at tiny dimensions and read the recorded scope fields
   - Expected: _value_of(out, "gui_perf_cpu_base_compare_source") equals `gui_perf_bench_external_cpu_library`
   - Expected: _value_of(out, "gui_perf_cpu_base_compare_pixels") equals `8x8`
   - Expected: _value_of(out, "gui_perf_cpu_base_compare_dpi") equals `300`
   - Expected: _value_of(out, "gui_perf_cpu_base_compare_frames") equals `1`
   - Expected: _value_of(out, "gui_perf_cpu_base_compare_simple_mode") equals `native`
   - Expected: _value_of(out, "gui_perf_cpu_base_compare_simple_launch_kind") equals `run`
   - Expected: _value_of(out, "gui_perf_cpu_base_compare_simple_native_artifact_used") equals `false`
   - Expected: _value_of(out, "gui_perf_cpu_base_compare_schedule_order") equals `cpu_simd_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run the external benchmark runner at tiny dimensions and read the recorded scope fields")
val root = "build/test-cpu-simd-render-scale-bench-scope"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && BUILD_DIR=" + root + "/build REPORT_PATH=" + root + "/report.md" +
    " WIDTH=8 HEIGHT=8 FRAMES=1 DPI=300" +
    " bash tools/gui_perf_bench/run_all_benchmarks.shs > " + root + "/stdout.txt 2>&1"
val (_stdout, _stderr, _code) = process_run("/bin/sh", ["-c", command])
val out = file_read(root + "/stdout.txt")
expect(_value_of(out, "gui_perf_cpu_base_compare_source")).to_equal("gui_perf_bench_external_cpu_library")  # oracle: the baseline comes from the external CPU library, not a synthetic source
expect(_value_of(out, "gui_perf_cpu_base_compare_pixels")).to_equal("8x8")  # oracle: recorded pixel scope matches the tiny probe dimensions
expect(_value_of(out, "gui_perf_cpu_base_compare_dpi")).to_equal("300")  # oracle: DPI is recorded
expect(_value_of(out, "gui_perf_cpu_base_compare_frames")).to_equal("1")  # oracle: frame count is recorded
expect(_value_of(out, "gui_perf_cpu_base_compare_simple_mode")).to_equal("native")  # oracle: the mode lane is recorded
expect(_value_of(out, "gui_perf_cpu_base_compare_simple_launch_kind")).to_equal("run")  # oracle: launched via simple run, not a cached artifact
expect(_value_of(out, "gui_perf_cpu_base_compare_simple_native_artifact_used")).to_equal("false")  # oracle: no native artifact was claimed
expect(_value_of(out, "gui_perf_cpu_base_compare_schedule_order")).to_equal("cpu_simd_first")  # oracle: run order is explicit
```

</details>

#### software exporter routes the configured backend through the shared Draw IR executor

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- same fixture, two backends: identical checksums prove one shared Draw IR route; counters prove SIMD routing
   - Expected: _sample_field(simd_out, "runtime_execution_path") equals `simple_web_layout_engine2d_cpu_simd`
   - Expected: _sample_field(soft_out, "runtime_execution_path") equals `simple_web_layout_software`
   - Expected: _sample_field(simd_out, "requested") equals `cpu_simd`
   - Expected: _sample_field(soft_out, "requested") equals `software`
   - Expected: _sample_field(simd_out, "checksum") equals `_sample_field(soft_out, "checksum")`
   - Expected: _sample_field(simd_out, "simd_provider_hits") != "0" is true
   - Expected: _sample_field(simd_out, "native_simd_executed") equals `true`
   - Expected: _sample_field(soft_out, "simd_provider_hits") equals `0`
   - Expected: _sample_field(soft_out, "native_simd_executed") equals `false`
   - Expected: _value_of(simd_out, "gui_perf_benchmark_simd_provider_hits") != "0" is true
   - Expected: _value_of(simd_out, "gui_perf_benchmark_native_simd_executed") equals `true`
   - Expected: _value_of(soft_out, "gui_perf_benchmark_native_simd_executed") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CPU-SIMD-SCALE-004
# @req REQ-SSPEC-SYSTEM
step("same fixture, two backends: identical checksums prove one shared Draw IR route; counters prove SIMD routing")
val simd_out = _run_export("cpu_simd")
val soft_out = _run_export("software")
expect(_sample_field(simd_out, "runtime_execution_path")).to_equal("simple_web_layout_engine2d_cpu_simd")  # oracle: cpu_simd routes through the Engine2D CPU SIMD executor
expect(_sample_field(soft_out, "runtime_execution_path")).to_equal("simple_web_layout_software")  # oracle: software routes through the scalar baseline
expect(_sample_field(simd_out, "requested")).to_equal("cpu_simd")  # oracle: the configured backend is honored, not swapped
expect(_sample_field(soft_out, "requested")).to_equal("software")
expect(_sample_field(simd_out, "checksum")).to_equal(_sample_field(soft_out, "checksum"))  # oracle: shared Draw IR means byte-identical pixels
expect(_sample_field(simd_out, "simd_provider_hits") != "0").to_equal(true)  # oracle: CPU-SIMD rows carry positive provider hits
expect(_sample_field(simd_out, "native_simd_executed")).to_equal("true")  # oracle: SIMD rows executed natively
expect(_sample_field(soft_out, "simd_provider_hits")).to_equal("0")  # oracle: scalar rows carry zero SIMD hits
expect(_sample_field(soft_out, "native_simd_executed")).to_equal("false")  # oracle: scalar rows never executed SIMD
expect(_value_of(simd_out, "gui_perf_benchmark_simd_provider_hits") != "0").to_equal(true)
expect(_value_of(simd_out, "gui_perf_benchmark_native_simd_executed")).to_equal("true")
expect(_value_of(soft_out, "gui_perf_benchmark_native_simd_executed")).to_equal("false")
```

</details>

#### typed software exporter reports true nearest rank percentiles

**Manual warnings:**
- invalid capture metadata value: bit_table (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- run one sample: nearest-rank p50 and p95 must both be exactly that sample
   - Expected: _sample_field(out, "sample_count") equals `1`
   - Expected: _sample_field(out, "p50_frame_us") equals `_sample_field(out, "cold_start_us")`
   - Expected: _sample_field(out, "p95_frame_us") equals `_sample_field(out, "cold_start_us")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run one sample: nearest-rank p50 and p95 must both be exactly that sample")
val out = _run_export("software")
expect(_sample_field(out, "sample_count")).to_equal("1")  # oracle: single-sample run isolates nearest-rank behavior
expect(_sample_field(out, "p50_frame_us")).to_equal(_sample_field(out, "cold_start_us"))  # oracle: nearest rank of one sample is the sample
expect(_sample_field(out, "p95_frame_us")).to_equal(_sample_field(out, "cold_start_us"))  # oracle: p95 of one sample is the sample, never a clamp or zero
```

</details>

#### fills a 1M-pixel framebuffer through the native repeat path with every pixel set

**Manual warnings:**
- invalid capture metadata value: bit_table (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- render at 1024x1024: the native fill path must set all 1048576 pixels
   - Expected: code equals `0`
   - Expected: _sample_field(out, "pixel_proof") equals `nonzero_pixels:1048576`
   - Expected: _sample_field(out, "checksum") != "" is true
   - Expected: _sample_field(out, "native_simd_executed") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render at 1024x1024: the native fill path must set all 1048576 pixels")
val root = "build/test-cpu-simd-render-scale-1mp"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && bin/simple run src/app/wm_compare/backend_measurement_software_export.spl" +
    " --width 1024 --height 1024 --sample-count 1 --software-render-backend cpu_simd" +
    " > " + root + "/stdout.txt 2>&1"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)  # oracle: the 1M-pixel render must complete
val out = file_read(root + "/stdout.txt")
expect(_sample_field(out, "pixel_proof")).to_equal("nonzero_pixels:1048576")  # oracle: every pixel of the 2^20 framebuffer is written
expect(_sample_field(out, "checksum") != "").to_equal(true)  # oracle: a checksum over the full buffer exists
expect(_sample_field(out, "native_simd_executed")).to_equal("true")  # oracle: the SIMD fill kernels executed
```

</details>

#### browser layout framebuffers use the safe owner fill facade

**Manual warnings:**
- invalid capture metadata value: bit_table (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- render the canonical fixture: the owner fill facade writes every framebuffer pixel
   - Expected: _sample_field(out, "pixel_proof") equals `nonzero_pixels:256`
   - Expected: _sample_field(out, "fallback_used") equals `false`
   - Expected: _sample_field(out, "status") equals `Initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render the canonical fixture: the owner fill facade writes every framebuffer pixel")
val out = _run_export("software")
expect(_sample_field(out, "pixel_proof")).to_equal("nonzero_pixels:256")  # oracle: all 16x16 pixels written by the fill facade
expect(_sample_field(out, "fallback_used")).to_equal("false")  # oracle: no fallback path was taken
expect(_sample_field(out, "status")).to_equal("Initialized")  # oracle: the render loop reached its ready state
```

</details>

#### runs small dimensions and keeps comparison fields

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- runs small dimensions and keeps comparison fields
- Render canonical HTML through the CPU SIMD Draw IR route
   - Expected: code equals `0`
- Render the same fixture through the scalar route
- Compare pixels and SIMD counters


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs small dimensions and keeps comparison fields")
step("Render canonical HTML through the CPU SIMD Draw IR route")
val root = "build/test-cpu-simd-render-scale-contract"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && SIMPLE_BIN='" + _test_simple_bin() + "'" +
    " CPU_SIMD_RENDER_SCALE_4K_WIDTH=16 CPU_SIMD_RENDER_SCALE_4K_HEIGHT=16" +
    " CPU_SIMD_RENDER_SCALE_8K_WIDTH=32 CPU_SIMD_RENDER_SCALE_8K_HEIGHT=32" +
    " CPU_SIMD_RENDER_SCALE_RUN_ORDER=software_first CPU_SIMD_RENDER_SCALE_SAMPLE_COUNT=1 OUT_DIR=" + root + "/out" +
    " sh scripts/check/check-cpu-simd-render-scale-contract.shs > " + root + "/stdout.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)  # oracle: gate must exit green

step("Render the same fixture through the scalar route")
val out = file_read(root + "/stdout.txt")
expect(out).to_contain("cpu_simd_render_scale_contract_status=pass")
expect(out).to_contain("cpu_simd_render_scale_contract_mode=native")
expect(out).to_contain("cpu_simd_render_scale_contract_dpi=300")
expect(out).to_contain("cpu_simd_render_scale_contract_dpi_source=default")
expect(out).to_contain("cpu_simd_render_scale_contract_sample_count=1")
expect(out).to_contain("cpu_simd_render_scale_contract_run_order=software_first")
expect(out).to_contain("cpu_simd_render_scale_engine2d_binary_link_status=")
expect(out).to_contain("cpu_simd_render_scale_engine2d_binary_link_required=0")
expect(out).to_contain("cpu_simd_render_scale_runtime_source_fresh_status=")
expect(out).to_contain("cpu_simd_render_scale_runtime_source_fresh_required=0")
expect(out).to_contain("cpu_simd_render_scale_4k_pixels=16x16")
expect(out).to_contain("cpu_simd_render_scale_8k_pixels=32x32")
expect(out).to_contain("cpu_simd_render_scale_4k_software_p50_frame_us=")
expect(out).to_contain("cpu_simd_render_scale_8k_software_p50_frame_us=")
expect(out).to_contain("cpu_simd_render_scale_4k_vs_software_p50_ratio_permille=")
expect(out).to_contain("cpu_simd_render_scale_8k_vs_software_p50_ratio_permille=")
expect(out).to_contain("gui_perf_cpu_base_compare_status=measured")
expect(out).to_contain("gui_perf_cpu_base_compare_pixels=32x32")
expect(out).to_contain("gui_perf_cpu_base_compare_simple_backend=simple_web_cpu_simd")
expect(out).to_contain("gui_perf_cpu_base_compare_baseline_backend=simple_web_software")
expect(out).to_contain("gui_perf_cpu_base_compare_schedule_order=software_first")
expect(out).to_contain("gui_perf_cpu_base_compare_target_met=")
expect(out).to_contain("gui_perf_cpu_base_compare_simd_provider_hits=")
expect(out).to_contain("gui_perf_cpu_base_compare_native_simd_executed=")
step("Compare pixels and SIMD counters")
expect(out).to_contain("cpu_simd_render_scale_4k_software_checksum_parity=true")
expect(out).to_contain("cpu_simd_render_scale_8k_software_checksum_parity=true")
```

</details>

#### runs small dimensions with an explicit dpi override

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- runs small dimensions with an explicit dpi override
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs small dimensions with an explicit dpi override")
val root = "build/test-cpu-simd-render-scale-contract-dpi-override"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && SIMPLE_BIN='" + _test_simple_bin() + "'" +
    " CPU_SIMD_RENDER_SCALE_4K_WIDTH=8 CPU_SIMD_RENDER_SCALE_4K_HEIGHT=8" +
    " CPU_SIMD_RENDER_SCALE_8K_WIDTH=16 CPU_SIMD_RENDER_SCALE_8K_HEIGHT=16" +
    " CPU_SIMD_RENDER_SCALE_DPI=220 CPU_SIMD_RENDER_SCALE_SAMPLE_COUNT=1 OUT_DIR=" + root + "/out" +
    " sh scripts/check/check-cpu-simd-render-scale-contract.shs > " + root + "/stdout.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)  # oracle: gate must exit green

val out = file_read(root + "/stdout.txt")
expect(out).to_contain("cpu_simd_render_scale_contract_status=pass")
expect(out).to_contain("cpu_simd_render_scale_contract_dpi=220")
expect(out).to_contain("cpu_simd_render_scale_contract_dpi_source=override")
expect(out).to_contain("cpu_simd_render_scale_4k_pixels=8x8")
expect(out).to_contain("cpu_simd_render_scale_8k_pixels=16x16")
```

</details>

<details>
<summary>Advanced: requires arch matrix target binaries without rerunning render benchmarks</summary>

#### requires arch matrix target binaries without rerunning render benchmarks

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- requires arch matrix target binaries without rerunning render benchmarks
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires arch matrix target binaries without rerunning render benchmarks")
val root = "build/test-cpu-simd-render-scale-arch-matrix-only"
val env_path = root + "/evidence.env"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && printf '%s\\n' " +
    "'cpu_simd_engine2d_arch_matrix_status=pass' " +
    "'cpu_simd_engine2d_arch_matrix_x86_64_target_binary_status=pass' " +
    "'cpu_simd_engine2d_arch_matrix_aarch64_target_binary_status=pass' " +
    "'cpu_simd_engine2d_arch_matrix_riscv64_target_binary_status=pass' > " + env_path +
    " && CPU_SIMD_RENDER_SCALE_ARCH_MATRIX_ONLY=1" +
    " CPU_SIMD_RENDER_SCALE_REQUIRE_ARCH_MATRIX=1" +
    " CPU_SIMD_RENDER_SCALE_ARCH_MATRIX_ENV=" + env_path +
    " sh scripts/check/check-cpu-simd-render-scale-contract.shs > " + root + "/stdout.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)  # oracle: gate must exit green

val out = file_read(root + "/stdout.txt")
expect(out).to_contain("cpu_simd_render_scale_contract_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_required=1")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_x86_64_target_binary_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_aarch64_target_binary_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_riscv64_target_binary_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_only=1")
```

</details>


</details>

#### rejects a missing x86_64 target result

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- rejects a missing x86_64 target result
- Validate strict architecture evidence
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a missing x86_64 target result")
step("Validate strict architecture evidence")
val (out, code) = _arch_matrix_result("x86-missing", "missing", "pass", "pass")
expect(code).to_equal(1)  # oracle: gate must reject the missing/failing lane
expect(out).to_contain("arch_matrix_x86_64_target_binary_expected_pass_got_missing")
```

</details>

#### rejects a missing AArch64 target result

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- rejects a missing AArch64 target result
- Validate strict architecture evidence
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a missing AArch64 target result")
step("Validate strict architecture evidence")
val (out, code) = _arch_matrix_result("aarch64-missing", "pass", "missing", "pass")
expect(code).to_equal(1)  # oracle: gate must reject the missing/failing lane
expect(out).to_contain("arch_matrix_aarch64_target_binary_expected_pass_got_missing")
```

</details>

#### rejects a missing RISC-V target result

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- rejects a missing RISC-V target result
- Validate strict architecture evidence
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a missing RISC-V target result")
step("Validate strict architecture evidence")
val (out, code) = _arch_matrix_result("riscv-missing", "pass", "pass", "missing")
expect(code).to_equal(1)  # oracle: gate must reject the missing/failing lane
expect(out).to_contain("arch_matrix_riscv64_target_binary_expected_pass_got_missing")
```

</details>

#### rejects a required native probe that is absent

- rejects a required native probe that is absent
- Validate strict native probe evidence
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a required native probe that is absent")
step("Validate strict native probe evidence")
val root = "build/test-cpu-simd-render-scale-native-probe-missing"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && CPU_SIMD_RENDER_SCALE_PROBE_ONLY=1" +
    " CPU_SIMD_RENDER_SCALE_REQUIRE_NATIVE_PROBE=1" +
    " CPU_SIMD_RENDER_SCALE_NATIVE_PROBE_BIN=" + root + "/missing" +
    " OUT_DIR=" + root + "/out" +
    " sh scripts/check/check-cpu-simd-render-scale-contract.shs > " + root + "/stdout.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)  # oracle: gate must reject the missing/failing lane
expect(file_read(root + "/stdout.txt")).to_contain("native_probe_missing")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-CPU-SIMD-SCALE-001 through REQ-CPU-SIMD-SCALE-013`
- **Plan:** `doc/07_guide/platform/gui_perf_benchmark_comparison.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-CPU-SIMD-SCALE-001`
- `REQ-CPU-SIMD-SCALE-013`
- `REQ-CPU-SIMD-SCALE-001:`
- `REQ-CPU-SIMD-SCALE-002:`
- `REQ-CPU-SIMD-SCALE-003:`
- `REQ-CPU-SIMD-SCALE-004:`
- `REQ-CPU-SIMD-SCALE-005:`
- `REQ-CPU-SIMD-SCALE-006:`
- `REQ-CPU-SIMD-SCALE-007:`
- `REQ-CPU-SIMD-SCALE-008:`
- `REQ-CPU-SIMD-SCALE-009:`
- `REQ-CPU-SIMD-SCALE-010:`
- `REQ-CPU-SIMD-SCALE-011:`
- `REQ-CPU-SIMD-SCALE-012:`
- `REQ-CPU-SIMD-SCALE-013:`
- `REQ-CPU-SIMD-SCALE-002`
- `REQ-CPU-SIMD-SCALE-003`
- `REQ-CPU-SIMD-SCALE-010`
- `REQ-001..003`
- `REQ-CPU-SIMD-SCALE-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `051cadd9a8cb075cd8f0bd4281f8ccc92c972a938a20c97687f6b6dcaca762e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `051cadd9a8cb075cd8f0bd4281f8ccc92c972a938a20c97687f6b6dcaca762e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `051cadd9a8cb075cd8f0bd4281f8ccc92c972a938a20c97687f6b6dcaca762e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/03_system/check/cpu_simd_render_scale_contract_spec.spl
mirror: doc/06_spec/03_system/check/cpu_simd_render_scale_contract_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/cpu_simd_render_scale_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/cpu_simd_render_scale_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/cpu_simd_render_scale_contract_spec.spl:378:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a required native probe that is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
