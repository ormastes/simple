# GUI Widget Showcase 4K/8K Perf Contract

> Validates the source-level contract for the retained GUI widget showcase performance checker. This spec is headless-safe: it reads the checker source and asserts the required evidence fields, but it does not run the 4K/8K showcase benchmark, launch a GUI, or produce new performance claims.

<!-- sdn-diagram:id=widget_showcase_4k_8k_perf_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_showcase_4k_8k_perf_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_showcase_4k_8k_perf_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_showcase_4k_8k_perf_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Widget Showcase 4K/8K Perf Contract

Validates the source-level contract for the retained GUI widget showcase performance checker. This spec is headless-safe: it reads the checker source and asserts the required evidence fields, but it does not run the 4K/8K showcase benchmark, launch a GUI, or produce new performance claims.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/05_perf/gui/widget_showcase_4k_8k_perf_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the source-level contract for the retained GUI widget showcase
performance checker. This spec is headless-safe: it reads the checker source
and asserts the required evidence fields, but it does not run the 4K/8K
showcase benchmark, launch a GUI, or produce new performance claims.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/05_perf/gui/widget_showcase_4k_8k_perf_contract_spec.spl --mode=interpreter --clean
```

## Bounded subprocess boundary

```simple
use std.spec.*
use std.io_runtime.{file_read}
use app.io.mod.{process_run_timeout}

fn process_run(cmd: text, args: [text]) -> (text, text, i32):
    process_run_timeout(cmd, args, 120000)
```

## Acceptance

- The checker rejects Rust seed Simple binaries.
- The checker searches self-hosted Simple binaries before optional PATH lookup.
- 4K evidence keeps 3840x2160 geometry, 200fps target, checksum/readback, RSS,
  retained render mode, and redraw-count rows.
- 8K evidence keeps 7680x4320 geometry, 200fps target, checksum/readback, RSS,
  retained render mode, and redraw-count rows.
- The retained alias is generated through Simple source/build paths rather than
  adding raw `rt_*` shortcuts to the performance contract.
- The generated retained alias fails closed before native-build if raw `rt_*`
  calls enter the alias source.
- Native-build output must be a regular executable native binary before the
  checker runs it.
- Real rows require an explicit SHA-pinned v2 baseline with matching resolution,
  timestamped artifact SHA, and a bucket derived from exact producer-owned
  machine/runtime/executable/protocol fields. Median/p95 may regress by at most 10% and RSS by at
  most 5%; the aggregate recomputes these limits independently.

## Scenarios

### GUI widget showcase 4K and 8K retained perf contract

#### keeps self-hosted binary and retained evidence rows mandatory

- Read the retained showcase checker
- Assert self-hosted Simple binary selection and Rust seed rejection
- Assert 4K and 8K geometry and target FPS are explicit
- Assert retained performance evidence rows are emitted
- Assert retained alias and source revision evidence stay visible
- Assert invalid native-build artifacts fail before benchmark execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 87 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the retained showcase checker")
val script = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")

step("Assert self-hosted Simple binary selection and Rust seed rejection")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("ALLOW_PATH_SIMPLE_BIN")
expect(script).to_contain("rust-seed-simple-binary-forbidden")
expect(script).to_contain("src/compiler_rust/*|*/src/compiler_rust/*")
expect(script).to_contain("release-self-hosted-simple-binary-required")

step("Assert 4K and 8K geometry and target FPS are explicit")
expect(script).to_contain("WIDTH=3840")
expect(script).to_contain("HEIGHT=2160")
expect(script).to_contain("WIDTH=7680")
expect(script).to_contain("HEIGHT=4320")
expect(script).to_contain("TARGET_FPS=200")
expect(script).to_contain("STATUS_PREFIX=gui_showcase_4k_200fps")
expect(script).to_contain("STATUS_PREFIX=gui_showcase_8k_perf")

step("Assert retained performance evidence rows are emitted")
expect(script).to_contain("_simple_bin_status=")
expect(script).to_contain("_native_bin_file_status=")
expect(script).to_contain("_native_bin_executable_status=")
expect(script).to_contain("_native_bin_format_status=")
expect(script).to_contain("_fps_x1000=")
expect(script).to_contain("_backend=$BENCHMARK_BACKEND")
expect(script).to_contain("_frame_p50_ns=")
expect(script).to_contain("_frame_p95_ns=")
expect(script).to_contain("_checksum=")
expect(script).to_contain("_checksum_status=")
expect(script).to_contain("_max_rss_kb=")
expect(script).to_contain("_max_rss_budget_kb=")
expect(script).to_contain("_rss_status=")
expect(script).to_contain("_render_mode=")
expect(script).to_contain("_retained_render_mode_status=")
expect(script).to_contain("_redraw_frames=")
expect(script).to_contain("_retained_redraw_status=")
expect(script).to_contain("_log_file_status=pass")
expect(script).to_contain("_time_log_file_status=pass")

step("Assert retained alias and source revision evidence stay visible")
expect(script).to_contain("Generated retained-perf alias")
expect(script).to_contain("alias_raw_rt_count()")
expect(script).to_contain("validate_alias_source()")
expect(script).to_contain("alias-raw-rt-forbidden")
expect(script).to_contain("_alias_raw_rt_count=")
expect(script).to_contain("native-build --source src --source examples")
expect(script).to_contain("_source_revision=")
expect(script).to_contain("_source_revision_kind=content-sha256")
expect(script).to_contain("_source_revision_files=")
expect(script).to_contain("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
expect(script).to_contain("src/lib/gc_async_mut/gpu/engine2d/backend_software.spl")

step("Assert invalid native-build artifacts fail before benchmark execution")
expect(script).to_contain("validate_native_binary()")
expect(script).to_contain("native-bin-artifact-invalid")
expect(script).to_contain("native_file_status")
expect(script).to_contain("native_executable_status")
expect(script).to_contain("native_format_status")
expect(script).to_contain("[ ! -f \"$1\" ] || [ ! -s \"$1\" ]")
expect(script).to_contain("[ ! -f \"$1\" ] || [ ! -x \"$1\" ]")
expect(script).to_contain("validate_native_binary || exit 1")

step("Assert immutable historical-baseline evidence and fixed NFR-006 limits")
expect(script).to_contain("GUI_SHOWCASE_PERF_BASELINE_ENV")
expect(script).to_contain("GUI_SHOWCASE_PERF_BASELINE_SHA256")
expect(script).to_contain("GUI_SHOWCASE_PERF_EXECUTABLE_SHA256")
expect(script).to_contain("canonical_bucket()")
expect(script).to_contain("PERF_TIMING_PROTOCOL=retained-static-present-monotonic-ns-v1")
expect(script).to_contain("revalidate_perf_baseline()")
expect(script).to_contain("baseline-artifact-changed-before-pass")
expect(script).to_contain("[ -L \"$1\" ]")
expect(script).to_contain("[ \"$link_count\" -gt 1 ]")
expect(script).to_contain("baseline_capture_timestamp")
expect(script).to_contain("baseline_artifact_sha256")
expect(script).to_contain("source-revision-override-forbidden")
expect(script).to_contain("BASELINE_FRAME_DELTA_PERCENT=10")
expect(script).to_contain("BASELINE_RSS_DELTA_PERCENT=5")
expect(script).to_contain("stale-baseline-sha256-mismatch")
expect(script).to_contain("baseline-bucket-mismatch")
expect(script).to_contain("p95-regression-exceeded")
expect(script).to_contain("rss-regression-exceeded")
expect(script).to_contain("_baseline_source_revision=")
expect(script).to_contain("_baseline_frame_p95_delta_bp=")
```

</details>

#### proves the generated retained alias has no raw runtime calls in plan-only mode

- Run the checker in 4K plan-only mode without native build or GUI execution
   - Expected: code equals `0`
- Run the checker in 8K plan-only mode without native build or GUI execution
   - Expected: code_8k equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the checker in 4K plan-only mode without native build or GUI execution")
val command = "rm -rf build/test-widget-showcase-4k-plan-only && PLAN_ONLY=1 USE_NATIVE=1 RESOLUTION=4k BUILD_DIR=build/test-widget-showcase-4k-plan-only sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
expect(stdout).to_contain("gui_showcase_4k_200fps_status=plan-only")
expect(stdout).to_contain("gui_showcase_4k_200fps_backend=simple-retained-widget-showcase")
expect(stdout).to_contain("gui_showcase_4k_200fps_alias_src_file_status=pass")
expect(stdout).to_contain("gui_showcase_4k_200fps_alias_raw_rt_count=0")

step("Run the checker in 8K plan-only mode without native build or GUI execution")
val command_8k = "rm -rf build/test-widget-showcase-8k-plan-only && PLAN_ONLY=1 USE_NATIVE=1 RESOLUTION=8k BUILD_DIR=build/test-widget-showcase-8k-plan-only sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (stdout_8k, _stderr_8k, code_8k) = process_run("/bin/sh", ["-c", command_8k])
expect(code_8k).to_equal(0)
expect(stdout_8k).to_contain("gui_showcase_8k_perf_status=plan-only")
expect(stdout_8k).to_contain("gui_showcase_8k_perf_backend=simple-retained-widget-showcase")
expect(stdout_8k).to_contain("gui_showcase_8k_perf_alias_src_file_status=pass")
expect(stdout_8k).to_contain("gui_showcase_8k_perf_alias_raw_rt_count=0")
```

</details>

#### rejects explicit Rust seed binaries before retained perf evidence can pass

- Run the 4K checker with an explicit Rust seed Simple binary
   - Expected: code_4k equals `0`
- Run the 8K checker with an explicit Rust seed Simple binary
   - Expected: code_8k equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the 4K checker with an explicit Rust seed Simple binary")
val command_4k = "rm -rf build/test-widget-showcase-4k-seed-forbidden && PLAN_ONLY=1 USE_NATIVE=1 RESOLUTION=4k SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=build/test-widget-showcase-4k-seed-forbidden sh scripts/check/check-widget-showcase-4k-200fps.shs || true"
val (_stdout_4k, _stderr_4k, code_4k) = process_run("/bin/sh", ["-c", command_4k])
expect(code_4k).to_equal(0)
val evidence_4k = file_read("build/test-widget-showcase-4k-seed-forbidden/status.env")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_reason=rust-seed-simple-binary-forbidden")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_simple_bin_status=forbidden")

step("Run the 8K checker with an explicit Rust seed Simple binary")
val command_8k = "rm -rf build/test-widget-showcase-8k-seed-forbidden && PLAN_ONLY=1 USE_NATIVE=1 RESOLUTION=8k SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=build/test-widget-showcase-8k-seed-forbidden sh scripts/check/check-widget-showcase-4k-200fps.shs || true"
val (_stdout_8k, _stderr_8k, code_8k) = process_run("/bin/sh", ["-c", command_8k])
expect(code_8k).to_equal(0)
val evidence_8k = file_read("build/test-widget-showcase-8k-seed-forbidden/status.env")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_reason=rust-seed-simple-binary-forbidden")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_simple_bin_status=forbidden")
```

</details>

#### rejects repo launcher binaries before real retained perf runs

- Run the 4K checker outside plan-only with an explicit repo launcher
   - Expected: the evidence fails with `release-self-hosted-simple-binary-required`
- Run the 8K checker outside plan-only with an explicit repo launcher
   - Expected: the evidence fails with `release-self-hosted-simple-binary-required`

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the 4K checker outside plan-only with an explicit repo launcher")
val command_4k = "rm -rf build/test-widget-showcase-4k-repo-bin-forbidden && USE_NATIVE=1 RESOLUTION=4k SIMPLE_BIN=bin/simple SIMPLE_BIN_SOURCE=repo-bin BUILD_DIR=build/test-widget-showcase-4k-repo-bin-forbidden sh scripts/check/check-widget-showcase-4k-200fps.shs || true"
val (_stdout_4k, _stderr_4k, code_4k) = process_run("/bin/sh", ["-c", command_4k])
expect(code_4k).to_equal(0)
val evidence_4k = file_read("build/test-widget-showcase-4k-repo-bin-forbidden/status.env")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_reason=release-self-hosted-simple-binary-required")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_simple_bin=bin/simple")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_simple_bin_source=repo-bin")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_simple_bin_status=forbidden")

step("Run the 8K checker outside plan-only with an explicit repo launcher")
val command_8k = "rm -rf build/test-widget-showcase-8k-repo-bin-forbidden && USE_NATIVE=1 RESOLUTION=8k SIMPLE_BIN=bin/simple SIMPLE_BIN_SOURCE=repo-bin BUILD_DIR=build/test-widget-showcase-8k-repo-bin-forbidden sh scripts/check/check-widget-showcase-4k-200fps.shs || true"
val (_stdout_8k, _stderr_8k, code_8k) = process_run("/bin/sh", ["-c", command_8k])
expect(code_8k).to_equal(0)
val evidence_8k = file_read("build/test-widget-showcase-8k-repo-bin-forbidden/status.env")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_reason=release-self-hosted-simple-binary-required")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_simple_bin=bin/simple")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_simple_bin_source=repo-bin")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_simple_bin_status=forbidden")
```

</details>

#### fails closed for missing, mismatched, and regressed historical baselines

- Admit a hash-pinned 4K fixture within the selected NFR-006 limits.
- Reject the 3 ms to 4.8 ms p95 false-green despite the 5 ms absolute budget.
- Reject median/RSS regressions, stale or duplicate baseline input, and
  canonical identity or resolution mismatch; admit a matching 8K fixture.
- Require the aggregate to reject a forged producer PASS independently.
- Reject producer revision overrides on real paths; aggregate overrides are
  ignored unless explicit fixture mode is active, which cannot complete a row.


<details>
<summary>Executable SSpec</summary>

Runnable source: 79 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create one immutable 4K baseline fixture and validate an in-budget comparison")
val root = "build/test-widget-showcase-historical-baseline"
val create = "rm -rf " + root + " && mkdir -p " + root + " && cp test/fixtures/gui/widget_showcase_perf_baseline_4k.env " + root + "/baseline.env && sha256sum " + root + "/baseline.env | awk '{print $1}'"
val (sha_out, _sha_err, sha_code) = process_run("/bin/sh", ["-c", create])
expect(sha_code).to_equal(0)
val sha = sha_out.trim()
val identity = " GUI_SHOWCASE_PERF_OS=linux GUI_SHOWCASE_PERF_ARCH=x86_64 GUI_SHOWCASE_PERF_CPU=test-cpu GUI_SHOWCASE_PERF_GPU=test-gpu GUI_SHOWCASE_PERF_DRIVER=test-driver GUI_SHOWCASE_PERF_COMPILER=simple-test GUI_SHOWCASE_PERF_RUNTIME=software-retained GUI_SHOWCASE_PERF_EXECUTABLE_SHA256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val base_env = "PERF_BASELINE_VALIDATE_ONLY=1 SOURCE_REVISION=accepted-rev RESOLUTION=4k SIMPLE_BIN=release/x86_64-unknown-linux-gnu/simple SIMPLE_BIN_SOURCE=self-hosted-release BUILD_DIR=" + root + "/out GUI_SHOWCASE_PERF_BASELINE_ENV=" + root + "/baseline.env GUI_SHOWCASE_PERF_BASELINE_SHA256=" + sha + identity + " CURRENT_FPS_X1000=220000"
val (pass_out, _pass_err, pass_code) = process_run("/bin/sh", ["-c", base_env + " CURRENT_FRAME_P50_NS=2700000 CURRENT_FRAME_P95_NS=3200000 CURRENT_MAX_RSS_KB=104000 sh scripts/check/check-widget-showcase-4k-200fps.shs"])
expect(pass_code).to_equal(0)
expect(pass_out).to_contain("gui_showcase_4k_200fps_baseline_status=pass")
expect(pass_out).to_contain("gui_showcase_4k_200fps_baseline_frame_p95_limit_ns=3300000")

step("Reject source revision overrides on real producer paths while fixture validation remains explicit")
val (override_out, _override_err, override_code) = process_run("/bin/sh", ["-c", "PLAN_ONLY=1 SOURCE_REVISION=forged-revision SOURCE_REVISION_FILES=test/fixtures/gui/widget_showcase_perf_baseline_4k.env RESOLUTION=4k BUILD_DIR=" + root + "/override sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(override_code).to_equal(0)
expect(override_out).to_contain("gui_showcase_4k_200fps_reason=source-revision-override-forbidden")
expect(pass_out).to_contain("gui_showcase_4k_200fps_source_revision_override_status=fixture")

step("Reject the 3ms to 4.8ms false-green even though 4.8ms remains below the absolute 5ms budget")
val (p95_out, _p95_err, p95_code) = process_run("/bin/sh", ["-c", base_env + " BUILD_DIR=" + root + "/p95 CURRENT_FRAME_P50_NS=2700000 CURRENT_FRAME_P95_NS=4800000 CURRENT_MAX_RSS_KB=104000 sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(p95_code).to_equal(0)
expect(p95_out).to_contain("gui_showcase_4k_200fps_status=fail")
expect(p95_out).to_contain("gui_showcase_4k_200fps_reason=p95-regression-exceeded")

step("Reject median or RSS beyond tolerance and a mismatched canonical producer identity")
val (median_out, _median_err, median_code) = process_run("/bin/sh", ["-c", base_env + " BUILD_DIR=" + root + "/median CURRENT_FRAME_P50_NS=2800000 CURRENT_FRAME_P95_NS=3200000 CURRENT_MAX_RSS_KB=104000 sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(median_code).to_equal(0)
expect(median_out).to_contain("gui_showcase_4k_200fps_reason=median-regression-exceeded")
val (rss_out, _rss_err, rss_code) = process_run("/bin/sh", ["-c", base_env + " BUILD_DIR=" + root + "/rss CURRENT_FRAME_P50_NS=2700000 CURRENT_FRAME_P95_NS=3200000 CURRENT_MAX_RSS_KB=106000 sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(rss_code).to_equal(0)
expect(rss_out).to_contain("gui_showcase_4k_200fps_reason=rss-regression-exceeded")
val (bucket_out, _bucket_err, bucket_code) = process_run("/bin/sh", ["-c", base_env + " BUILD_DIR=" + root + "/bucket GUI_SHOWCASE_PERF_GPU=other-gpu CURRENT_FRAME_P50_NS=2700000 CURRENT_FRAME_P95_NS=3200000 CURRENT_MAX_RSS_KB=104000 sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(bucket_code).to_equal(0)
expect(bucket_out).to_contain("gui_showcase_4k_200fps_reason=baseline-bucket-mismatch")

step("Reject missing baseline input before any benchmark is launched")
val (missing_out, _missing_err, missing_code) = process_run("/bin/sh", ["-c", "PERF_BASELINE_VALIDATE_ONLY=1 RESOLUTION=4k SIMPLE_BIN=release/x86_64-unknown-linux-gnu/simple SIMPLE_BIN_SOURCE=self-hosted-release BUILD_DIR=" + root + "/missing" + identity + " CURRENT_FRAME_P50_NS=2700000 CURRENT_FRAME_P95_NS=3200000 CURRENT_FPS_X1000=220000 CURRENT_MAX_RSS_KB=104000 sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(missing_code).to_equal(0)
expect(missing_out).to_contain("gui_showcase_4k_200fps_reason=missing-baseline-path")

step("Reject stale SHA, duplicate schema, and wrong resolution; admit the matching 8K fixture")
val (stale_out, _stale_err, stale_code) = process_run("/bin/sh", ["-c", base_env + " BUILD_DIR=" + root + "/stale GUI_SHOWCASE_PERF_BASELINE_SHA256=cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc CURRENT_FRAME_P50_NS=2700000 CURRENT_FRAME_P95_NS=3200000 CURRENT_MAX_RSS_KB=104000 sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(stale_code).to_equal(0)
expect(stale_out).to_contain("gui_showcase_4k_200fps_reason=stale-baseline-sha256-mismatch")
val duplicate = "test/fixtures/gui/widget_showcase_perf_baseline_duplicate_4k.env"
val (dup_sha_out, _dup_sha_err, dup_sha_code) = process_run("/bin/sh", ["-c", "sha256sum " + duplicate + " | awk '{print $1}'"])
expect(dup_sha_code).to_equal(0)
val (dup_out, _dup_err, dup_code) = process_run("/bin/sh", ["-c", base_env + " BUILD_DIR=" + root + "/duplicate GUI_SHOWCASE_PERF_BASELINE_ENV=" + duplicate + " GUI_SHOWCASE_PERF_BASELINE_SHA256=" + dup_sha_out.trim() + " CURRENT_FRAME_P50_NS=2700000 CURRENT_FRAME_P95_NS=3200000 CURRENT_MAX_RSS_KB=104000 sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(dup_code).to_equal(0)
expect(dup_out).to_contain("gui_showcase_4k_200fps_reason=invalid-baseline-schema")
val (resolution_out, _resolution_err, resolution_code) = process_run("/bin/sh", ["-c", base_env + " RESOLUTION=8k BUILD_DIR=" + root + "/resolution CURRENT_FRAME_P50_NS=5200000 CURRENT_FRAME_P95_NS=6200000 CURRENT_MAX_RSS_KB=410000 sh scripts/check/check-widget-showcase-4k-200fps.shs || true"])
expect(resolution_code).to_equal(0)
expect(resolution_out).to_contain("gui_showcase_8k_perf_reason=baseline-resolution-mismatch")
val (sha8_out, _sha8_err, sha8_code) = process_run("/bin/sh", ["-c", "sha256sum test/fixtures/gui/widget_showcase_perf_baseline_8k.env | awk '{print $1}'"])
expect(sha8_code).to_equal(0)
val identity8 = " GUI_SHOWCASE_PERF_OS=linux GUI_SHOWCASE_PERF_ARCH=x86_64 GUI_SHOWCASE_PERF_CPU=test-cpu GUI_SHOWCASE_PERF_GPU=test-gpu GUI_SHOWCASE_PERF_DRIVER=test-driver GUI_SHOWCASE_PERF_COMPILER=simple-test GUI_SHOWCASE_PERF_RUNTIME=software-retained GUI_SHOWCASE_PERF_EXECUTABLE_SHA256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
val validate8 = "PERF_BASELINE_VALIDATE_ONLY=1 SOURCE_REVISION=accepted-rev-8k RESOLUTION=8k SIMPLE_BIN=release/x86_64-unknown-linux-gnu/simple SIMPLE_BIN_SOURCE=self-hosted-release BUILD_DIR=" + root + "/8k GUI_SHOWCASE_PERF_BASELINE_ENV=test/fixtures/gui/widget_showcase_perf_baseline_8k.env GUI_SHOWCASE_PERF_BASELINE_SHA256=" + sha8_out.trim() + identity8 + " CURRENT_FRAME_P50_NS=5200000 CURRENT_FRAME_P95_NS=6200000 CURRENT_FPS_X1000=202000 CURRENT_MAX_RSS_KB=410000 sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (eight_out, _eight_err, eight_code) = process_run("/bin/sh", ["-c", validate8])
expect(eight_code).to_equal(0)
expect(eight_out).to_contain("gui_showcase_8k_perf_baseline_status=pass")

step("Reject forged producer PASS by independently recomputing the aggregate baseline comparison")
val forged = "GUI_RENDERDOC_AGGREGATE_FIXTURE_MODE=1 GUI_SHOWCASE_CURRENT_SOURCE_REVISION=accepted-rev GUI_SHOWCASE_4K_PERF_ENV=test/fixtures/gui/widget_showcase_perf_forged_pass_4k.env GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1 BUILD_DIR=" + root + "/aggregate REPORT_PATH=" + root + "/aggregate.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_forged_out, _forged_err, forged_code) = process_run("/bin/sh", ["-c", forged])
expect(forged_code).to_equal(0)
val aggregate = file_read(root + "/aggregate/evidence.env")
expect(aggregate).to_contain("gui_showcase_4k_200fps_status=fail")
expect(aggregate).to_contain("gui_showcase_4k_200fps_reason=p95-regression-exceeded")
expect(aggregate).to_contain("gui_showcase_4k_200fps_baseline_aggregate_status=fail")
expect(aggregate).to_contain("gui_showcase_current_source_revision_override_status=fixture")

step("Ignore aggregate current-revision overrides outside explicit fixture mode")
val real_override = "GUI_SHOWCASE_CURRENT_SOURCE_REVISION=forged-revision GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1 BUILD_DIR=" + root + "/aggregate-real-override REPORT_PATH=" + root + "/aggregate-real-override.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_real_out, _real_err, real_code) = process_run("/bin/sh", ["-c", real_override])
expect(real_code).to_equal(0)
val real_aggregate = file_read(root + "/aggregate-real-override/evidence.env")
expect(real_aggregate).to_contain("gui_showcase_current_source_revision_override_status=ignored")
expect(real_aggregate.contains("gui_showcase_4k_200fps_current_source_revision=forged-revision")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
