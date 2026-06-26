# GUI retained performance source freshness

> Validates the aggregate RenderDoc/GUI audit contract for retained 4K and 8K performance evidence source revisions. Release-grade evidence can opt into strict freshness so stale 4K/8K rows remain diagnostics instead of completion proof.

<!-- sdn-diagram:id=gui_retained_perf_source_freshness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_retained_perf_source_freshness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_retained_perf_source_freshness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_retained_perf_source_freshness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI retained performance source freshness

Validates the aggregate RenderDoc/GUI audit contract for retained 4K and 8K performance evidence source revisions. Release-grade evidence can opt into strict freshness so stale 4K/8K rows remain diagnostics instead of completion proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md |
| Source | `test/03_system/check/gui_retained_perf_source_freshness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the aggregate RenderDoc/GUI audit contract for retained 4K and 8K
performance evidence source revisions. Release-grade evidence can opt into
strict freshness so stale 4K/8K rows remain diagnostics instead of completion
proof.

**Plan:** doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Operator Flow

1. Produce retained 4K and 8K showcase evidence with
   `scripts/check/check-widget-showcase-4k-200fps.shs`.
2. Pass the produced env files into
   `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` through
   `GUI_SHOWCASE_4K_PERF_ENV` and `GUI_SHOWCASE_8K_PERF_ENV`.
3. For release or goal-completion evidence, set
   `GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1` so stale measurements fail
   instead of being accepted as current proof.
4. Read the aggregate `evidence.env` rows before claiming a 4K or 8K pass:
   source revision status, current source revision, binary path, native build
   mode, fallback state, FPS, checksum, frame timing, and RSS status must all be
   compatible with the claim.

## Evidence Contract

The aggregate must emit these source freshness rows for retained 4K evidence:

- `gui_showcase_4k_200fps_current_source_revision`
- `gui_showcase_4k_200fps_source_revision_status`
- `gui_showcase_4k_200fps_require_current_source_revision`
- `gui_showcase_4k_200fps_alias_src_file_status`
- `gui_showcase_4k_200fps_native_bin_file_status`
- `gui_showcase_4k_200fps_native_bin_executable_status`
- `gui_showcase_4k_200fps_native_bin_format`
- `gui_showcase_4k_200fps_native_bin_format_status`
- `gui_showcase_4k_200fps_native_build_log_file_status`

The aggregate must emit the matching 8K rows:

- `gui_showcase_8k_perf_current_source_revision`
- `gui_showcase_8k_perf_source_revision_status`
- `gui_showcase_8k_perf_require_current_source_revision`
- `gui_showcase_8k_perf_alias_src_file_status`
- `gui_showcase_8k_perf_native_bin_file_status`
- `gui_showcase_8k_perf_native_bin_executable_status`
- `gui_showcase_8k_perf_native_bin_format`
- `gui_showcase_8k_perf_native_bin_format_status`
- `gui_showcase_8k_perf_native_build_log_file_status`

With strict freshness enabled, a retained row whose `source_revision` does not
match the current checkout must fail with
`stale-4k-source-revision:mismatch` or `stale-8k-source-revision:mismatch`.
The report summary must also expose `source_status` and `current_source` so a
human reviewer can identify stale performance rows without opening the raw env
file.

Explicit producer artifact statuses are claims, not authority. When a retained
row says `*_native_bin_file_status=pass`,
`*_native_bin_executable_status=pass`, or `*_native_bin_format_status=pass`,
the aggregate must still inspect the referenced file and fail completion if the
actual bytes are not a recognized native binary.

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_retained_perf_source_freshness_spec.spl --native
```

## Scenarios

### GUI retained performance source freshness

#### rejects retained perf rows that point at missing native artifacts

- Create a retained 4K performance row with missing native artifacts
   - Expected: code equals `0`
- Assert missing native artifacts fail the retained 4K row


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a retained 4K performance row with missing native artifacts")
val command = "rm -rf build/test-gui-retained-perf-missing-native-artifacts && mkdir -p build/test-gui-retained-perf-missing-native-artifacts/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-missing-native-artifacts/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-missing-native-artifacts/source/time.log && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=artifact-test\\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-missing-native-artifacts/source/missing-native.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-missing-native-artifacts/source/missing-alias.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-missing-native-artifacts/source/missing-build.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-missing-native-artifacts/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-missing-native-artifacts/source/time.log\\n' > build/test-gui-retained-perf-missing-native-artifacts/source/status4k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-missing-native-artifacts/source/status4k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-missing-native-artifacts/out REPORT_PATH=build/test-gui-retained-perf-missing-native-artifacts/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert missing native artifacts fail the retained 4K row")
val evidence = file_read("build/test-gui-retained-perf-missing-native-artifacts/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-missing-native-artifacts/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_alias_src_file_status=missing")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_file_status=missing")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_executable_status=missing")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format=unknown")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_build_log_file_status=missing")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=missing-4k-native-artifacts:alias_src=missing;native_bin=missing;native_bin_executable=missing;native_bin_format=fail;native_build_log=missing")
expect(report).to_contain("4K retained perf native artifacts: alias_src missing; native_bin missing; native_bin_executable missing; native_bin_format fail (unknown); native_build_log missing")
```

</details>

#### rejects retained perf rows whose explicit native artifact pass claims contradict the file bytes

- Create a retained 4K performance row with a chmodded text file pretending to be native
   - Expected: code equals `0`
- Assert the aggregate uses actual native binary magic over explicit pass claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a retained 4K performance row with a chmodded text file pretending to be native")
val command = "rm -rf build/test-gui-retained-perf-spoofed-native-artifact && mkdir -p build/test-gui-retained-perf-spoofed-native-artifact/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/time.log && printf 'alias4k\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/alias4k.spl && printf 'not-native\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/native4k.bin && chmod +x build/test-gui-retained-perf-spoofed-native-artifact/source/native4k.bin && printf 'native build log\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/build4k.log && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=artifact-test\\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-spoofed-native-artifact/source/native4k.bin\\ngui_showcase_4k_200fps_native_bin_file_status=pass\\ngui_showcase_4k_200fps_native_bin_executable_status=pass\\ngui_showcase_4k_200fps_native_bin_magic=7f454c46\\ngui_showcase_4k_200fps_native_bin_format=elf\\ngui_showcase_4k_200fps_native_bin_format_status=pass\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-spoofed-native-artifact/source/alias4k.spl\\ngui_showcase_4k_200fps_alias_src_file_status=pass\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-spoofed-native-artifact/source/build4k.log\\ngui_showcase_4k_200fps_native_build_log_file_status=pass\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-spoofed-native-artifact/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-spoofed-native-artifact/source/time.log\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/status4k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-spoofed-native-artifact/source/status4k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-spoofed-native-artifact/out REPORT_PATH=build/test-gui-retained-perf-spoofed-native-artifact/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate uses actual native binary magic over explicit pass claims")
val evidence = file_read("build/test-gui-retained-perf-spoofed-native-artifact/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-spoofed-native-artifact/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_executable_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format=unknown")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=missing-4k-native-artifacts:alias_src=pass;native_bin=pass;native_bin_executable=pass;native_bin_format=fail;native_build_log=pass")
expect(report).to_contain("4K retained perf native artifacts: alias_src pass; native_bin pass; native_bin_executable pass; native_bin_format fail (unknown); native_build_log pass")
```

</details>

#### rejects stale 4K and 8K retained perf rows when strict source freshness is required

- Create stale retained 4K and 8K performance evidence
   - Expected: code equals `0`
- Assert stale rows fail and expose source freshness provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create stale retained 4K and 8K performance evidence")
val command = "rm -rf build/test-gui-retained-perf-source-freshness && mkdir -p build/test-gui-retained-perf-source-freshness/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-source-freshness/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-source-freshness/source/time.log && printf 'alias4k\\n' > build/test-gui-retained-perf-source-freshness/source/alias4k.spl && printf '\\177ELFbin4k\\n' > build/test-gui-retained-perf-source-freshness/source/native4k.bin && printf 'build4k\\n' > build/test-gui-retained-perf-source-freshness/source/build4k.log && printf 'alias8k\\n' > build/test-gui-retained-perf-source-freshness/source/alias8k.spl && printf '\\177ELFbin8k\\n' > build/test-gui-retained-perf-source-freshness/source/native8k.bin && printf 'build8k\\n' > build/test-gui-retained-perf-source-freshness/source/build8k.log && chmod +x build/test-gui-retained-perf-source-freshness/source/native4k.bin build/test-gui-retained-perf-source-freshness/source/native8k.bin && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=stale-source\\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-source-freshness/source/native4k.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-source-freshness/source/alias4k.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-source-freshness/source/build4k.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-source-freshness/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-source-freshness/source/time.log\\n' > build/test-gui-retained-perf-source-freshness/source/status4k.env && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_reason=met-target-fps\\ngui_showcase_8k_perf_resolution=8k\\ngui_showcase_8k_perf_width=7680\\ngui_showcase_8k_perf_height=4320\\ngui_showcase_8k_perf_frames=200\\ngui_showcase_8k_perf_fps_x1000=201000\\ngui_showcase_8k_perf_frame_avg_ns=4975124\\ngui_showcase_8k_perf_frame_p50_ns=4975124\\ngui_showcase_8k_perf_frame_p95_ns=4975124\\ngui_showcase_8k_perf_target_fps=200\\ngui_showcase_8k_perf_max_rss_kb=524288\\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_pixels=33177600\\ngui_showcase_8k_perf_nonzero_pixels=1000\\ngui_showcase_8k_perf_checksum=123456\\ngui_showcase_8k_perf_render_mode=retained-static-frame\\ngui_showcase_8k_perf_redraw_frames=1\\ngui_showcase_8k_perf_source_revision=stale-source\\ngui_showcase_8k_perf_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_8k_perf_use_native=1\\ngui_showcase_8k_perf_native_bin=build/test-gui-retained-perf-source-freshness/source/native8k.bin\\ngui_showcase_8k_perf_alias_src=build/test-gui-retained-perf-source-freshness/source/alias8k.spl\\ngui_showcase_8k_perf_native_build_log=build/test-gui-retained-perf-source-freshness/source/build8k.log\\ngui_showcase_8k_perf_native_build_mode=aggressive-native\\ngui_showcase_8k_perf_fallback_state=none\\ngui_showcase_8k_perf_log=build/test-gui-retained-perf-source-freshness/source/showcase.log\\ngui_showcase_8k_perf_time_log=build/test-gui-retained-perf-source-freshness/source/time.log\\n' > build/test-gui-retained-perf-source-freshness/source/status8k.env && GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-source-freshness/source/status4k.env GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-retained-perf-source-freshness/source/status8k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-source-freshness/out REPORT_PATH=build/test-gui-retained-perf-source-freshness/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert stale rows fail and expose source freshness provenance")
val evidence = file_read("build/test-gui-retained-perf-source-freshness/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-source-freshness/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_current_source_revision=")
expect(evidence).to_contain("gui_showcase_4k_200fps_source_revision_status=mismatch")
expect(evidence).to_contain("gui_showcase_4k_200fps_require_current_source_revision=1")
expect(evidence).to_contain("gui_showcase_4k_200fps_alias_src_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_executable_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format=elf")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_build_log_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=stale-4k-source-revision:mismatch")
expect(evidence).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_current_source_revision=")
expect(evidence).to_contain("gui_showcase_8k_perf_source_revision_status=mismatch")
expect(evidence).to_contain("gui_showcase_8k_perf_require_current_source_revision=1")
expect(evidence).to_contain("gui_showcase_8k_perf_alias_src_file_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_file_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_executable_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_format=elf")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_format_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_build_log_file_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=stale-8k-source-revision:mismatch")
expect(report).to_contain("source_status mismatch")
expect(report).to_contain("current_source")
expect(report).to_contain("4K retained perf native artifacts: alias_src pass; native_bin pass; native_bin_executable pass; native_bin_format pass (elf); native_build_log pass")
expect(report).to_contain("8K retained perf native artifacts: alias_src pass; native_bin pass; native_bin_executable pass; native_bin_format pass (elf); native_build_log pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md](doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md)


</details>
