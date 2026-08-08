# Widget Showcase Perf Wrapper Contract

> Validates the retained GUI showcase performance wrapper without requiring a live 4K or 8K performance host. The wrapper is the canonical producer for `gui_showcase_4k_200fps_*` and `gui_showcase_8k_perf_*` evidence consumed by the GUI RenderDoc feature aggregate.

<!-- sdn-diagram:id=widget_showcase_perf_wrapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_showcase_perf_wrapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_showcase_perf_wrapper_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_showcase_perf_wrapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Showcase Perf Wrapper Contract

Validates the retained GUI showcase performance wrapper without requiring a live 4K or 8K performance host. The wrapper is the canonical producer for `gui_showcase_4k_200fps_*` and `gui_showcase_8k_perf_*` evidence consumed by the GUI RenderDoc feature aggregate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/widget_showcase_perf_wrapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the retained GUI showcase performance wrapper without requiring a
live 4K or 8K performance host. The wrapper is the canonical producer for
`gui_showcase_4k_200fps_*` and `gui_showcase_8k_perf_*` evidence consumed by
the GUI RenderDoc feature aggregate.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
PLAN_ONLY=1 RESOLUTION=4k sh scripts/check/check-widget-showcase-4k-200fps.shs
PLAN_ONLY=1 RESOLUTION=8k sh scripts/check/check-widget-showcase-4k-200fps.shs
```

## Operator Flow

1. Use plan-only mode first to confirm wrapper routing without compiling or
   running the expensive native showcase.
2. For the 4K evidence row, run the wrapper with `RESOLUTION=4k` and keep
   `build/widget-showcase-4k-200fps/status.env`.
3. For the 8K evidence row, run the wrapper with `RESOLUTION=8k` and keep
   `build/widget-showcase-8k-perf/status.env`.
4. Feed those env files into the GUI RenderDoc aggregate with
   `GUI_SHOWCASE_4K_PERF_ENV` and `GUI_SHOWCASE_8K_PERF_ENV`.
5. Treat plan-only output as routing evidence only. It is not completion
   evidence because timing, RSS, checksum, and readback measurement rows remain
   empty until a real run executes.

## Acceptance

- 4K plan-only evidence selects `run_4k_perf_probe`, `gui_showcase_4k_perf`,
  `SHOWCASE_4K_PERF`, 3840x2160, 200 frames, and target FPS 200.
- 8K plan-only evidence selects `run_8k_perf_probe`, `gui_showcase_8k_perf`,
  `SHOWCASE_8K_PERF`, 7680x4320, 200 frames, and target FPS 200.
- Plan-only evidence includes native provenance and marks runtime log artifact
  status as `fail` because no expensive benchmark has executed yet.
- Plan-only evidence includes the full content-revision input set for the
  wrapper, widget showcase app, 8K scroll fixture, retained scroll/dirty-region
  helpers, and Simple Web HTML layout renderer. A 4K/8K row whose digest only
  covers the launcher and app is stale and cannot prove current-source perf.
- Plan-only evidence reports the generated alias source as present while the
  native binary, native executable bit, native binary format, and native build
  log remain absent until a real native run.
- Plan-only evidence emits the same measured field keys as a real row with empty
  values for FPS, frame timing, observed RSS, checksum, nonzero readback pixels,
  render mode, redraw count, and the readback proof status fields.
- Producer `frame_elapsed_ns` is trusted only when it is positive and no larger
  than the wrapper's measured run window; impossible producer timing falls back
  to measured elapsed time and cannot make a slow probe pass 200 FPS.
- Native plan-only mode writes the generated alias source that calls the
  selected probe function directly.
- The wrapper resolves a usable Simple launcher before the legacy Rust target
  when `SIMPLE_BIN` is not explicit, and records the resolution source.
- Plan-only evidence still reports `simple_bin_status=missing` when an
  explicit `SIMPLE_BIN` path is not executable; routing-only output must not
  overstate binary validity.
- Producer artifact status fields report `symlink` or `hardlink` instead of
  `pass` when retained evidence paths are linked aliases.
- The GUI showcase app routes `SHOWCASE_8K_PERF=1` through the env facade to
  `run_8k_perf_probe()` before normal GUI startup, and does not reintroduce a
  raw `rt_env_get` shortcut.

## Evidence Contract

The full 4K row must prove:

- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_4k_200fps_width=3840`
- `gui_showcase_4k_200fps_height=2160`
- `gui_showcase_4k_200fps_pixels=8294400`
- `gui_showcase_4k_200fps_frames` is at least 200.
- `gui_showcase_4k_200fps_target_fps` is at least 200.
- `gui_showcase_4k_200fps_fps_x1000` meets the target.
- `gui_showcase_4k_200fps_frame_p50_ns` and
  `gui_showcase_4k_200fps_frame_p95_ns` are present for timing distribution
  evidence.
- `gui_showcase_4k_200fps_frame_distribution_status=pass`
- `gui_showcase_4k_200fps_nonzero_pixels` is positive.
- `gui_showcase_4k_200fps_nonzero_pixels_status=pass`
- `gui_showcase_4k_200fps_checksum` is nonempty.
- `gui_showcase_4k_200fps_checksum_status=pass`
- `gui_showcase_4k_200fps_readback_mode=argb-checksum`
- `gui_showcase_4k_200fps_render_mode=retained-static-frame`
- `gui_showcase_4k_200fps_retained_render_mode_status=pass`
- `gui_showcase_4k_200fps_redraw_frames=1`
- `gui_showcase_4k_200fps_retained_redraw_status=pass`
- `gui_showcase_4k_200fps_rss_status=pass`
- `gui_showcase_4k_200fps_source_revision_files` names the wrapper, showcase
  app, 8K scroll fixture, scroll-surface helper, dirty-region helper, and Simple
  Web HTML layout renderer.
- The showcase log and `/usr/bin/time` log exist.
- Producer-side `*_log_file_status` and `*_time_log_file_status` are `pass`.
- Producer-side `*_alias_src_file_status`, `*_native_bin_file_status`, and
  `*_native_bin_executable_status`, `*_native_bin_format_status`, and
  `*_native_build_log_file_status` prove the harness source, compiled binary,
  executable bit, recognized native binary format, and build log artifacts are
  present for native completion evidence.
- Producer-side artifact status fields are typed: `pass` means a regular
  producer-owned artifact, while `symlink` and `hardlink` are diagnostic values
  that downstream aggregate gates must reject as completion evidence.

The full 8K row has the same contract with:

- `gui_showcase_8k_perf_width=7680`
- `gui_showcase_8k_perf_height=4320`
- `gui_showcase_8k_perf_pixels=33177600`
- `gui_showcase_8k_perf_frames` is at least 200.
- `gui_showcase_8k_perf_frame_p50_ns` and
  `gui_showcase_8k_perf_frame_p95_ns` are present for timing distribution
  evidence.
- `gui_showcase_8k_perf_frame_distribution_status=pass`
- `gui_showcase_8k_perf_nonzero_pixels_status=pass`
- `gui_showcase_8k_perf_checksum_status=pass`
- `gui_showcase_8k_perf_readback_mode=argb-checksum`
- `gui_showcase_8k_perf_retained_render_mode_status=pass`
- `gui_showcase_8k_perf_retained_redraw_status=pass`
- `gui_showcase_8k_perf_source_revision_files` names the same current-source
  revision input set as the 4K row.
- Producer-side `*_log_file_status` and `*_time_log_file_status` are `pass`.

## Completion Boundary

This wrapper proves retained static-frame showcase throughput and memory budget
only. It does not prove live redraw throughput, browser GPU backing, native
Vulkan/Metal/D3D12 capture, or production GUI/web parity. Those stay under the
separate RenderDoc, platform render-log, and production parity gates.

## Failure Semantics

The wrapper fails if the probe cannot run, the native build fails, the command
times out before producing probe rows, or the readback does not match the
requested resolution. It also fails when nonzero readback pixels or checksum are
missing, when the render mode is not `retained-static-frame`, when the redraw
count is not exactly one, when the measured FPS is below target, or when the RSS
budget is exceeded. A row with `rss_status=measured` is useful diagnostics but
is not completion evidence for the aggregate gate.
Producer artifact status is fail-closed: linked retained evidence is reported as
`symlink` or `hardlink` so copied or aliased artifacts cannot be mistaken for
fresh native-run proof.

## Aggregate Consumption

The GUI RenderDoc feature aggregate forwards the status rows without launching
the expensive native benchmark. It expects:

- `GUI_SHOWCASE_4K_PERF_ENV` to point at the 4K `status.env`.
- `GUI_SHOWCASE_8K_PERF_ENV` to point at the 8K `status.env`.
- Both rows to include log paths and time-log paths.
- Both log files to exist when the aggregate marks the perf lane complete.

## Native Alias Contract

The wrapper writes a build-local alias source so the native binary enters the
selected probe directly instead of running the full showcase main. This is a
bounded perf harness alias, not a runtime shortcut. The alias must call only
`run_4k_perf_probe()` or `run_8k_perf_probe()` and preserve the original
showcase source imports and helper definitions.

## Test Matrix

The spec covers plan-only 4K and 8K routing. It verifies the selected probe
function, evidence prefix, environment flag, resolution, frame count, target
FPS, pixel count, native provenance fields, empty measured field placeholders,
plan-only log artifact status, generated native alias source, and app-level 8K
environment dispatch. It also verifies producer-side typed link statuses for
preexisting hardlinked retained artifacts.

## Scenarios

### Widget showcase retained perf wrapper

#### selects the 4K 200fps probe contract

- Run the wrapper in 4K plan-only mode
   - Expected: code equals `0`
- Assert 4K evidence and generated native alias select the 4K probe
-  expect showcase revision files


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper in 4K plan-only mode")
val command = "rm -rf build/test-widget-showcase-perf-wrapper-4k && PLAN_ONLY=1 RESOLUTION=4k BUILD_DIR=build/test-widget-showcase-perf-wrapper-4k sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert 4K evidence and generated native alias select the 4K probe")
val evidence = file_read("build/test-widget-showcase-perf-wrapper-4k/status.env")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=plan-only")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=plan-only")
expect(evidence).to_contain("gui_showcase_4k_200fps_resolution=4k")
expect(evidence).to_contain("gui_showcase_4k_200fps_probe_fn=run_4k_perf_probe")
expect(evidence).to_contain("gui_showcase_4k_200fps_probe_prefix=gui_showcase_4k_perf")
expect(evidence).to_contain("gui_showcase_4k_200fps_perf_env_flag=SHOWCASE_4K_PERF")
expect(evidence).to_contain("gui_showcase_4k_200fps_width=3840")
expect(evidence).to_contain("gui_showcase_4k_200fps_height=2160")
expect(evidence).to_contain("gui_showcase_4k_200fps_frames=200")
expect(evidence).to_contain("gui_showcase_4k_200fps_target_fps=200")
expect(evidence).to_contain("gui_showcase_4k_200fps_pixels=8294400")
expect(evidence).to_contain("gui_showcase_4k_200fps_fps_x1000=")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_avg_ns=")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_elapsed_ns_status=")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_p50_ns=")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_p95_ns=")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_distribution_status=")
expect(evidence).to_contain("gui_showcase_4k_200fps_max_rss_kb=")
expect(evidence).to_contain("gui_showcase_4k_200fps_rss_status=")
expect(evidence).to_contain("gui_showcase_4k_200fps_nonzero_pixels=")
expect(evidence).to_contain("gui_showcase_4k_200fps_nonzero_pixels_status=")
expect(evidence).to_contain("gui_showcase_4k_200fps_checksum=")
expect(evidence).to_contain("gui_showcase_4k_200fps_checksum_status=")
expect(evidence).to_contain("gui_showcase_4k_200fps_readback_mode=")
expect(evidence).to_contain("gui_showcase_4k_200fps_render_mode=")
expect(evidence).to_contain("gui_showcase_4k_200fps_retained_render_mode_status=")
expect(evidence).to_contain("gui_showcase_4k_200fps_redraw_frames=")
expect(evidence).to_contain("gui_showcase_4k_200fps_retained_redraw_status=")
expect(evidence).to_contain("gui_showcase_4k_200fps_source_revision=")
expect(evidence).to_contain("gui_showcase_4k_200fps_source_revision_kind=content-sha256")
val source_files = _value_of(evidence, "gui_showcase_4k_200fps_source_revision_files")
_expect_showcase_revision_files(source_files)
expect(evidence).to_contain("gui_showcase_4k_200fps_simple_bin=")
expect(evidence).to_contain("gui_showcase_4k_200fps_simple_bin_source=")
expect(evidence).to_contain("gui_showcase_4k_200fps_use_native=1")
expect(evidence).to_contain("gui_showcase_4k_200fps_alias_src_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_file_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_executable_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format=unknown")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_build_log_file_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_build_mode=aggressive-native")
expect(evidence).to_contain("gui_showcase_4k_200fps_fallback_state=none")
expect(evidence).to_contain("gui_showcase_4k_200fps_log_file_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_time_log_file_status=fail")

val alias_src = file_read("build/test-widget-showcase-perf-wrapper-4k/widget_showcase_4k_perf.spl")
expect(alias_src).to_contain("fn main() -> i64:")
expect(alias_src).to_contain("run_4k_perf_probe()")
```

</details>

#### selects the 8K retained perf probe contract

- Run the wrapper in 8K plan-only mode
   - Expected: code equals `0`
- Assert 8K evidence and generated native alias select the 8K probe
-  expect showcase revision files


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper in 8K plan-only mode")
val command = "rm -rf build/test-widget-showcase-perf-wrapper-8k && PLAN_ONLY=1 RESOLUTION=8k BUILD_DIR=build/test-widget-showcase-perf-wrapper-8k sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert 8K evidence and generated native alias select the 8K probe")
val evidence = file_read("build/test-widget-showcase-perf-wrapper-8k/status.env")
expect(evidence).to_contain("gui_showcase_8k_perf_status=plan-only")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=plan-only")
expect(evidence).to_contain("gui_showcase_8k_perf_resolution=8k")
expect(evidence).to_contain("gui_showcase_8k_perf_probe_fn=run_8k_perf_probe")
expect(evidence).to_contain("gui_showcase_8k_perf_probe_prefix=gui_showcase_8k_perf")
expect(evidence).to_contain("gui_showcase_8k_perf_perf_env_flag=SHOWCASE_8K_PERF")
expect(evidence).to_contain("gui_showcase_8k_perf_width=7680")
expect(evidence).to_contain("gui_showcase_8k_perf_height=4320")
expect(evidence).to_contain("gui_showcase_8k_perf_frames=200")
expect(evidence).to_contain("gui_showcase_8k_perf_target_fps=200")
expect(evidence).to_contain("gui_showcase_8k_perf_pixels=33177600")
expect(evidence).to_contain("gui_showcase_8k_perf_fps_x1000=")
expect(evidence).to_contain("gui_showcase_8k_perf_frame_avg_ns=")
expect(evidence).to_contain("gui_showcase_8k_perf_frame_elapsed_ns_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_frame_p50_ns=")
expect(evidence).to_contain("gui_showcase_8k_perf_frame_p95_ns=")
expect(evidence).to_contain("gui_showcase_8k_perf_frame_distribution_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_max_rss_kb=")
expect(evidence).to_contain("gui_showcase_8k_perf_rss_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_nonzero_pixels=")
expect(evidence).to_contain("gui_showcase_8k_perf_nonzero_pixels_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_checksum=")
expect(evidence).to_contain("gui_showcase_8k_perf_checksum_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_readback_mode=")
expect(evidence).to_contain("gui_showcase_8k_perf_render_mode=")
expect(evidence).to_contain("gui_showcase_8k_perf_retained_render_mode_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_redraw_frames=")
expect(evidence).to_contain("gui_showcase_8k_perf_retained_redraw_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_source_revision=")
expect(evidence).to_contain("gui_showcase_8k_perf_source_revision_kind=content-sha256")
val source_files = _value_of(evidence, "gui_showcase_8k_perf_source_revision_files")
_expect_showcase_revision_files(source_files)
expect(evidence).to_contain("gui_showcase_8k_perf_simple_bin=")
expect(evidence).to_contain("gui_showcase_8k_perf_simple_bin_source=")
expect(evidence).to_contain("gui_showcase_8k_perf_use_native=1")
expect(evidence).to_contain("gui_showcase_8k_perf_alias_src_file_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_file_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_executable_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_format=unknown")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_format_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_native_build_log_file_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_native_build_mode=aggressive-native")
expect(evidence).to_contain("gui_showcase_8k_perf_fallback_state=none")
expect(evidence).to_contain("gui_showcase_8k_perf_log_file_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_time_log_file_status=fail")

val alias_src = file_read("build/test-widget-showcase-perf-wrapper-8k/widget_showcase_8k_perf.spl")
expect(alias_src).to_contain("fn main() -> i64:")
expect(alias_src).to_contain("run_8k_perf_probe()")
```

</details>

#### emits retained frame p50 and p95 timing fields for real runs

- Read the wrapper source
- Assert p50 and p95 are derived from the retained timing window


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the wrapper source")
val script = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")

step("Assert p50 and p95 are derived from the retained timing window")
expect(script).to_contain("frame_elapsed_ns_status=\"$(positive_int_range_status")
expect(script).to_contain("\"$FRAMES\" \"$elapsed_ns\"")
expect(script).to_contain("frame_avg_ns=$((fps_elapsed_ns / FRAMES))")
expect(script).to_contain("frame_p50_ns=$frame_avg_ns")
expect(script).to_contain("frame_p95_ns=$frame_avg_ns")
expect(script).to_contain("frame_distribution_status=\"$(frame_distribution_status")
expect(script).to_contain("_frame_elapsed_ns_status=$frame_elapsed_ns_status")
expect(script).to_contain("_frame_p50_ns=$frame_p50_ns")
expect(script).to_contain("_frame_p95_ns=$frame_p95_ns")
expect(script).to_contain("_frame_distribution_status=$frame_distribution_status")
```

</details>

#### resolves repo simple launcher before legacy cargo target

- Read the wrapper source
- Assert resolver order and provenance evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the wrapper source")
val script = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")

step("Assert resolver order and provenance evidence")
expect(script).to_contain("for candidate in \\\n        release/x86_64-unknown-linux-gnu/simple")
expect(script.index_of("release/x86_64-unknown-linux-gnu/simple")).to_be_less_than(script.index_of("bin/simple"))
expect(script).to_contain("SIMPLE_BIN_SOURCE=\"${SIMPLE_BIN_SOURCE:-missing-self-hosted}\"")
expect(script).to_contain("SIMPLE_BIN_STATUS=missing")
expect(script).to_contain("_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### marks explicit missing Simple binary as missing in plan-only evidence

- Run the wrapper in plan-only mode with an explicit missing Simple binary
   - Expected: code equals `0`
- Assert routing evidence does not overstate binary validity
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `plan-only`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_simple_bin") equals `build/test-widget-showcase-plan-only-missing-simple/no-simple`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_simple_bin_source") equals `explicit-env`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_simple_bin_status") equals `missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper in plan-only mode with an explicit missing Simple binary")
val command = "rm -rf build/test-widget-showcase-plan-only-missing-simple && PLAN_ONLY=1 RESOLUTION=4k SIMPLE_BIN=build/test-widget-showcase-plan-only-missing-simple/no-simple BUILD_DIR=build/test-widget-showcase-plan-only-missing-simple sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert routing evidence does not overstate binary validity")
val evidence = file_read("build/test-widget-showcase-plan-only-missing-simple/status.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("plan-only")
expect(_value_of(evidence, "gui_showcase_4k_200fps_simple_bin")).to_equal("build/test-widget-showcase-plan-only-missing-simple/no-simple")
expect(_value_of(evidence, "gui_showcase_4k_200fps_simple_bin_source")).to_equal("explicit-env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_simple_bin_status")).to_equal("missing")
```

</details>

#### emits hardlink artifact statuses in plan-only producer evidence

- Create hardlinked retained artifact paths before plan-only routing
   - Expected: code equals `0`
- Assert linked artifacts are not reported as pass
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `plan-only`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_native_bin_file_status") equals `hardlink`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_native_bin_executable_status") equals `hardlink`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_native_build_log_file_status") equals `hardlink`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_log_file_status") equals `hardlink`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_time_log_file_status") equals `hardlink`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create hardlinked retained artifact paths before plan-only routing")
val command = "rm -rf build/test-widget-showcase-plan-only-hardlinks && mkdir -p build/test-widget-showcase-plan-only-hardlinks && printf '\\177ELFfake-native\\n' > build/test-widget-showcase-plan-only-hardlinks/native-original && chmod +x build/test-widget-showcase-plan-only-hardlinks/native-original && ln build/test-widget-showcase-plan-only-hardlinks/native-original build/test-widget-showcase-plan-only-hardlinks/widget_showcase_gui_perf && printf 'native build log\\n' > build/test-widget-showcase-plan-only-hardlinks/native-build-original.log && ln build/test-widget-showcase-plan-only-hardlinks/native-build-original.log build/test-widget-showcase-plan-only-hardlinks/native-build.log && printf 'showcase log\\n' > build/test-widget-showcase-plan-only-hardlinks/showcase-original.log && ln build/test-widget-showcase-plan-only-hardlinks/showcase-original.log build/test-widget-showcase-plan-only-hardlinks/showcase.log && printf 'time log\\n' > build/test-widget-showcase-plan-only-hardlinks/time-original.log && ln build/test-widget-showcase-plan-only-hardlinks/time-original.log build/test-widget-showcase-plan-only-hardlinks/time.log && PLAN_ONLY=1 RESOLUTION=4k BUILD_DIR=build/test-widget-showcase-plan-only-hardlinks sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert linked artifacts are not reported as pass")
val evidence = file_read("build/test-widget-showcase-plan-only-hardlinks/status.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("plan-only")
expect(_value_of(evidence, "gui_showcase_4k_200fps_native_bin_file_status")).to_equal("hardlink")
expect(_value_of(evidence, "gui_showcase_4k_200fps_native_bin_executable_status")).to_equal("hardlink")
expect(_value_of(evidence, "gui_showcase_4k_200fps_native_build_log_file_status")).to_equal("hardlink")
expect(_value_of(evidence, "gui_showcase_4k_200fps_log_file_status")).to_equal("hardlink")
expect(_value_of(evidence, "gui_showcase_4k_200fps_time_log_file_status")).to_equal("hardlink")
```

</details>

#### does not let impossible producer timing pass a slow retained probe

- Run a fake native probe that sleeps but claims a one-nanosecond frame window
   - Expected: code equals `1`
- Assert the wrapper rejects the impossible producer timing and uses measured elapsed time
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_reason") equals `below-200fps`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_frame_elapsed_ns") equals `1`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_frame_elapsed_ns_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_fps_elapsed_ns") == "1" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a fake native probe that sleeps but claims a one-nanosecond frame window")
val command = "rm -rf build/test-widget-showcase-impossible-frame-timing && mkdir -p build/test-widget-showcase-impossible-frame-timing && printf '%s\\n' '#!/bin/sh' 'sleep 2' 'echo gui_showcase_4k_perf_width=3840' 'echo gui_showcase_4k_perf_height=2160' 'echo gui_showcase_4k_perf_frame_elapsed_ns=1' 'echo gui_showcase_4k_perf_pixels=8294400' 'echo gui_showcase_4k_perf_nonzero_pixels=100' 'echo gui_showcase_4k_perf_checksum=123456' 'echo gui_showcase_4k_perf_render_mode=retained-static-frame' 'echo gui_showcase_4k_perf_redraw_frames=1' > build/test-widget-showcase-impossible-frame-timing/fake-native && chmod +x build/test-widget-showcase-impossible-frame-timing/fake-native && printf '%s\\n' '#!/bin/sh' 'out=' 'while [ $# -gt 0 ]; do' 'if [ $1 = --output ]; then' 'shift' 'out=$1' 'fi' 'shift || true' 'done' 'cp build/test-widget-showcase-impossible-frame-timing/fake-native $out' 'chmod +x $out' > build/test-widget-showcase-impossible-frame-timing/fake-simple && chmod +x build/test-widget-showcase-impossible-frame-timing/fake-simple && SIMPLE_BIN=build/test-widget-showcase-impossible-frame-timing/fake-simple BUILD_DIR=build/test-widget-showcase-impossible-frame-timing RESOLUTION=4k TIMEOUT_SECS=5 sh scripts/check/check-widget-showcase-4k-200fps.shs > build/test-widget-showcase-impossible-frame-timing/stdout.txt 2> build/test-widget-showcase-impossible-frame-timing/stderr.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

step("Assert the wrapper rejects the impossible producer timing and uses measured elapsed time")
val evidence = file_read("build/test-widget-showcase-impossible-frame-timing/status.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_reason")).to_equal("below-200fps")
expect(_value_of(evidence, "gui_showcase_4k_200fps_frame_elapsed_ns")).to_equal("1")
expect(_value_of(evidence, "gui_showcase_4k_200fps_frame_elapsed_ns_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_fps_elapsed_ns") == "1").to_equal(false)
```

</details>

#### rejects nonnumeric retained readback checksums at the producer

- Read the wrapper source
- Assert checksum_status fails empty or nonnumeric values


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the wrapper source")
val script = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")

step("Assert checksum_status fails empty or nonnumeric values")
expect(script).to_contain("checksum_status()")
expect(script).to_contain("\"\"|*[!0-9]*)")
expect(script).to_contain("echo fail")
expect(script).to_contain("_checksum_status=$checksum_proof_status")
expect(script).to_contain("readback_mode=argb-checksum")
expect(script).to_contain("_readback_mode=$readback_mode")
```

</details>

#### keeps the GUI showcase 8K env flag wired through the facade

- Read the GUI showcase source
- Assert 8K dispatch uses env_ops and enters the retained 8K probe
- Assert raw runtime env access stays out of the app
   - Expected: showcase does not contain `extern fn rt_env_get`
   - Expected: showcase does not contain `rt_env_get(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the GUI showcase source")
val showcase = file_read("examples/06_io/ui/widget_showcase_gui.spl")

step("Assert 8K dispatch uses env_ops and enters the retained 8K probe")
expect(showcase).to_contain("use std.nogc_sync_mut.io.env_ops.{env_get}")
expect(showcase).to_contain("fn run_8k_perf_probe() -> i64:")
expect(showcase).to_contain("run_widget_showcase_perf_probe(7680, 4320, 200, \"gui_showcase_8k_perf\")")
expect(showcase).to_contain("if (env_get(\"SHOWCASE_8K_PERF\") ?? \"\") == \"1\":")
expect(showcase).to_contain("return run_8k_perf_probe()")
expect(showcase).to_contain("val ppm_path = env_get(\"SHOWCASE_PPM\") ?? \"\"")
expect(showcase).to_contain("if (env_get(\"SIMPLE_GUI\") ?? \"\") != \"1\":")

step("Assert raw runtime env access stays out of the app")
expect(showcase.contains("extern fn rt_env_get")).to_equal(false)
expect(showcase.contains("rt_env_get(")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
