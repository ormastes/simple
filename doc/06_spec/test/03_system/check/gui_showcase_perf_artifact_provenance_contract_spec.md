# GUI Showcase Perf Artifact Provenance Contract

> Validates that retained 4K/8K GUI showcase performance completion evidence is bound to regular artifact files. The GUI RenderDoc aggregate must not accept symlinked showcase logs, time logs, alias sources, native binaries, or native build logs as completion proof.

<!-- sdn-diagram:id=gui_showcase_perf_artifact_provenance_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_showcase_perf_artifact_provenance_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_showcase_perf_artifact_provenance_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_showcase_perf_artifact_provenance_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Artifact Provenance Contract

Validates that retained 4K/8K GUI showcase performance completion evidence is bound to regular artifact files. The GUI RenderDoc aggregate must not accept symlinked showcase logs, time logs, alias sources, native binaries, or native build logs as completion proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_artifact_provenance_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that retained 4K/8K GUI showcase performance completion evidence is
bound to regular artifact files. The GUI RenderDoc aggregate must not accept
symlinked showcase logs, time logs, alias sources, native binaries, or native
build logs as completion proof.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
bin/simple test test/03_system/check/gui_showcase_perf_artifact_provenance_contract_spec.spl --mode=interpreter
```

## Acceptance

- A complete retained 4K performance row with a symlinked time log fails with a
  typed `time_log=symlink` reason.
- A complete retained 8K performance row with a symlinked native binary fails
  with typed `native_bin=symlink` and executable `symlink` rows.
- The aggregate implementation uses regular-file checks for showcase
  performance artifact paths and does not read native binary magic through
  symlinks.
- The retained perf producer prefers release/self-hosted binaries before
  repo-bin shims so native perf evidence does not depend on a slower or stale
  launcher.

## Scenarios

### GUI showcase perf artifact provenance contract

#### rejects symlinked retained showcase artifact paths

- "printf 'fn main
   - Expected: code equals `0`
- Confirm symlinked 4K retained logs cannot satisfy perf completion
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_log_file_status") equals `symlink`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_time_log_file_status") equals `symlink`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_reason") equals `missing-4k-retained-log-artifacts:log=symlink;time_log=symlink`
- Confirm symlinked 8K native binaries cannot satisfy native provenance
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_file_status") equals `symlink`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_executable_status") equals `symlink`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_magic") equals ``
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_format_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_reason") equals `missing-8k-native-artifacts:alias_src=pass;native_bin=symlink;native_bin_exec... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-showcase-perf-artifact-provenance"
val setup = "rm -rf " + root + " && mkdir -p " + root + "/4k " + root + "/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/4k/native-real.bin && chmod +x " + root + "/4k/native-real.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/8k/native-real.bin && chmod +x " + root + "/8k/native-real.bin && ln -s native-real.bin " + root + "/8k/native-link.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > " + root + "/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > " + root + "/8k/showcase.spl && " +
    "printf 'native build log\\n' > " + root + "/4k/build.log && printf 'native build log\\n' > " + root + "/8k/build.log && " +
    "printf 'showcase retained log\\n' > " + root + "/4k/showcase-real.log && ln -s showcase-real.log " + root + "/4k/showcase.log && " +
    "printf 'elapsed_ms=597\\n' > " + root + "/4k/time-real.log && ln -s time-real.log " + root + "/4k/time.log && " +
    "printf 'showcase retained log\\n' > " + root + "/8k/showcase.log && printf 'elapsed_ms=597\\n' > " + root + "/8k/time.log && "
val write_4k = _fixture_command(root, "4k", root + "/4k/native-real.bin", root + "/4k/showcase.spl", root + "/4k/build.log", root + "/4k/showcase.log", root + "/4k/time.log")
val write_8k = _fixture_command(root, "8k", root + "/8k/native-link.bin", root + "/8k/showcase.spl", root + "/8k/build.log", root + "/8k/showcase.log", root + "/8k/time.log")
val command = setup + write_4k + " && " + write_8k + " && " +
    "GUI_SHOWCASE_4K_PERF_ENV=" + root + "/4k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-4k REPORT_PATH=" + root + "/report-4k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs && " +
    "GUI_SHOWCASE_8K_PERF_ENV=" + root + "/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-8k REPORT_PATH=" + root + "/report-8k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val four_k = file_read(root + "/out-4k/evidence.env")
val eight_k = file_read(root + "/out-8k/evidence.env")
step("Confirm symlinked 4K retained logs cannot satisfy perf completion")
expect(_value_of(four_k, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(four_k, "gui_showcase_4k_200fps_log_file_status")).to_equal("symlink")
expect(_value_of(four_k, "gui_showcase_4k_200fps_time_log_file_status")).to_equal("symlink")
expect(_value_of(four_k, "gui_showcase_4k_200fps_reason")).to_equal("missing-4k-retained-log-artifacts:log=symlink;time_log=symlink")

step("Confirm symlinked 8K native binaries cannot satisfy native provenance")
expect(_value_of(eight_k, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_file_status")).to_equal("symlink")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_executable_status")).to_equal("symlink")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_magic")).to_equal("")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_format_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_reason")).to_equal("missing-8k-native-artifacts:alias_src=pass;native_bin=symlink;native_bin_executable=symlink;native_bin_format=fail;native_build_log=pass")
```

</details>

#### keeps the aggregate wired to regular showcase artifact checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")
expect(script).to_contain("def regular_file_status")
expect(script).to_contain("path.is_symlink()")
expect(script).to_contain("def evidence_regular_file_status")
expect(script).to_contain("def evidence_regular_executable_status")
expect(script).to_contain("showcase_4k_log_file_status = regular_file_status(showcase_4k_log)")
expect(script).to_contain("showcase_8k_time_log_file_status = regular_file_status(showcase_8k_time_log)")
expect(script).to_contain("showcase_4k_native_bin_file_status = evidence_regular_file_status")
expect(script).to_contain("showcase_8k_native_bin_executable_status = evidence_regular_executable_status")
```

</details>

#### prefers release self-hosted binaries before repo-bin shims for retained perf producer evidence

- Assert default discovery tries release/self-hosted binaries before bin/simple
- Assert release paths are labelled as self-hosted perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")
step("Assert default discovery tries release/self-hosted binaries before bin/simple")
expect(script).to_contain("for candidate in \\\n        release/x86_64-unknown-linux-gnu/simple")
expect(script).to_contain("bin/release/x86_64-apple-darwin/simple \\\n        bin/simple")

step("Assert release paths are labelled as self-hosted perf evidence")
expect(script).to_contain("release/*|bin/release/*) SIMPLE_BIN_SOURCE=\"self-hosted-release\"")
expect(script).to_contain("*) SIMPLE_BIN_SOURCE=\"repo-bin\"")
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

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
