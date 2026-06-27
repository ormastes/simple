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
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Artifact Provenance Contract

Validates that retained 4K/8K GUI showcase performance completion evidence is
bound to regular artifact files. The GUI RenderDoc aggregate must not accept
symlinked showcase logs, time logs, alias sources, native binaries, or native
build logs as completion proof.

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
| Updated | 2026-06-27 |
| Generator | manual companion for `simple spipe-docgen` output |

## Overview

The retained showcase performance rows are release evidence for high-resolution
GUI rendering. A row is only trustworthy when its logs, native binary, alias
source, and native build log point at regular files. Symlinks can redirect proof
after capture, so the aggregate treats them as typed failures instead of
following them with `Path.is_file()` or executable checks.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- A retained 4K row with symlinked showcase and timing logs is normalized to
  `fail`.
- The 4K reason reports `log=symlink` and `time_log=symlink`.
- A retained 8K row with a symlinked native binary is normalized to `fail`.
- The 8K native file and executable statuses report `symlink`.
- Native binary magic is not read through the symlink, so the format status
  fails.
- The aggregate implementation remains wired to regular-file helpers for
  retained showcase performance artifacts.

## Syntax

```sh
bin/simple test test/03_system/check/gui_showcase_perf_artifact_provenance_contract_spec.spl --mode=interpreter
```

The aggregate receives one retained showcase row through
`GUI_SHOWCASE_4K_PERF_ENV` or `GUI_SHOWCASE_8K_PERF_ENV`. This contract creates
synthetic rows that otherwise satisfy timing, checksum, RSS, resolution,
retained redraw, fallback, and source revision gates so the first selected
failure is the symlinked artifact path.

## Examples

Given a 4K row whose `*_log` and `*_time_log` fields point at symlinks, the
aggregate emits `gui_showcase_4k_200fps_status=fail` with
`missing-4k-retained-log-artifacts:log=symlink;time_log=symlink`.

Given an 8K row whose `*_native_bin` field points at a symlink, the aggregate
emits `gui_showcase_8k_perf_status=fail`, marks both native file checks as
`symlink`, leaves `*_native_bin_magic` empty, and fails the native format gate.

## Fixture Shape

The fixture uses `build/test-gui-showcase-perf-artifact-provenance` and writes
real native placeholders, alias sources, native build logs, showcase logs, and
time logs. It then replaces the 4K showcase log paths with symlink references
and replaces the 8K native binary path with a symlink reference.

The status rows deliberately claim `*_file_status=pass`,
`*_native_bin_executable_status=pass`, and `*_native_bin_format_status=pass`.
The aggregate must re-check the filesystem path class and override those
status-only pass claims when the path is a symlink.

## Failure Ordering

The 4K case targets retained log provenance, so the native binary remains a
regular executable placeholder. The expected failure reason is
`missing-4k-retained-log-artifacts`.

The 8K case targets native binary provenance, so showcase and time logs remain
regular files. The expected failure reason is `missing-8k-native-artifacts`.

## Evidence Checklist

- `*_status=fail` proves symlinked artifacts cannot pass completion.
- `*_log_file_status=symlink` and `*_time_log_file_status=symlink` prove log
  path type is checked directly.
- `*_native_bin_file_status=symlink` proves native binary path type is checked
  directly.
- `*_native_bin_executable_status=symlink` proves executable validation does not
  follow the link.
- Empty `*_native_bin_magic` proves native magic is not read through the link.
- Source-wiring assertions keep the aggregate on regular-file helper paths.

## Scenarios

### GUI showcase perf artifact provenance contract

#### rejects symlinked retained showcase artifact paths

- Create retained 4K and 8K fixture rows with complete surrounding proof.
- Replace the 4K showcase and timing logs with symlink paths.
- Replace the 8K native binary with a symlink path.
- Run `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` for both
  rows.
- Assert the emitted evidence reports typed `symlink` statuses and deterministic
  failure reasons.

#### keeps the aggregate wired to regular showcase artifact checks

- Read `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`.
- Assert the regular-file helpers and symlink checks are present.
- Assert retained 4K/8K showcase artifact fields use those helpers.

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)

</details>
