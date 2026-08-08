# GUI RenderDoc aggregate cache modes

> This SSpec validates the aggregate audit cache split used by the GUI/Web/2D completion criteria. The seeded cache can be shared as read-only while misses are written to a per-run cache, preventing completion checks from mutating shared evidence.

<!-- sdn-diagram:id=gui_renderdoc_aggregate_cache_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_renderdoc_aggregate_cache_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_renderdoc_aggregate_cache_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_renderdoc_aggregate_cache_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI RenderDoc aggregate cache modes

This SSpec validates the aggregate audit cache split used by the GUI/Web/2D completion criteria. The seeded cache can be shared as read-only while misses are written to a per-run cache, preventing completion checks from mutating shared evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_renderdoc_aggregate_cache_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec validates the aggregate audit cache split used by the GUI/Web/2D
completion criteria. The seeded cache can be shared as read-only while misses
are written to a per-run cache, preventing completion checks from mutating
shared evidence.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_renderdoc_aggregate_cache_modes_spec.spl --mode=interpreter --clean --fail-fast
```

## Cache Contract

The aggregate audit supports two cache inputs for nested status gates:

- `GUI_RENDERDOC_AGGREGATE_READONLY_STATIC_CACHE_DIR` is a seeded cache. The
  aggregate may copy evidence from this tree into the current build output, but
  must not populate it during this run.
- `GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR` is the writable cache. When no
  seeded entry exists, the aggregate may run the nested gate and store the
  result under this path.

This split lets the GUI/Web/2D completion criteria use expensive precomputed
evidence without allowing concurrent agents to overwrite shared cache entries.
The completion SSpec can keep per-run build directories and per-run writable
caches while still reading stable seeded evidence quickly.

## Scenario Setup

The test uses the aggregate script's self-test mode instead of launching
RenderDoc, Electron, Chrome, or platform GPU tools. The self-test creates a
read-only seed for `cache-selftest-readonly`, then asks the aggregate nested
gate helper to resolve it. If lookup order is correct, the nested command for
that gate is not used and the emitted source is `readonly`.

The same self-test then resolves `cache-selftest-writable` without a read-only
seed. That path must execute the nested command and populate only the writable
cache. The emitted source is `writable`, and the writable cache evidence file
must exist.

## Expected Evidence

The generated `evidence.env` must include:

- `aggregate_cache_selftest_status=pass`
- `aggregate_cache_selftest_reason=pass`
- `aggregate_cache_selftest_readonly_source=readonly`
- `aggregate_cache_selftest_writable_source=writable`
- `aggregate_cache_selftest_writable_cache_file_status=pass`

The config self-test must also prove:

- `aggregate_cache_config_selftest_status=pass`
- disabling the default cache with no explicit writable cache leaves static
  cache status `unset`
- disabling the default cache with an explicit writable cache keeps static cache
  status `explicit`

## Failure Meaning

`readonly-cache-not-preferred` means a seeded cache entry was ignored or a
writable cache entry shadowed it. That is unsafe for shared completion evidence.

`writable-cache-miss-not-populated` means cache misses no longer populate the
per-run writable cache. That would make isolated completion runs cold and can
reintroduce the timeout recorded in
`doc/08_tracking/bug/gui_web_2d_completion_static_cache_isolation_timeout_2026-06-28.md`.

`cache-dirs-missing` means the caller did not provide both cache roots. The
GUI/Web/2D completion SSpec should always provide both.

## Non-Goals

This test does not prove platform GPU capture, RenderDoc artifact validity, or
4K/8K frame-rate performance. Those remain covered by the broader completion
criteria and by live platform runs. This test only protects the aggregate
cache behavior needed for concurrent, headless completion evidence checks.

## Operator Notes

Run this spec after changing `run_nested_gate`, aggregate cache environment
variables, or the GUI/Web/2D completion criteria's cache setup. A pass here is
required before claiming the completion SSpec is isolated from shared mutable
cache writes.

## Troubleshooting

If the self-test fails, inspect these files first:

- `build/test-gui-renderdoc-aggregate-cache-modes/out/evidence.env`
- `build/test-gui-renderdoc-aggregate-cache-modes/readonly-cache/cache-selftest-readonly/evidence.env`
- `build/test-gui-renderdoc-aggregate-cache-modes/writable-cache/cache-selftest-writable/evidence.env`

The read-only cache file should contain `aggregate_cache_selftest_readonly_source=readonly`.
The writable cache file should contain `aggregate_cache_selftest_writable_source=writable`.
If the writable file is missing, the nested command may not have received the
expected `BUILD_DIR` environment. If the read-only source is `writable`, the
lookup order has regressed and the seeded cache no longer wins.

Do not replace this test with the full GUI/Web/2D completion SSpec. The full
completion SSpec is useful end-to-end evidence, but this test is intentionally
small so cache regressions fail quickly and with a narrow error.

## Scenarios

### GUI RenderDoc aggregate cache modes

#### prefers read-only seeded cache and writes misses to per-run cache

- Run the aggregate cache self-test with separate read-only and writable caches
   - Expected: code equals `0`
- Assert read-only hits are used and writable misses populate only the writable cache
   - Expected: value_of(evidence, "aggregate_cache_selftest_status") equals `pass`
   - Expected: value_of(evidence, "aggregate_cache_selftest_reason") equals `pass`
   - Expected: value_of(evidence, "aggregate_cache_selftest_readonly_source") equals `readonly`
   - Expected: value_of(evidence, "aggregate_cache_selftest_writable_source") equals `writable`
   - Expected: value_of(evidence, "aggregate_cache_selftest_writable_cache_file_status") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the aggregate cache self-test with separate read-only and writable caches")
val root = "build/test-gui-renderdoc-aggregate-cache-modes"
val command = "rm -rf " + root + " && " +
    "GUI_RENDERDOC_AGGREGATE_CACHE_SELFTEST=1 " +
    "GUI_RENDERDOC_AGGREGATE_READONLY_STATIC_CACHE_DIR=" + root + "/readonly-cache " +
    "GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=" + root + "/writable-cache " +
    "BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md " +
    "sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert read-only hits are used and writable misses populate only the writable cache")
val evidence = file_read(root + "/out/evidence.env")
expect(value_of(evidence, "aggregate_cache_selftest_status")).to_equal("pass")
expect(value_of(evidence, "aggregate_cache_selftest_reason")).to_equal("pass")
expect(value_of(evidence, "aggregate_cache_selftest_readonly_source")).to_equal("readonly")
expect(value_of(evidence, "aggregate_cache_selftest_writable_source")).to_equal("writable")
expect(value_of(evidence, "aggregate_cache_selftest_writable_cache_file_status")).to_equal("pass")
```

</details>

#### disables default shared cache while preserving explicit per-run cache

- Run config self-test with the default shared cache disabled and no explicit cache
- Assert disabling the default cache leaves no shared static cache
   - Expected: value_of(disabled_evidence, "aggregate_cache_config_selftest_status") equals `pass`
   - Expected: value_of(disabled_evidence, "aggregate_cache_config_disable_default") equals `1`
   - Expected: value_of(disabled_evidence, "aggregate_cache_config_static_cache_status") equals `unset`
   - Expected: value_of(disabled_evidence, "aggregate_cache_config_readonly_cache_status") equals `unset`
- Run config self-test with an explicit per-run writable cache
- Assert explicit per-run cache remains available when default cache is disabled
   - Expected: value_of(explicit_evidence, "aggregate_cache_config_selftest_status") equals `pass`
   - Expected: value_of(explicit_evidence, "aggregate_cache_config_disable_default") equals `1`
   - Expected: value_of(explicit_evidence, "aggregate_cache_config_static_cache_status") equals `explicit`
   - Expected: value_of(explicit_evidence, "aggregate_cache_config_static_cache_path") contains `root + "/explicit-cache"`
   - Expected: value_of(explicit_evidence, "aggregate_cache_config_readonly_cache_status") equals `unset`

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run config self-test with the default shared cache disabled and no explicit cache")
val root = "build/test-gui-renderdoc-aggregate-cache-config"
val disabled_command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "GUI_RENDERDOC_AGGREGATE_CACHE_CONFIG_SELFTEST=1 " +
    "GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1 " +
    "BUILD_DIR=" + root + "/disabled-out REPORT_PATH=" + root + "/disabled-report.md " +
    "sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_disabled_stdout, _disabled_stderr, disabled_code) = process_run("/bin/sh", ["-c", disabled_command])
expect(disabled_code).to_equal(0)

step("Assert disabling the default cache leaves no shared static cache")
val disabled_evidence = file_read(root + "/disabled-out/evidence.env")
expect(value_of(disabled_evidence, "aggregate_cache_config_selftest_status")).to_equal("pass")
expect(value_of(disabled_evidence, "aggregate_cache_config_disable_default")).to_equal("1")
expect(value_of(disabled_evidence, "aggregate_cache_config_static_cache_status")).to_equal("unset")
expect(value_of(disabled_evidence, "aggregate_cache_config_readonly_cache_status")).to_equal("unset")

step("Run config self-test with an explicit per-run writable cache")
val explicit_command =
    "GUI_RENDERDOC_AGGREGATE_CACHE_CONFIG_SELFTEST=1 " +
    "GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1 " +
    "GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=" + root + "/explicit-cache " +
    "BUILD_DIR=" + root + "/explicit-out REPORT_PATH=" + root + "/explicit-report.md " +
    "sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_explicit_stdout, _explicit_stderr, explicit_code) = process_run("/bin/sh", ["-c", explicit_command])
expect(explicit_code).to_equal(0)

step("Assert explicit per-run cache remains available when default cache is disabled")
val explicit_evidence = file_read(root + "/explicit-out/evidence.env")
expect(value_of(explicit_evidence, "aggregate_cache_config_selftest_status")).to_equal("pass")
expect(value_of(explicit_evidence, "aggregate_cache_config_disable_default")).to_equal("1")
expect(value_of(explicit_evidence, "aggregate_cache_config_static_cache_status")).to_equal("explicit")
expect(value_of(explicit_evidence, "aggregate_cache_config_static_cache_path")).to_contain(root + "/explicit-cache")
expect(value_of(explicit_evidence, "aggregate_cache_config_readonly_cache_status")).to_equal("unset")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
