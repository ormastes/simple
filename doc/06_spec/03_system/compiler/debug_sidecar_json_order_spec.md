# Debug Sidecar JSON Key-Order Specification

> Verifies that the generated `*.debug.json` sidecar files produced by the FPGA Linux generation scripts maintain their exact key order after the MDSOC capsule reorganization.

<!-- sdn-diagram:id=debug_sidecar_json_order_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_sidecar_json_order_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_sidecar_json_order_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_sidecar_json_order_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Sidecar JSON Key-Order Specification

Verifies that the generated `*.debug.json` sidecar files produced by the FPGA Linux generation scripts maintain their exact key order after the MDSOC capsule reorganization.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #rtl-mdsoc-reorg |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md |
| Design | doc/05_design/rtl_riscv_mdsoc_capsules.md |
| Source | `test/03_system/compiler/debug_sidecar_json_order_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the generated `*.debug.json` sidecar files produced by the FPGA
Linux generation scripts maintain their exact key order after the MDSOC
capsule reorganization.

The `debug_sidecar_json` function in `fpga_linux_manifest.spl` emits JSON via
string concatenation in literal source order. This is an immutable contract —
no serializer, no key shuffling allowed.

## Key Order Contract (AC-3, D-4)

Expected JSON key order:
1. `reportMarkers`
2. `runnerSuccessMarkers`
3. `sourceMap`
4. `proofLane` (header field)

The exact expected order is recorded in the baseline at:
`doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md`

Pending: tests that require the baseline are gated on SA-1 creating it.

## Acceptance Criteria

- AC-3: *.debug.json sidecar contract preserved (reportMarkers,
  runnerSuccessMarkers byte-equivalent)
- AC-8: Verify in interpreter mode

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `rtl_mdsoc_baseline_2026-05-02.md` | Artifact | `doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md` |

## Scenarios

### Debug Sidecar JSON Key Order: source contract (AC-3, D-4)

#### AC-3: fpga_linux_manifest.spl contains reportMarkers key string

1. check msg
   - Expected: has_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = manifest_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val content = read_file(path)
val has_key = content.contains("reportMarkers")
expect(has_key).to_equal(true)
```

</details>

#### AC-3: fpga_linux_manifest.spl contains runnerSuccessMarkers key string

1. check msg
   - Expected: has_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = manifest_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val content = read_file(path)
val has_key = content.contains("runnerSuccessMarkers")
expect(has_key).to_equal(true)
```

</details>

#### AC-3: reportMarkers appears before runnerSuccessMarkers in manifest source

1. check msg
2. check msg
3. check msg
4. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = manifest_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val pos_report = source_key_offset("reportMarkers")
val pos_runner = source_key_offset("runnerSuccessMarkers")
check_msg(pos_report >= 0, "reportMarkers not found in manifest source")
check_msg(pos_runner >= 0, "runnerSuccessMarkers not found in manifest source")
check_msg(pos_report < pos_runner, "reportMarkers must appear before runnerSuccessMarkers in source")
expect(pos_report).to_be_less_than(pos_runner)
```

</details>

#### AC-3: sourceMap appears after runnerSuccessMarkers in manifest source

1. check msg
2. check msg
3. check msg
4. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = manifest_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val pos_runner = source_key_offset("runnerSuccessMarkers")
val pos_source_map = source_key_offset("sourceMap")
check_msg(pos_runner >= 0, "runnerSuccessMarkers not found in manifest source")
check_msg(pos_source_map >= 0, "sourceMap not found in manifest source")
check_msg(pos_runner < pos_source_map, "runnerSuccessMarkers must appear before sourceMap in source")
expect(pos_runner).to_be_less_than(pos_source_map)
```

</details>

#### AC-3: D-4 invariant — no json_ helper functions exist outside fpga_linux_manifest.spl

1. check msg
2. check msg
   - Expected: has_json_helper is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The D-4 decision states all json_* helpers live exclusively in
# fpga_linux_manifest.spl. Verify that fpga_linux_orchestrator.spl
# does not contain json_ helper definitions.
val path = orchestrator_src_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val content = read_file(path)
val has_json_helper = content.contains("fn json_")
check_msg(not has_json_helper, "D-4 violation: json_ helper defined in orchestrator, must be in manifest only")
expect(has_json_helper).to_equal(false)
```

</details>

### Debug Sidecar JSON Key Order: generated output (AC-3)

#### AC-3: RV32 generated debug.json key-order check is pending until SA-3 complete

1. pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pending("SA-3 gate — build output not yet generated by split scripts")
```

</details>

#### AC-3: RV32 generated debug.json has reportMarkers key

1. pending
2. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not rt_file_exists(rv32_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos = debug_json_key_offset(rv32_build_dir(), "reportMarkers")
check_msg(pos >= 0, "reportMarkers missing from generated debug.json in " + rv32_build_dir())
expect(pos).to_be_greater_than(-1)
```

</details>

#### AC-3: RV32 generated debug.json has runnerSuccessMarkers key

1. pending
2. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not rt_file_exists(rv32_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos = debug_json_key_offset(rv32_build_dir(), "runnerSuccessMarkers")
check_msg(pos >= 0, "runnerSuccessMarkers missing from generated debug.json in " + rv32_build_dir())
expect(pos).to_be_greater_than(-1)
```

</details>

#### AC-3: RV32 generated debug.json reportMarkers precedes runnerSuccessMarkers

1. pending
2. check msg
3. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not rt_file_exists(rv32_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos_report = debug_json_key_offset(rv32_build_dir(), "reportMarkers")
val pos_runner = debug_json_key_offset(rv32_build_dir(), "runnerSuccessMarkers")
check_msg(pos_report >= 0, "reportMarkers not found in generated json")
check_msg(pos_runner >= 0, "runnerSuccessMarkers not found in generated json")
expect(pos_report).to_be_less_than(pos_runner)
```

</details>

#### AC-3: RV64 generated debug.json key-order check is pending until SA-3 complete

1. pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pending("SA-3 gate — build output not yet generated by split scripts")
```

</details>

#### AC-3: RV64 generated debug.json has reportMarkers key

1. pending
2. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not rt_file_exists(rv64_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos = debug_json_key_offset(rv64_build_dir(), "reportMarkers")
check_msg(pos >= 0, "reportMarkers missing from generated debug.json in " + rv64_build_dir())
expect(pos).to_be_greater_than(-1)
```

</details>

#### AC-3: RV64 generated debug.json reportMarkers precedes runnerSuccessMarkers

1. pending
2. check msg
3. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not rt_file_exists(rv64_build_dir()):
    pending("SA-3 gate — build output not yet generated")
val pos_report = debug_json_key_offset(rv64_build_dir(), "reportMarkers")
val pos_runner = debug_json_key_offset(rv64_build_dir(), "runnerSuccessMarkers")
check_msg(pos_report >= 0, "reportMarkers not found in generated json")
check_msg(pos_runner >= 0, "runnerSuccessMarkers not found in generated json")
expect(pos_report).to_be_less_than(pos_runner)
```

</details>

### Debug Sidecar JSON Order: baseline comparison (AC-3)

#### AC-3: debug.json sha256 comparison is pending until SA-1 baseline exists

1. pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pending("SA-1 baseline gate — doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md not yet created")
```

</details>

#### AC-3: baseline contains debug.json section when present

1. pending
2. check msg
   - Expected: has_json_section is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not rt_file_exists(baseline_path()):
    pending("SA-1 baseline gate — " + baseline_path() + " not yet created")
val baseline = read_file(baseline_path())
val has_json_section = baseline.contains("debug.json")
check_msg(has_json_section, "baseline missing debug.json section — SA-1 must record sidecar sha256")
expect(has_json_section).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md](doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md)
- **Design:** [doc/05_design/rtl_riscv_mdsoc_capsules.md](doc/05_design/rtl_riscv_mdsoc_capsules.md)


</details>
