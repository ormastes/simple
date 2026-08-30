# qemu_runner_fs_exec_fallback_acceptance_spec

> fs-exec lanes must fail closed: resident-manifest fallback is never accepted

<!-- sdn-diagram:id=qemu_runner_fs_exec_fallback_acceptance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_runner_fs_exec_fallback_acceptance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_runner_fs_exec_fallback_acceptance_spec -> std
qemu_runner_fs_exec_fallback_acceptance_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_runner_fs_exec_fallback_acceptance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# qemu_runner_fs_exec_fallback_acceptance_spec

fs-exec lanes must fail closed: resident-manifest fallback is never accepted

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

fs-exec lanes must fail closed: resident-manifest fallback is never accepted
as completion evidence on any architecture lane.

NOTE: end-to-end acceptance checks through catalog-lane scenario constructors
(scenario_riscv64_hosted, scenario_*_virtio_fat32_smf, scenario_x64_net_user)
cannot run in interpreter mode — simpleos_platform_qemu_smoke_lane crashes the
interpreter (see doc/08_tracking/bug/interp_simpleos_lane_contract_crash_2026-06-13.md).
Lane coverage here uses the name-based predicate wired into
qemu_scenario_serial_acceptance_reason; arm64-wm-ramfb (hardcoded markers,
no catalog) provides the end-to-end case.

## Scenarios

### fs-exec lane fallback-rejection predicate covers every arch lane

#### rejects on riscv64-hosted

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_lane_name_rejects_resident_fallback("riscv64-hosted")).to_equal(true)
```

</details>

#### rejects on riscv64-virtio-fat32-smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_lane_name_rejects_resident_fallback("riscv64-virtio-fat32-smf")).to_equal(true)
```

</details>

#### rejects on riscv32-virtio-fat32-smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_lane_name_rejects_resident_fallback("riscv32-virtio-fat32-smf")).to_equal(true)
```

</details>

#### rejects on arm64-virtio-fat32-smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_lane_name_rejects_resident_fallback("arm64-virtio-fat32-smf")).to_equal(true)
```

</details>

#### rejects on arm32-virtio-fat32-smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_lane_name_rejects_resident_fallback("arm32-virtio-fat32-smf")).to_equal(true)
```

</details>

#### rejects on arm64-wm-ramfb

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_lane_name_rejects_resident_fallback("arm64-wm-ramfb")).to_equal(true)
```

</details>

#### rejects on x86_64 fs-exec and desktop lanes (review parity fix)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_lane_name_rejects_resident_fallback("x64-nvme-fat32")).to_equal(true)
expect(fs_exec_lane_name_rejects_resident_fallback("x64-full-stack")).to_equal(true)
expect(fs_exec_lane_name_rejects_resident_fallback("x64-desktop-test")).to_equal(true)
expect(fs_exec_lane_name_rejects_resident_fallback("x64-desktop-uefi")).to_equal(true)
```

</details>

#### does not apply to non-fs-exec lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_lane_name_rejects_resident_fallback("x64-net-user")).to_equal(false)
expect(fs_exec_lane_name_rejects_resident_fallback("x86_64-physical-nvme-perf")).to_equal(false)
expect(fs_exec_lane_name_rejects_resident_fallback("")).to_equal(false)
```

</details>

### fs-exec serial acceptance rejects resident-manifest fallback end-to-end

#### arm64-wm-ramfb accepts complete serial then rejects once fallback marker appears

- var serial =  serial with required markers
   - Expected: qemu_scenario_serial_acceptance_reason(s, "", serial) equals `ready`
   - Expected: qemu_scenario_serial_acceptance_reason(s, "", serial) equals `resident-fallback-rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = scenario_arm64_wm_ramfb()
var serial = _serial_with_required_markers(_scenario_required_marker_fragments(s))
expect(qemu_scenario_serial_acceptance_reason(s, "", serial)).to_equal("ready")
serial = serial + "[desktop-e2e] resident-fallback:active\n"
expect(qemu_scenario_serial_acceptance_reason(s, "", serial)).to_equal("resident-fallback-rejected")
```

</details>

#### arm64-wm-ramfb rejects launcher fallback marker form too

- var serial =  serial with required markers
   - Expected: qemu_scenario_serial_acceptance_reason(s, "", serial) equals `resident-fallback-rejected`
   - Expected: fs_exec_serial_has_fallback(serial) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = scenario_arm64_wm_ramfb()
var serial = _serial_with_required_markers(_scenario_required_marker_fragments(s))
serial = serial + "[launcher] fallback=resident-manifest\n"
expect(qemu_scenario_serial_acceptance_reason(s, "", serial)).to_equal("resident-fallback-rejected")
expect(fs_exec_serial_has_fallback(serial)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
