# qemu_runner_fs_exec_fallback_acceptance_spec

> fs-exec lanes must fail closed: resident-manifest fallback is never accepted

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects on riscv64-hosted
   - Expected: fs_exec_lane_name_rejects_resident_fallback("riscv64-hosted") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects on riscv64-hosted")
expect(fs_exec_lane_name_rejects_resident_fallback("riscv64-hosted")).to_equal(true)
```

</details>

#### rejects on riscv64-virtio-fat32-smf

- rejects on riscv64-virtio-fat32-smf
   - Expected: fs_exec_lane_name_rejects_resident_fallback("riscv64-virtio-fat32-smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects on riscv64-virtio-fat32-smf")
expect(fs_exec_lane_name_rejects_resident_fallback("riscv64-virtio-fat32-smf")).to_equal(true)
```

</details>

#### rejects on riscv32-virtio-fat32-smf

- rejects on riscv32-virtio-fat32-smf
   - Expected: fs_exec_lane_name_rejects_resident_fallback("riscv32-virtio-fat32-smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects on riscv32-virtio-fat32-smf")
expect(fs_exec_lane_name_rejects_resident_fallback("riscv32-virtio-fat32-smf")).to_equal(true)
```

</details>

#### rejects on arm64-virtio-fat32-smf

- rejects on arm64-virtio-fat32-smf
   - Expected: fs_exec_lane_name_rejects_resident_fallback("arm64-virtio-fat32-smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects on arm64-virtio-fat32-smf")
expect(fs_exec_lane_name_rejects_resident_fallback("arm64-virtio-fat32-smf")).to_equal(true)
```

</details>

#### rejects on arm32-virtio-fat32-smf

- rejects on arm32-virtio-fat32-smf
   - Expected: fs_exec_lane_name_rejects_resident_fallback("arm32-virtio-fat32-smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects on arm32-virtio-fat32-smf")
expect(fs_exec_lane_name_rejects_resident_fallback("arm32-virtio-fat32-smf")).to_equal(true)
```

</details>

#### rejects on arm64-wm-ramfb

- rejects on arm64-wm-ramfb
   - Expected: fs_exec_lane_name_rejects_resident_fallback("arm64-wm-ramfb") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects on arm64-wm-ramfb")
expect(fs_exec_lane_name_rejects_resident_fallback("arm64-wm-ramfb")).to_equal(true)
```

</details>

#### rejects on x86_64 fs-exec and desktop lanes (review parity fix)

- rejects on x86_64 fs-exec and desktop lanes (review parity fix)
   - Expected: fs_exec_lane_name_rejects_resident_fallback("x64-nvme-fat32") is true
   - Expected: fs_exec_lane_name_rejects_resident_fallback("x64-full-stack") is true
   - Expected: fs_exec_lane_name_rejects_resident_fallback("x64-desktop-test") is true
   - Expected: fs_exec_lane_name_rejects_resident_fallback("x64-desktop-uefi") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects on x86_64 fs-exec and desktop lanes (review parity fix)")
expect(fs_exec_lane_name_rejects_resident_fallback("x64-nvme-fat32")).to_equal(true)
expect(fs_exec_lane_name_rejects_resident_fallback("x64-full-stack")).to_equal(true)
expect(fs_exec_lane_name_rejects_resident_fallback("x64-desktop-test")).to_equal(true)
expect(fs_exec_lane_name_rejects_resident_fallback("x64-desktop-uefi")).to_equal(true)
```

</details>

#### does not apply to non-fs-exec lanes

- does not apply to non-fs-exec lanes
   - Expected: fs_exec_lane_name_rejects_resident_fallback("x64-net-user") is false
   - Expected: fs_exec_lane_name_rejects_resident_fallback("x86_64-physical-nvme-perf") is false
   - Expected: fs_exec_lane_name_rejects_resident_fallback("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not apply to non-fs-exec lanes")
expect(fs_exec_lane_name_rejects_resident_fallback("x64-net-user")).to_equal(false)
expect(fs_exec_lane_name_rejects_resident_fallback("x86_64-physical-nvme-perf")).to_equal(false)
expect(fs_exec_lane_name_rejects_resident_fallback("")).to_equal(false)
```

</details>

### fs-exec serial acceptance rejects resident-manifest fallback end-to-end

#### arm64-wm-ramfb accepts complete serial then rejects once fallback marker appears

- arm64-wm-ramfb accepts complete serial then rejects once fallback marker appears
   - Expected: qemu_scenario_serial_acceptance_reason(s, "", serial) equals `ready`
   - Expected: qemu_scenario_serial_acceptance_reason(s, "", serial) equals `resident-fallback-rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64-wm-ramfb accepts complete serial then rejects once fallback marker appears")
val s = scenario_arm64_wm_ramfb()
var serial = _serial_with_required_markers(_scenario_required_marker_fragments(s))
expect(qemu_scenario_serial_acceptance_reason(s, "", serial)).to_equal("ready")
serial = serial + "[desktop-e2e] resident-fallback:active\n"
expect(qemu_scenario_serial_acceptance_reason(s, "", serial)).to_equal("resident-fallback-rejected")
```

</details>

#### arm64-wm-ramfb rejects launcher fallback marker form too

- arm64-wm-ramfb rejects launcher fallback marker form too
   - Expected: qemu_scenario_serial_acceptance_reason(s, "", serial) equals `resident-fallback-rejected`
   - Expected: fs_exec_serial_has_fallback(serial) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64-wm-ramfb rejects launcher fallback marker form too")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `978eb05845f676227798da7b020be6ba9888da74618b37bfaa54b2ddbdb79f51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `978eb05845f676227798da7b020be6ba9888da74618b37bfaa54b2ddbdb79f51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `978eb05845f676227798da7b020be6ba9888da74618b37bfaa54b2ddbdb79f51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.spl
mirror: doc/06_spec/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects on riscv64-hosted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects on riscv64-virtio-fat32-smf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects on riscv32-virtio-fat32-smf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
