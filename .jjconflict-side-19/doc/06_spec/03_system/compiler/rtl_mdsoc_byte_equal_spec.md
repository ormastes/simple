# RTL MDSOC Byte-Equal Verification Specification

> Verifies that the MDSOC capsule reorganization of the Simple-source VHDL emitter produces byte-identical VHDL output to the pre-refactor baseline.

<!-- sdn-diagram:id=rtl_mdsoc_byte_equal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rtl_mdsoc_byte_equal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rtl_mdsoc_byte_equal_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rtl_mdsoc_byte_equal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RTL MDSOC Byte-Equal Verification Specification

Verifies that the MDSOC capsule reorganization of the Simple-source VHDL emitter produces byte-identical VHDL output to the pre-refactor baseline.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #rtl-mdsoc-reorg |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md |
| Design | doc/05_design/rtl_riscv_mdsoc_capsules.md |
| Research | N/A |
| Source | `test/03_system/compiler/rtl_mdsoc_byte_equal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the MDSOC capsule reorganization of the Simple-source VHDL
emitter produces byte-identical VHDL output to the pre-refactor baseline.

This spec is gate-blocked on Sub-agent 1 (SA-1) populating the baseline file
at `doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md`. Until that file
exists, all byte-equal assertions are `pending`.

## Byte-Equal Harness Design

- Invokes `scripts/rtl_riscv32_linux_generated.shs` and
  `scripts/rtl_riscv64_linux_generated.shs`
- Captures sha256 of every file under `build/rtl_linux/generated_rv32/` and
  `build/rtl_linux/generated_rv64/`
- Compares against baseline hashes from the baseline markdown file
- Skip-if-baseline-missing: tests in this category are `pending` until SA-1
  populates the baseline (TODO: SA-1 baseline gate)

## Acceptance Criteria

- AC-2: Generated VHDL diff vs current main is byte-empty for both RV32 and
  RV64 generated-Linux lanes (sha256 proof)
- AC-3: *.debug.json sidecar contract preserved (reportMarkers,
  runnerSuccessMarkers byte-equivalent)
- AC-8: Verify in interpreter mode; record compile-mode regressions separately

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

### RTL MDSOC Byte-Equal: AC-2 RV32 generated VHDL

#### AC-2: RV32 byte-equal check is pending until SA-1 populates baseline

1. pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pending("SA-1 baseline gate — doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md must be created first")
```

</details>

#### AC-2: RV32 generation script exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("scripts/rtl_riscv32_linux_generated.shs")
expect(exists).to_equal(true)
```

</details>

#### AC-2: RV32 generated VHDL sha256 matches pre-refactor baseline

1. pending
2. check msg
3. check msg
4. check msg
   - Expected: current_hashes does not contain ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not baseline_exists():
    pending("SA-1 baseline gate — baseline file missing")
val script_ok = run_generation_script("scripts/rtl_riscv32_linux_generated.shs")
check_msg(script_ok, "RV32 generation script failed")
val current_hashes = sha256_dir(rv32_build_dir(), "*.vhd")
val baseline = read_baseline()
check_msg(baseline.contains("rv32"), "baseline missing rv32 section")
check_msg(current_hashes != "", "no RV32 .vhd files found after script run")
expect(current_hashes.contains("")).to_equal(false)
```

</details>

### RTL MDSOC Byte-Equal: AC-2 RV64 generated VHDL

#### AC-2: RV64 byte-equal check is pending until SA-1 populates baseline

1. pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pending("SA-1 baseline gate — doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md must be created first")
```

</details>

#### AC-2: RV64 generation script exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("scripts/rtl_riscv64_linux_generated.shs")
expect(exists).to_equal(true)
```

</details>

#### AC-2: RV64 generated VHDL sha256 matches pre-refactor baseline

1. pending
2. check msg
3. check msg
4. check msg
   - Expected: current_hashes does not contain ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not baseline_exists():
    pending("SA-1 baseline gate — baseline file missing")
val script_ok = run_generation_script("scripts/rtl_riscv64_linux_generated.shs")
check_msg(script_ok, "RV64 generation script failed")
val current_hashes = sha256_dir(rv64_build_dir(), "*.vhd")
val baseline = read_baseline()
check_msg(baseline.contains("rv64"), "baseline missing rv64 section")
check_msg(current_hashes != "", "no RV64 .vhd files found after script run")
expect(current_hashes.contains("")).to_equal(false)
```

</details>

### RTL MDSOC Byte-Equal: AC-3 debug.json sidecar

#### AC-3: sidecar byte-equal check is pending until SA-1 populates baseline

1. pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pending("SA-1 baseline gate — doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md must be created first")
```

</details>

#### AC-3: RV32 .debug.json sha256 matches pre-refactor baseline

1. pending
2. check msg
3. check msg
   - Expected: current_hashes does not contain ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not baseline_exists():
    pending("SA-1 baseline gate — baseline file missing")
val current_hashes = sha256_dir(rv32_build_dir(), "*.debug.json")
val baseline = read_baseline()
check_msg(baseline.contains("debug.json"), "baseline missing debug.json section")
check_msg(current_hashes != "", "no RV32 .debug.json files found")
expect(current_hashes.contains("")).to_equal(false)
```

</details>

#### AC-3: RV64 .debug.json sha256 matches pre-refactor baseline

1. pending
2. check msg
3. check msg
   - Expected: current_hashes does not contain ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not baseline_exists():
    pending("SA-1 baseline gate — baseline file missing")
val current_hashes = sha256_dir(rv64_build_dir(), "*.debug.json")
val baseline = read_baseline()
check_msg(baseline.contains("debug.json"), "baseline missing debug.json section")
check_msg(current_hashes != "", "no RV64 .debug.json files found")
expect(current_hashes.contains("")).to_equal(false)
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

- **Plan:** [doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md](doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md)
- **Design:** [doc/05_design/rtl_riscv_mdsoc_capsules.md](doc/05_design/rtl_riscv_mdsoc_capsules.md)


</details>
