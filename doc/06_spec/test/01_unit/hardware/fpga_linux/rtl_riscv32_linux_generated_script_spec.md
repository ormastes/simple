# Rtl Riscv32 Linux Generated Script Specification

> <details>

<!-- sdn-diagram:id=rtl_riscv32_linux_generated_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rtl_riscv32_linux_generated_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rtl_riscv32_linux_generated_script_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rtl_riscv32_linux_generated_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rtl Riscv32 Linux Generated Script Specification

## Scenarios

### generated RV32 RTL Linux smoke script

#### probes LLVM native-build capability instead of trusting help output alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/rtl_riscv32_linux_generated.shs")
expect(script).to_contain("can_run_simple_bin()")
expect(script).to_contain("build_simple_candidate_list()")
expect(script).to_contain("if \"$candidate\" native-build")
expect(script).to_contain("--backend llvm")
expect(script).to_contain("missing llvm feature (log:")
```

</details>

#### tries bootstrap and packaged release candidates before the generic wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/rtl_riscv32_linux_generated.shs")
expect(script).to_contain("\"$REPO_ROOT/bin/release/x86_64-unknown-linux-gnu/simple\"")
expect(script).to_contain("\"$REPO_ROOT/build/bootstrap/full/x86_64-unknown-linux-gnu/simple\"")
expect(script).to_contain("\"$REPO_ROOT/build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple\"")
expect(script).to_contain("\"$REPO_ROOT/src/compiler_rust/target/release-opt/simple\"")
expect(script).to_contain("\"$REPO_ROOT/bin/simple\"")
```

</details>

#### reports a precise prerequisite after exhausting LLVM candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/rtl_riscv32_linux_generated.shs")
expect(script).to_contain("FAIL: unable to build $LANE_ID payload with an LLVM-capable Simple compiler")
expect(script).to_contain("tried candidates:")
expect(script).to_contain("cargo build --features llvm -p simple-driver")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/fpga_linux/rtl_riscv32_linux_generated_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- generated RV32 RTL Linux smoke script

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
