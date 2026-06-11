# Rtl Riscv64 Linux Generated Script Specification

> <details>

<!-- sdn-diagram:id=rtl_riscv64_linux_generated_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rtl_riscv64_linux_generated_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rtl_riscv64_linux_generated_script_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rtl_riscv64_linux_generated_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rtl Riscv64 Linux Generated Script Specification

## Scenarios

### generated RV64 RTL Linux smoke script

#### probes LLVM native-build capability instead of trusting executable bits alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/rtl_riscv64_linux_generated.shs")
expect(script).to_contain("can_run_simple_bin()")
expect(script).to_contain("can_native_build_with_candidate()")
expect(script).to_contain("timeout 5 \"$candidate\" native-build --help >/dev/null 2>&1")
expect(script).to_contain("\"$candidate\" native-build")
expect(script).to_contain("FAIL: unable to build $LANE_ID payload with an LLVM-capable Simple compiler")
```

</details>

#### tries release and bootstrap candidates before the generic wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/rtl_riscv64_linux_generated.shs")
expect(script).to_contain("SIMPLE_BINARY")
expect(script).to_contain("\"$REPO_ROOT/bin/release/x86_64-unknown-linux-gnu/simple\"")
expect(script).to_contain("\"$REPO_ROOT/build/bootstrap/full/x86_64-unknown-linux-gnu/simple\"")
expect(script).to_contain("\"$REPO_ROOT/src/compiler_rust/target/bootstrap/simple\"")
expect(script).to_contain("\"$REPO_ROOT/src/compiler_rust/target/release/simple\"")
expect(script).to_contain("\"$REPO_ROOT/bin/simple\"")
```

</details>

#### reports a precise prerequisite after exhausting candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/rtl_riscv64_linux_generated.shs")
expect(script).to_contain("native-build unsupported/silent rc=3")
expect(script).to_contain("cargo build --features llvm -p simple-driver")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/fpga_linux/rtl_riscv64_linux_generated_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- generated RV64 RTL Linux smoke script

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
