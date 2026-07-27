# Test Host Env Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Host Env Specification

## Scenarios

### test host environment SIMD evidence

#### binds every SIMD row to one complete architecture-owned frame receipt

- "HostCapabilityRow create
   - Expected: source does not contain `"matrix`
   - Expected: source does not contain `native_simd_pixel_evidence`
   - Expected: source does not contain `if env.validation_reason() == "":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/test/test_host_env.spl")

expect(source).to_contain(
    "val CPU_SIMD_PATH = \"build/cpu-simd-engine2d-evidence/evidence.env\"")
expect(source).to_contain(
    "val ARM_SIMD_PATH = \"build/cpu-simd-engine2d-arch-matrix/aarch64/out/evidence.env\"")
expect(source).to_contain(
    "val RISCV_SIMD_PATH = \"build/cpu-simd-engine2d-arch-matrix/riscv64/out/evidence.env\"")
expect(source).to_contain("if host_x86_simd_evidence_passes(cpu_simd):")
expect(source).to_contain("host_renderdoc_evidence_passes(renderdoc) and host_renderdoc_capture_is_current(renderdoc)")
expect(source).to_contain("host_simd_capability_row(")
expect(source).to_contain("\"arm_simd\", arm_simd, \"aarch64\", \"neon\", ARM_SIMD_PATH")
expect(source).to_contain("\"riscv_simd\", riscv_simd, \"riscv64\", \"rvv\", RISCV_SIMD_PATH")
expect(source).to_contain(
    "HostCapabilityRow.create(\"x86_simd\", \"pass\", \"\", CPU_SIMD_PATH, \"\")")
expect(source.contains("matrix.contains(")).to_equal(false)
expect(source.contains("native_simd_pixel_evidence")).to_equal(false)
expect(source.contains("detect_simd_level")).to_equal(false)
expect(source).to_contain("if env.ready():")
expect(source.contains("if env.validation_reason() == \"\":")).to_equal(false)
```

</details>

#### rejects a deleted or changed retained RenderDoc capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple-test-host-env-renderdoc-current.rdc"
file_delete(path)
expect(file_write(path, "RDOC-original")).to_be(true)
val evidence = "rdoc_simple_gate_capture_file=" + path + "\n" +
    "rdoc_simple_gate_capture_file_sha256=" + file_hash_sha256(path)
expect(host_renderdoc_capture_is_current(evidence)).to_be(true)
expect(file_write(path, "RDOC-changed")).to_be(true)
expect(host_renderdoc_capture_is_current(evidence)).to_be(false)
file_delete(path)
expect(host_renderdoc_capture_is_current(evidence)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_host_env_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- test host environment SIMD evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
