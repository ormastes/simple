# Test Host Env Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

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
expect(source).to_contain("host_renderdoc_evidence_passes(renderdoc) and host_renderdoc_artifacts_are_current(renderdoc)")
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

#### rejects deleted or changed retained RenderDoc artifacts

- Bind the retained receipt to current capture and replay XML bytes
- Change and remove either retained RenderDoc artifact

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind the retained receipt to current capture and replay XML bytes")
val capture_path = "/tmp/simple-test-host-env-renderdoc-current.rdc"
val xml_path = "/tmp/simple-test-host-env-renderdoc-current.xml"
file_delete(capture_path)
file_delete(xml_path)
expect(file_write(capture_path, "RDOC-original")).to_be(true)
expect(file_write(xml_path, "replay-original")).to_be(true)
val evidence = "rdoc_simple_gate_capture_file=" + capture_path + "\n" +
    "rdoc_simple_gate_capture_file_sha256=" + file_hash_sha256(capture_path) + "\n" +
    "rdoc_simple_gate_replay_xml_path=" + xml_path + "\n" +
    "rdoc_simple_gate_replay_xml_file_sha256=" + file_hash_sha256(xml_path)
expect(host_renderdoc_artifacts_are_current(evidence)).to_be(true)
step("Change and remove either retained RenderDoc artifact")
expect(file_write(xml_path, "replay-changed")).to_be(true)
expect(host_renderdoc_artifacts_are_current(evidence)).to_be(false)
expect(file_write(xml_path, "replay-original")).to_be(true)
expect(file_write(capture_path, "RDOC-changed")).to_be(true)
expect(host_renderdoc_artifacts_are_current(evidence)).to_be(false)
expect(file_write(capture_path, "RDOC-original")).to_be(true)
file_delete(xml_path)
expect(host_renderdoc_artifacts_are_current(evidence)).to_be(false)
expect(file_write(xml_path, "replay-original")).to_be(true)
file_delete(capture_path)
expect(host_renderdoc_artifacts_are_current(evidence)).to_be(false)
file_delete(xml_path)
```

</details>

#### rejects deleted or changed retained framebuffer captures

- Bind baseline and input receipts to current PPM bytes
- Change and remove the retained framebuffer captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind baseline and input receipts to current PPM bytes")
val baseline_path = "/tmp/simple-test-host-env-baseline.ppm"
val input_path = "/tmp/simple-test-host-env-input.ppm"
file_delete(baseline_path)
file_delete(input_path)
expect(file_write(baseline_path, "P6-baseline")).to_be(true)
expect(file_write(input_path, "P6-input")).to_be(true)
val evidence = "linux_hosted_wm_live_window_baseline_capture=" + baseline_path + "\n" +
    "linux_hosted_wm_live_window_baseline_capture_sha256=" + file_hash_sha256(baseline_path) + "\n" +
    "linux_hosted_wm_live_window_input_capture=" + input_path + "\n" +
    "linux_hosted_wm_live_window_input_capture_sha256=" + file_hash_sha256(input_path)
expect(host_readback_captures_are_current(evidence)).to_be(true)
step("Change and remove the retained framebuffer captures")
expect(file_write(input_path, "P6-tampered")).to_be(true)
expect(host_readback_captures_are_current(evidence)).to_be(false)
file_delete(baseline_path)
expect(host_readback_captures_are_current(evidence)).to_be(false)
file_delete(input_path)
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
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
