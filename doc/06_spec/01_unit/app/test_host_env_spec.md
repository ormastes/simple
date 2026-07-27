# Test Host Env Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Host Env Specification

## Scenarios

### test host environment SIMD evidence

Shared real-host symlink helper:

```simple
fn create_file_symlink(target: text, link: text) -> i64:
    val (_, _, code) = if host_os() == "windows":
        process_run_timeout("cmd", ["/c", "mklink", link, target], 5000)
    else:
        process_run_timeout("/bin/ln", ["-s", target, link], 5000)
    code
```

#### binds every SIMD row to one complete architecture-owned frame receipt

- "HostCapabilityRow create
   - Expected: source does not contain `"matrix`
   - Expected: source does not contain `native_simd_pixel_evidence`
   - Expected: source does not contain `if env.validation_reason() == "":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/test/test_host_env.spl")
val test_source = file_read("test/01_unit/app/test_host_env_spec.spl")

expect(source).to_contain(
    "val CPU_SIMD_PATH = \"build/cpu-simd-engine2d-evidence/evidence.env\"")
expect(source).to_contain(
    "val ARM_SIMD_PATH = \"build/cpu-simd-engine2d-arch-matrix/aarch64/out/evidence.env\"")
expect(source).to_contain(
    "val RISCV_SIMD_PATH = \"build/cpu-simd-engine2d-arch-matrix/riscv64/out/evidence.env\"")
expect(source).to_contain("host_capability_row_from_evidence(")
expect(source).to_contain(
    "host_x86_simd_evidence_passes(cpu_simd) and host_simd_artifacts_are_current(cpu_simd),")
expect(source).to_contain("host_renderdoc_evidence_passes(renderdoc) and host_renderdoc_artifacts_are_current(renderdoc)")
expect(source).to_contain("host_simd_capability_row_current(")
expect(source).to_contain(
    "host_simd_evidence_passes(evidence, arch, feature) and host_simd_artifacts_are_current(evidence),")
expect(source).to_contain("\"arm_simd\", arm_simd, \"aarch64\", \"neon\", ARM_SIMD_PATH")
expect(source).to_contain("\"riscv_simd\", riscv_simd, \"riscv64\", \"rvv\", RISCV_SIMD_PATH")
expect(source).to_contain("file_exists(CPU_SIMD_PATH)")
expect(source).to_contain(
    "file_exists(VULKAN_PATH) and file_exists(VULKAN_RUN_PATH) and file_exists(VULKAN_BROWSER_PATH)")
expect(source).to_contain("file_exists(RENDERDOC_PATH)")
expect(source).to_contain("file_exists(LIVE_WM_PATH)")
expect(source.contains("matrix.contains(")).to_equal(false)
expect(source.contains("native_simd_pixel_evidence")).to_equal(false)
expect(source.contains("detect_simd_level")).to_equal(false)
expect(source).to_contain("if env.ready():")
expect(source.contains("if env.validation_reason() == \"\":")).to_equal(false)
expect(test_source).to_contain("process_run_timeout(\"/bin/ln\"")
expect(test_source).to_contain("process_run_timeout(\"cmd\"")
expect(test_source.contains("process_run(\"/bin/ln\"")).to_be(false)
```

</details>

#### rejects stale or substituted SIMD source compiler and receipt provenance

- Reject changed canonical source bytes
- Reject changed or substituted compiler bytes, including a same-byte symlink
- Reject a receipt hash that does not bind the recorded frame fields

The retained SIMD row passes only while the canonical evidence source and selected
compiler are regular non-symlink files whose current SHA-256 hashes match the
receipt, and the receipt SHA-256 matches the producer's exact six-line payload.

<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_path = "/tmp/simple-test-host-env-simd-source.spl"
val source_target_path = "/tmp/simple-test-host-env-simd-source-target.spl"
val compiler_path = "/tmp/simple-test-host-env-simd-compiler"
val compiler_target_path = "/tmp/simple-test-host-env-simd-compiler-target"
file_delete(source_path)
file_delete(source_target_path)
file_delete(compiler_path)
file_delete(compiler_target_path)
expect(file_write(source_path, "canonical SIMD source")).to_be(true)
expect(file_write(compiler_path, "selected Simple compiler")).to_be(true)
val evidence = simd_provenance_evidence(source_path, compiler_path)
expect(host_simd_artifacts_are_current(evidence, source_path)).to_be(true)
step("Reject changed canonical source bytes")
expect(file_write(source_path, "changed SIMD source")).to_be(true)
expect(host_simd_artifacts_are_current(evidence, source_path)).to_be(false)
expect(file_write(source_path, "canonical SIMD source")).to_be(true)
expect(file_write(source_target_path, "canonical SIMD source")).to_be(true)
file_delete(source_path)
expect(create_file_symlink(source_target_path, source_path)).to_equal(0)
expect(host_simd_artifacts_are_current(evidence, source_path)).to_be(false)
file_delete(source_path)
expect(file_write(source_path, "canonical SIMD source")).to_be(true)
step("Reject changed or substituted compiler bytes")
expect(file_write(compiler_path, "changed Simple compiler")).to_be(true)
expect(host_simd_artifacts_are_current(evidence, source_path)).to_be(false)
file_delete(compiler_path)
expect(host_simd_artifacts_are_current(evidence, source_path)).to_be(false)
expect(file_write(compiler_target_path, "selected Simple compiler")).to_be(true)
expect(create_file_symlink(compiler_target_path, compiler_path)).to_equal(0)
expect(file_hash_sha256(compiler_path)).to_equal(file_hash_sha256(compiler_target_path))
expect(host_simd_artifacts_are_current(evidence, source_path)).to_be(false)
file_delete(compiler_path)
expect(file_write(compiler_path, "selected Simple compiler")).to_be(true)
step("Reject a receipt hash that does not bind the recorded frame fields")
val altered_receipt = evidence.replace(
    "cpu_simd_evidence_frame_receipt_sha256=",
    "cpu_simd_evidence_frame_receipt_sha256=0")
expect(host_simd_artifacts_are_current(altered_receipt, source_path)).to_be(false)
file_delete(source_path)
expect(host_simd_artifacts_are_current(evidence, source_path)).to_be(false)
file_delete(compiler_path)
file_delete(source_target_path)
file_delete(compiler_target_path)
```

</details>

#### rejects deleted or changed retained RenderDoc artifacts

- Bind the retained receipt to current capture and replay XML bytes
- Reject a same-byte replay XML symlink
- Change and remove either retained RenderDoc artifact

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind the retained receipt to current capture and replay XML bytes")
val capture_path = "/tmp/simple-test-host-env-renderdoc-current.rdc"
val xml_path = "/tmp/simple-test-host-env-renderdoc-current.xml"
val xml_target_path = "/tmp/simple-test-host-env-renderdoc-target.xml"
file_delete(capture_path)
file_delete(xml_path)
file_delete(xml_target_path)
expect(file_write(capture_path, "RDOC-original")).to_be(true)
expect(file_write(xml_path, "replay-original")).to_be(true)
val xml_sha = file_hash_sha256(xml_path)
val evidence = "rdoc_simple_gate_capture_file=" + capture_path + "\n" +
    "rdoc_simple_gate_capture_file_sha256=" + file_hash_sha256(capture_path) + "\n" +
    "rdoc_simple_gate_replay_xml_path=" + xml_path + "\n" +
    "rdoc_simple_gate_replay_xml_file_sha256=" + xml_sha
expect(host_renderdoc_artifacts_are_current(evidence)).to_be(true)
step("Reject a same-byte replay XML symlink")
expect(file_write(xml_target_path, "replay-original")).to_be(true)
file_delete(xml_path)
val xml_link_code = create_file_symlink(xml_target_path, xml_path)
expect(xml_link_code).to_equal(0)
expect(file_hash_sha256(xml_path)).to_equal(xml_sha)
expect(host_renderdoc_artifacts_are_current(evidence)).to_be(false)
file_delete(xml_path)
expect(file_write(xml_path, "replay-original")).to_be(true)
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
file_delete(xml_target_path)
```

</details>

#### rejects deleted or changed retained framebuffer captures

- Bind baseline and input receipts to current PPM bytes
- Reject a same-byte input framebuffer symlink
- Change and remove the retained framebuffer captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind baseline and input receipts to current PPM bytes")
val baseline_path = "/tmp/simple-test-host-env-baseline.ppm"
val input_path = "/tmp/simple-test-host-env-input.ppm"
val input_target_path = "/tmp/simple-test-host-env-input-target.ppm"
file_delete(baseline_path)
file_delete(input_path)
file_delete(input_target_path)
expect(file_write(baseline_path, "P6-baseline")).to_be(true)
expect(file_write(input_path, "P6-input")).to_be(true)
val input_sha = file_hash_sha256(input_path)
val evidence = "linux_hosted_wm_live_window_baseline_capture=" + baseline_path + "\n" +
    "linux_hosted_wm_live_window_baseline_capture_sha256=" + file_hash_sha256(baseline_path) + "\n" +
    "linux_hosted_wm_live_window_input_capture=" + input_path + "\n" +
    "linux_hosted_wm_live_window_input_capture_sha256=" + input_sha
expect(host_readback_captures_are_current(evidence)).to_be(true)
step("Reject a same-byte input framebuffer symlink")
expect(file_write(input_target_path, "P6-input")).to_be(true)
file_delete(input_path)
val input_link_code = create_file_symlink(input_target_path, input_path)
expect(input_link_code).to_equal(0)
expect(file_hash_sha256(input_path)).to_equal(input_sha)
expect(host_readback_captures_are_current(evidence)).to_be(false)
file_delete(input_path)
expect(file_write(input_path, "P6-input")).to_be(true)
step("Change and remove the retained framebuffer captures")
expect(file_write(input_path, "P6-tampered")).to_be(true)
expect(host_readback_captures_are_current(evidence)).to_be(false)
file_delete(baseline_path)
expect(host_readback_captures_are_current(evidence)).to_be(false)
file_delete(input_path)
file_delete(input_target_path)
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
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
