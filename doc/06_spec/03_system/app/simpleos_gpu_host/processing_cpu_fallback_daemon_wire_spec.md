# processing_cpu_fallback_daemon_wire_spec

> Source contract for host-only CPU fallback over the file-backed wire.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_cpu_fallback_daemon_wire_spec

Source contract for host-only CPU fallback over the file-backed wire.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Source contract for host-only CPU fallback over the file-backed wire.

## Scenarios

### SimpleOS processing CPU fallback daemon wire

#### normalizes writable mmap flags before the native ABI

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalizes writable mmap flags before the native ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes writable mmap flags before the native ABI")
val app_file_ops = file_read("src/app/io/file_ops.spl")
val lib_file_ops = file_read("src/lib/nogc_sync_mut/io/file_ops.spl")
for source in [app_file_ops, lib_file_ops]:
    expect(source).to_contain(
        "extern fn rt_mmap(path: text, size: i64, offset: i64, readonly: i64) -> i64")
    expect(source).to_contain(
        "rt_mmap(path, size, offset, if readonly: 1 else: 0)")
```

</details>

#### owns the daemon lifetime outside the native array ABI

- owns the daemon lifetime outside the native array ABI
   - Expected: file_exists("scripts/check/check-simpleos-gpu-fallback-wire.shs") is true
   - Expected: probe does not contain `process_spawn_async`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("owns the daemon lifetime outside the native array ABI")
val wrapper = file_read("scripts/check/check-simpleos-gpu-fallback-wire.shs")
val probe = file_read("src/app/test/simpleos_gpu_fallback_wire_probe.spl")
expect(file_exists("scripts/check/check-simpleos-gpu-fallback-wire.shs")).to_equal(true)
expect(wrapper).to_contain("DAEMON_TIMEOUT_SECONDS=$((TEST_TIMEOUT_SECONDS + 10))")
expect(wrapper).to_contain("timeout -k 2 \"$DAEMON_TIMEOUT_SECONDS\" env")
expect(wrapper).to_contain("SIMPLE_GPU_FAULT_INJECT_SKIP_MATCHES=1")
expect(wrapper).to_contain("trap cleanup EXIT INT TERM")
expect(wrapper).to_contain("receipt_status=4 reason=$EXPECTED_REASON source=2")
expect(wrapper).to_contain("grep -Fq \"HOST_GPU_DAEMON_TRANSPORT shm_offset=\" \"$DAEMON_LOG\"")
expect(wrapper).to_contain("simpleos_gpu_fallback_wire_reason=daemon-not-ready")
expect(wrapper).to_contain("SIMPLEOS_GPU_FALLBACK_WIRE_MIN_OFFLOAD_ELEMENTS:-0")
expect(wrapper).to_contain("SIMPLEOS_GPU_FALLBACK_WIRE_EXPECT_REASON:-16")
expect(wrapper).to_contain("0|[1-9]*) ;; *) exit 2")
expect(probe.contains("process_spawn_async")).to_equal(false)
expect(probe).to_contain("host_gpu_ivshmem_fallback_receipt_valid")
expect(probe).to_contain("if args.contains(\"--mmap-smoke\"):")
expect(probe).to_contain("GPU_FALLBACK_MMAP status=")
```

</details>

#### measures repeated exact CUDA device requests through one daemon

- measures repeated exact CUDA device requests through one daemon
   - Expected: probe.split("_output_exact(receipt, count, value)").len() equals `2`
   - Expected: probe does not contain `arg[prefix.len():]`
   - Expected: probe does not contain `processing_ir_execute_cpu`
   - Expected: daemon does not contain `while i < count:`
   - Expected: daemon does not contain `words[5].to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("measures repeated exact CUDA device requests through one daemon")
val wrapper = file_read("scripts/check/check-simpleos-gpu-fallback-wire.shs")
val probe = file_read("src/app/test/simpleos_gpu_fallback_wire_probe.spl")
val daemon = file_read("src/app/simpleos_gpu_host/daemon_runner.spl")
expect(wrapper).to_contain(
    "case \"$MODE\" in fallback|device-warm|device-warm-production)")
expect(wrapper).to_contain("--processing-fallback=none")
expect(wrapper).to_contain("--processing-verify-cpu >\"$DAEMON_LOG\"")
expect(wrapper).to_contain("\"$PROBE_BIN\" --shm \"$SHM\" --device-warm")
expect(wrapper).to_contain("warmups=3 samples=5 requests=8 count=1048576")
expect(wrapper).to_contain("checksum=809508928")
expect(wrapper).to_contain("preference != expected")
expect(wrapper).to_contain("generation != seen + 2")
expect(wrapper).to_contain("simpleos_gpu_device_warm_wire_status=pass")
expect(wrapper).to_contain(
    "simpleos_gpu_device_warm_production_wire_status=pass")
expect(wrapper).to_contain(
    "HOST_GPU_DAEMON_VERIFY processing_verify_cpu=$expected_verify$")
expect(wrapper).to_contain(
    "simpleos_gpu_fallback_wire_reason=daemon-verifier-mode-mismatch")
expect(wrapper).to_contain("cpu <= 0 || device <= 0")
expect(wrapper).to_contain(
    "simpleos_gpu_fallback_wire_reason=unexpected-cpu-verification")
expect(probe).to_contain("host_gpu_ivshmem_device_receipt_valid")
expect(probe).to_contain("val warmups: i64 = 3")
expect(probe).to_contain("val samples: i64 = 5")
expect(probe).to_contain("val expected_checksum: i64 = 809508928")
expect(probe).to_contain("_output_exact(receipt, count, value)")
expect(probe.split("_output_exact(receipt, count, value)").len()).to_equal(2)
expect(probe).to_contain("receipt.native_handle == handle")
expect(probe).to_contain("receipt.device_identity == identity")
expect(probe).to_contain("if receipt.output_addr > 0u64 and receipt.output_bytes >= 4:")
expect(probe).to_contain(
    "last_receipt_valid=" + "{" + "last_receipt_valid}")
expect(probe).to_contain(
    "last_output_exact=" + "{" + "last_output_exact}")
expect(probe).to_contain("last_output0=" + "{" + "last_output0}")
expect(probe).to_contain("GPU_DEVICE_WARM_MEDIAN status=")
expect(probe).to_contain(
    "median_device_us=" + "{" + "median_device_us}")
expect(probe).to_contain(
    "median_non_device_us=" + "{" + "median_non_device_us}")
expect(probe.contains("arg[prefix.len():]")).to_equal(false)
expect(probe.contains("processing_ir_execute_cpu")).to_equal(false)
expect(daemon).to_contain("raw_read_i32(")
expect(daemon).to_contain("simpleos_host_gpu_wire_payload_offset() + 5 * 8")
expect(daemon).to_contain("simpleos_host_gpu_wire_payload_offset() + 5 * 8) as u32")
expect(daemon).to_contain("processing_ir_fill_u32(element_count, fill_value)")
expect(daemon).to_contain("raw_write_u32s_checksum(")
expect(daemon.contains("while i < count:")).to_equal(false)
expect(daemon.contains("words[5].to_u32()")).to_equal(false)
```

</details>

#### retains the canonical OpenCL and SIMD providers in the GPU runtime

- retains the canonical OpenCL and SIMD providers in the GPU runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retains the canonical OpenCL and SIMD providers in the GPU runtime")
val runtime_build = file_read("src/compiler_rust/runtime/build.rs")
val simd_runtime = file_read("src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs")
val qemu_gate = file_read("scripts/check/check-simpleos-qemu-host-gpu-2d.shs")
expect(runtime_build).to_contain("\"runtime_simd_dispatch.c\"")
expect(runtime_build).to_contain("build.define(\"SIMPLE_RUNTIME_OPENCL_ONLY\", None)")
expect(runtime_build).to_contain("collect_c_runtime_exports")
expect(runtime_build).to_contain("symbol.starts_with(\"rt_opencl_\")")
expect(simd_runtime).to_contain("pub extern \"C\" fn rt_simd_engine2d_neon_hits() -> i64")
expect(simd_runtime).to_contain("pub extern \"C\" fn rt_simd_engine2d_neon_reset() -> i64")
expect(qemu_gate).to_contain("--features vulkan,cuda,runtime-symbol-table")
expect(qemu_gate).to_contain("\\\"runtime-symbol-table\\\"")
```

</details>

#### routes native string primitives to runtime owners without self dispatch

- routes native string primitives to runtime owners without self dispatch
   - Expected: strings does not contain `"\n    s`
   - Expected: strings does not contain `\n    s.starts_with(prefix)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes native string primitives to runtime owners without self dispatch")
val strings = file_read("src/lib/common/string_core.spl")
val runtime = file_read("src/compiler_rust/runtime/src/value/collections.rs")
val simple_core = file_read("src/runtime/simple_core/core_string.spl")
expect(strings).to_contain("fn str_len(s: text) -> i64:\n    rt_string_len(s)")
expect(strings).to_contain("fn str_contains(s: text, sub: text) -> bool:\n    rt_string_contains(s, sub)")
expect(strings).to_contain("fn str_starts_with(s: text, prefix: text) -> bool:\n    rt_string_starts_with(s, prefix)")
expect(strings).to_contain("fn str_index_of(s: text, sub: text) -> i64:\n    rt_string_find(s, sub)")
expect(strings).to_contain("fn str_last_index_of(s: text, sub: text) -> i64:\n    rt_string_rfind(s, sub)")
expect(strings.contains("\n    s.contains(sub)")).to_equal(false)
expect(strings.contains("\n    s.starts_with(prefix)")).to_equal(false)
expect(runtime).to_contain("pub extern \"C\" fn rt_string_contains")
expect(simple_core).to_contain("pub fn rt_string_contains(value: i64, needle: i64) -> i64:")
```

</details>

#### bounds request completion by an independent deadline and poll ceiling

- bounds request completion by an independent deadline and poll ceiling
   - Expected: probe does not contain `50000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bounds request completion by an independent deadline and poll ceiling")
val bridge = file_read("src/os/lib/gpu_bridge/host_gpu_ivshmem.spl")
val probe = file_read("src/app/test/simpleos_gpu_fallback_wire_probe.spl")
expect(bridge).to_contain("HOST_GPU_IVSHMEM_DEFAULT_TIMEOUT_POLLS: i64 = 50000000")
expect(bridge).to_contain("HOST_GPU_IVSHMEM_MAX_TIMEOUT_POLLS: i64 = 250000000")
expect(bridge).to_contain("HOST_GPU_IVSHMEM_REQUEST_BUDGET_US: i64 = 5000000")
expect(bridge).to_contain("boot_monotonic_deadline_us(started_now, HOST_GPU_IVSHMEM_REQUEST_BUDGET_US)")
expect(bridge).to_contain("val bounded_timeout_polls = if timeout_polls < HOST_GPU_IVSHMEM_MAX_TIMEOUT_POLLS:")
expect(bridge).to_contain("polls < bounded_timeout_polls and observed < generation and now_us > 0 and now_us <= deadline_us")
expect(bridge).to_contain("observed != generation or now_us <= 0 or now_us > deadline_us")
expect(probe).to_contain("HOST_GPU_IVSHMEM_MAX_TIMEOUT_POLLS")
expect(probe.contains("50000000")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b952315d92549d697193d8aa9d448bc32641ded7831e2e89dff20c8437f0ae3d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b952315d92549d697193d8aa9d448bc32641ded7831e2e89dff20c8437f0ae3d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b952315d92549d697193d8aa9d448bc32641ded7831e2e89dff20c8437f0ae3d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes writable mmap flags before the native ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns the daemon lifetime outside the native array ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_daemon_wire_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures repeated exact CUDA device requests through one daemon' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
