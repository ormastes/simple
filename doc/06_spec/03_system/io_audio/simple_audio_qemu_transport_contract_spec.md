# simple_audio_qemu_transport_contract_spec

> QEMU CUDA audio has distinct transport, payload, clock, and boot owners.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_audio_qemu_transport_contract_spec

QEMU CUDA audio has distinct transport, payload, clock, and boot owners.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU CUDA audio has distinct transport, payload, clock, and boot owners.

## Scenarios

### SimpleOS QEMU CUDA audio transport

#### maps a second ivshmem function instead of aliasing the render wire

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps a second ivshmem function instead of aliasing the render wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps a second ivshmem function instead of aliasing the render wire")
val mapper = file_read("src/os/kernel/ipc/host_gpu_ivshmem_map.spl")
expect(mapper).to_contain("fn map_qemu_audio_ivshmem_bar2() -> i64:")
expect(mapper).to_contain("if ordinal == 1:")
expect(mapper).to_contain("_map_qemu_ivshmem_bar64(0u8, dev, func, 2u8, ordinal)")
expect(mapper).to_contain("fn qemu_audio_ivshmem_window_base(mapped_slot: i64) -> u64:")
```

</details>

#### publishes bounded Q15 payload before the slot state

- publishes bounded Q15 payload before the slot state


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes bounded Q15 payload before the slot state")
val wire = file_read("src/os/lib/audio_offload/ivshmem_protocol.spl")
expect(wire).to_contain("SIMPLE_AUDIO_IVSHMEM_INPUT_OFFSET")
expect(wire).to_contain("SIMPLE_AUDIO_IVSHMEM_KERNEL_OFFSET")
expect(wire).to_contain("SIMPLE_AUDIO_IVSHMEM_OUTPUT_OFFSET")
expect(wire).to_contain("_write_q15_words(payload + (SIMPLE_AUDIO_IVSHMEM_INPUT_OFFSET as u64), input)")
expect(wire).to_contain("val status = simple_audio_ivshmem_publish")
```

</details>

#### uses the guest clock for admission and host time only as elapsed evidence

- uses the guest clock for admission and host time only as elapsed evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses the guest clock for admission and host time only as elapsed evidence")
val wire = file_read("src/os/lib/audio_offload/ivshmem_protocol.spl")
val driver = file_read("src/lib/common/engine/audio/simple_audio_remote_driver.spl")
expect(wire).to_contain("if observed_guest_ns > deadline_ns:")
expect(driver).to_contain("service_elapsed_ns: u64")
expect(driver).to_contain("if now_ns > work.deadline_ns:")
```

</details>

<details>
<summary>Advanced: polls the event state without allocating completion records in the hot loop</summary>

#### polls the event state without allocating completion records in the hot loop

- polls the event state without allocating completion records in the hot loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("polls the event state without allocating completion records in the hot loop")
val wire = file_read("src/os/lib/audio_offload/ivshmem_protocol.spl")
val probe = file_read("examples/09_embedded/simple_os/arch/x86_64/audio_cuda_ivshmem_probe_entry.spl")
expect(wire).to_contain("fn simple_audio_ivshmem_state(base: u64, slot: i64, capacity: i64) -> i64:")
expect(probe).to_contain("while wire_state != SIMPLE_AUDIO_WIRE_STATE_COMPLETED")
expect(probe).to_contain("val completion = simple_audio_ivshmem_poll")
```

</details>


</details>

#### boots direct HDA independently and probes optional CUDA audio offload

- boots direct HDA independently and probes optional CUDA audio offload


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots direct HDA independently and probes optional CUDA audio offload")
val entry = file_read("examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl")
expect(entry).to_contain("val hda_status = simpleos_hda_start()")
expect(entry).to_contain("val audio_offload_status = simpleos_audio_offload_start()")
expect(entry).to_contain("[audio-offload] status=")
```

</details>

#### host service admits only device-origin parity checked output

- host service admits only device-origin parity checked output


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("host service admits only device-origin parity checked output")
val daemon = file_read("src/app/simpleos_audio_host/daemon_runner.spl")
val cuda = file_read("src/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15.spl")
val shim = file_read("src/runtime/sffi/simple_audio_cuda_driver.c")
expect(daemon).to_contain("simple_audio_q15_execute_cuda_raw(executor, input_ptr, input_count, kernel_ptr, kernel_count)")
expect(daemon).to_contain("result.backend_handle <= 0")
expect(daemon).to_contain("result.device_identity <= 0")
expect(daemon).to_contain("result.normalized_error_millionths > 10")
expect(daemon).to_contain("volatile_write_u64_required(payload + AUDIO_OUTPUT_OFFSET")
expect(cuda).to_contain("_audio_raw_parity_error(input_ptr, input_count, kernel_ptr, kernel_count, host_output)")
expect(cuda).to_contain("cuda-audio-input-upload-parity-failed")
expect(cuda).to_contain("cuda-audio-kernel-upload-parity-failed")
expect(shim).to_contain("simple_audio_host_map_shared")
expect(shim).to_contain("MAP_SHARED")
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
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e0b20de71e345742c8ba165af200d3ec7678b7085013eb014f86b436a57266e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e0b20de71e345742c8ba165af200d3ec7678b7085013eb014f86b436a57266e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e0b20de71e345742c8ba165af200d3ec7678b7085013eb014f86b436a57266e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl
mirror: doc/06_spec/03_system/io_audio/simple_audio_qemu_transport_contract_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/simple_audio_qemu_transport_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/simple_audio_qemu_transport_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps a second ivshmem function instead of aliasing the render wire' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes bounded Q15 payload before the slot state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the guest clock for admission and host time only as elapsed evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
