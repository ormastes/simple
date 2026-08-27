# vulkan_environment_hal_communication_spec

> Purpose: This spec proves Vulkan environment and HAL communication.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_environment_hal_communication_spec

Purpose: This spec proves Vulkan environment and HAL communication.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Vulkan environment and HAL communication.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Vulkan environment and HAL communication

#### should retain a machine-readable physical environment receipt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Probe the actual Vulkan loader compiler validator and device
   - Expected: rt_file_write_bytes(spirv_path, spirv_clear()) is true
   - Expected: loader_status equals `0`
   - Expected: loader_size_status equals `0`
   - Expected: loader_size_err equals ``
   - Expected: loader_sha_status equals `0`
   - Expected: loader_sha_err equals ``
   - Expected: loader_sha.len() equals `64`
   - Expected: assembler_status equals `0`
   - Expected: validator_status equals `0`
   - Expected: spirv_status equals `0`
   - Expected: spirv_err equals ``
   - Expected: session.init() equals `0`
   - Expected: evidence_class equals `physical-device`
   - Expected: mkdir_status equals `0`
   - Expected: rt_file_write_text(environment_receipt_path, environment_receipt) is true
   - Expected: vulkan_sffi_shutdown_reaped() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-013
# @req: REQ-014
step("Probe the actual Vulkan loader compiler validator and device")
val (loader_out, _loader_err, loader_status) = rt_process_run(
    "/bin/sh", ["-c", "ldconfig -p | sed -n 's/.*libvulkan.so.1.*=> //p' | head -n 1"])
val (_as_out, _as_err, assembler_status) = rt_process_run(
    "/bin/sh", ["-c", "command -v spirv-as >/dev/null 2>&1"])
val (_val_out, _val_err, validator_status) = rt_process_run(
    "/bin/sh", ["-c", "command -v spirv-val >/dev/null 2>&1"])
val spirv_path = "/tmp/simple_vulkan_hal_environment_clear.spv"
expect(rt_file_write_bytes(spirv_path, spirv_clear())).to_equal(true)
val (_spirv_out, spirv_err, spirv_status) = rt_process_run(
    "spirv-val", ["--target-env", "vulkan1.1", spirv_path])
expect(loader_status).to_equal(0)
expect(loader_out.len()).to_be_greater_than(0)
val loader_path = loader_out.trim()
val (loader_size_out, loader_size_err, loader_size_status) = rt_process_run("stat", ["-c", "%s", loader_path])
val (loader_sha_out, loader_sha_err, loader_sha_status) = rt_process_run("sha256sum", [loader_path])
expect(loader_size_status).to_equal(0)
expect(loader_size_err).to_equal("")
expect(loader_size_out.trim().to_i64()).to_be_greater_than(0)
expect(loader_sha_status).to_equal(0)
expect(loader_sha_err).to_equal("")
val loader_sha = loader_sha_out.split(" ")[0]
expect(loader_sha.len()).to_equal(64)
expect(assembler_status).to_equal(0)
expect(validator_status).to_equal(0)
expect(spirv_status).to_equal(0)
expect(spirv_err).to_equal("")

var session = VulkanSession.create()
expect(session.init()).to_equal(0)
val evidence_class = if session.device_type == "discrete" or session.device_type == "integrated":
    "physical-device"
elif session.device_type == "virtual":
    "emulator"
elif session.device_type == "cpu":
    "software"
else:
    "blocked"
expect(evidence_class).to_equal("physical-device")
expect(session.device).to_be_greater_than(0)
expect(session.driver_identity.len()).to_be_greater_than(0)
print("vulkan_hal_receipt_version=1")
print("vulkan_hal_evidence_class=" + evidence_class)
print("vulkan_hal_owner=VulkanSession+Engine2D")
print("vulkan_hal_loader=" + loader_path)
print("vulkan_hal_loader_size=" + loader_size_out.trim())
print("vulkan_hal_loader_sha256=" + loader_sha)
print("vulkan_hal_compiler=spirv-as")
print("vulkan_hal_validator=spirv-val")
print("vulkan_hal_device_name=" + session.device_name)
print("vulkan_hal_device_type=" + session.device_type)
print("vulkan_hal_driver_identity=" + session.driver_identity)
print("vulkan_hal_memory_capability=host-upload+device-storage+host-readback")
print("vulkan_hal_readiness=ready")
val environment_receipt = "version=1\ncommand=bin/simple test test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl --mode=interpreter --no-session-daemon\nevidence_class=" + evidence_class + "\nowner=VulkanSession+Engine2D\nloader=" + loader_path + "\nloader_size=" + loader_size_out.trim() + "\nloader_sha256=" + loader_sha + "\ncompiler=spirv-as\nvalidator=spirv-val\ndevice_name=" + session.device_name + "\ndevice_type=" + session.device_type + "\ndriver_identity=" + session.driver_identity + "\nmemory_capability=host-upload+device-storage+host-readback\nreadiness=ready\n"
expect(environment_receipt).to_contain("loader_sha256=" + loader_sha)
expect(environment_receipt).to_contain("evidence_class=physical-device")
val (_mkdir_out, _mkdir_err, mkdir_status) = rt_process_run("/bin/mkdir", ["-p", VULKAN_HAL_ARTIFACT_DIR])
expect(mkdir_status).to_equal(0)
val environment_receipt_path = VULKAN_HAL_ARTIFACT_DIR + "/environment.receipt"
expect(rt_file_write_text(environment_receipt_path, environment_receipt)).to_equal(true)
print("vulkan_hal_environment_receipt=" + environment_receipt_path)
session.release()
expect(vulkan_sffi_shutdown_reaped()).to_equal(true)
```

</details>

#### should upload dispatch download and reuse stable native identity

- should upload dispatch download and reuse stable native identity
- Upload exact CPU bytes through the Vulkan HAL
   - Expected: session.init() equals `0`
   - Expected: vulkan_sffi_copy_to_buffer(buffer, upload, 0) is true
   - Expected: vulkan_sffi_read_buffer_bytes(buffer, 64, 0) equals `upload`
- Dispatch twice through the retained session pipeline
   - Expected: first equals `_repeated_u32(0xaabbccddu32, 16)`
   - Expected: second equals `_repeated_u32(0x11223344u32, 16)`
   - Expected: identity_second equals `identity_first`
   - Expected: session.device equals `handle_first`
   - Expected: mkdir_status equals `0`
   - Expected: rt_file_write_text(communication_receipt_path, communication_receipt) is true
   - Expected: vulkan_sffi_free_buffer(buffer) is true
   - Expected: vulkan_sffi_shutdown_reaped() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should upload dispatch download and reuse stable native identity")
step("Upload exact CPU bytes through the Vulkan HAL")
var session = VulkanSession.create()
expect(session.init()).to_equal(0)
val buffer = vulkan_sffi_alloc_buffer(64, 0x80)
expect(buffer).to_be_greater_than(0)
val upload = _repeated_u32(0x01020304u32, 16)
expect(vulkan_sffi_copy_to_buffer(buffer, upload, 0)).to_equal(true)
expect(vulkan_sffi_read_buffer_bytes(buffer, 64, 0)).to_equal(upload)

step("Dispatch twice through the retained session pipeline")
val identity_first = vulkan_sffi_selected_device_driver_identity_hash()
val handle_first = session.device
expect(vulkan_dispatch_framebuffer_compute_checked(buffer, session.pipe_clear,
    _clear_push(0xaabbccddu32, 4u32, 4u32), 1, 1, 1)).to_equal(1)
val first = vulkan_sffi_read_buffer_bytes(buffer, 64, 0)
expect(first).to_equal(_repeated_u32(0xaabbccddu32, 16))
expect(vulkan_dispatch_framebuffer_compute_checked(buffer, session.pipe_clear,
    _clear_push(0x11223344u32, 4u32, 4u32), 1, 1, 1)).to_equal(1)
val second = vulkan_sffi_read_buffer_bytes(buffer, 64, 0)
val identity_second = vulkan_sffi_selected_device_driver_identity_hash()
expect(second).to_equal(_repeated_u32(0x11223344u32, 16))
expect(identity_first).to_be_greater_than(0)
expect(identity_second).to_equal(identity_first)
expect(session.device).to_equal(handle_first)
print("vulkan_hal_upload_bytes=64")
print("vulkan_hal_download_bytes=64")
print("vulkan_hal_dispatch_count=2")
print("vulkan_hal_backend_handle=" + handle_first.to_text())
print("vulkan_hal_device_identity=" + identity_first.to_text())
print("vulkan_hal_byte_parity=pass")
val (_mkdir_out, _mkdir_err, mkdir_status) = rt_process_run("/bin/mkdir", ["-p", VULKAN_HAL_ARTIFACT_DIR])
expect(mkdir_status).to_equal(0)
val communication_receipt_path = VULKAN_HAL_ARTIFACT_DIR + "/communication.receipt"
val communication_receipt = "version=1\nevidence_class=physical-device\nupload_bytes=64\ndownload_bytes=64\ndispatch_count=2\nbackend_handle=" + handle_first.to_text() + "\ndevice_identity=" + identity_first.to_text() + "\nbyte_parity=pass\n"
expect(rt_file_write_text(communication_receipt_path, communication_receipt)).to_equal(true)
print("vulkan_hal_communication_receipt=" + communication_receipt_path)
expect(vulkan_sffi_free_buffer(buffer)).to_equal(true)
session.release()
expect(vulkan_sffi_shutdown_reaped()).to_equal(true)
```

</details>

#### should render through Engine2D and reject invalid transfers

- should render through Engine2D and reject invalid transfers
- Render pixels through the canonical Engine2D Vulkan owner
   - Expected: backend.init(4, 4) is true
   - Expected: readback.source equals `device_readback`
   - Expected: readback.pixels equals `[`
- Reject invalid transfer handles without GPU provenance
   - Expected: vulkan_sffi_copy_to_buffer(0, [1u8, 2u8, 3u8, 4u8], 0) is false
   - Expected: vulkan_sffi_read_buffer_bytes(0, 4, 0).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should render through Engine2D and reject invalid transfers")
step("Render pixels through the canonical Engine2D Vulkan owner")
var backend = VulkanBackend.create()
expect(backend.init(4, 4)).to_equal(true)
backend.clear(0xff102030u32)
backend.draw_rect_filled(1, 1, 2, 2, 0xffa0b0c0u32)
val readback = backend.read_pixels_with_source()
expect(readback.source).to_equal("device_readback")
expect(readback.backend_handle).to_be_greater_than(0)
expect(readback.pixels).to_equal([
    0xff102030u32, 0xff102030u32, 0xff102030u32, 0xff102030u32,
    0xff102030u32, 0xffa0b0c0u32, 0xffa0b0c0u32, 0xff102030u32,
    0xff102030u32, 0xffa0b0c0u32, 0xffa0b0c0u32, 0xff102030u32,
    0xff102030u32, 0xff102030u32, 0xff102030u32, 0xff102030u32])
backend.shutdown()

step("Reject invalid transfer handles without GPU provenance")
expect(vulkan_sffi_copy_to_buffer(0, [1u8, 2u8, 3u8, 4u8], 0)).to_equal(false)
expect(vulkan_sffi_read_buffer_bytes(0, 4, 0).len()).to_equal(0)
print("vulkan_hal_invalid_transfer=reject")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-013`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `00897544785d265cd324b657ad64cda3c967d54fa1f1c0679604366e5ab526d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00897544785d265cd324b657ad64cda3c967d54fa1f1c0679604366e5ab526d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00897544785d265cd324b657ad64cda3c967d54fa1f1c0679604366e5ab526d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl
mirror: doc/06_spec/02_integration/rendering/vulkan_environment_hal_communication_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/vulkan_environment_hal_communication_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/vulkan_environment_hal_communication_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain a machine-readable physical environment receipt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain a machine-readable physical environment receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl:132:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should upload dispatch download and reuse stable native identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should upload dispatch download and reuse stable native identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl:175:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render through Engine2D and reject invalid transfers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render through Engine2D and reject invalid transfers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
