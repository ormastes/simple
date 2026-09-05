# Simpleos Render Evidence Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Render Evidence Specification

## Scenarios

### SimpleOS portable rendering evidence

#### should validate a correlated QEMU target record

- Prepare correlated guest serial and QMP evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `pass`
   - Expected: simpleos_render_target_status(evidence) equals `qemu-verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare correlated guest serial and QMP evidence")
val evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("pass")
expect(simpleos_render_target_status(evidence)).to_equal("qemu-verified")
```

</details>

#### should validate a complete physical-board record

- Prepare identified board boot capture and transcript evidence
   - Expected: simpleos_render_target_status(evidence) equals `board-verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare identified board boot capture and transcript evidence")
val evidence = target_evidence("physical-board", "kv260-1", EVIDENCE_HASH, EVIDENCE_HASH, "boot-1")
expect(simpleos_render_target_status(evidence)).to_equal("board-verified")
```

</details>

<details>
<summary>Advanced: should reject physical-board evidence without board identity</summary>

#### should reject physical-board evidence without board identity

- Remove board identity from a physical run
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-board-identity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove board identity from a physical run")
val evidence = target_evidence("physical-board", "", "", EVIDENCE_HASH, "boot-1")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-board-identity")
```

</details>


</details>

<details>
<summary>Advanced: should identify an invalid physical-board serial hash exactly</summary>

#### should identify an invalid physical-board serial hash exactly

- Corrupt only the board serial digest
   - Expected: result.code equals `missing-board-identity`
   - Expected: result.path equals `board_serial_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Corrupt only the board serial digest")
val evidence = target_evidence(
    "physical-board", "kv260-1", "not-a-sha256", EVIDENCE_HASH, "boot-1")
val result = validate_simpleos_render_target_evidence(evidence)
expect(result.code).to_equal("missing-board-identity")
expect(result.path).to_equal("board_serial_hash")
```

</details>


</details>

<details>
<summary>Advanced: should reject guest and external capture hash disagreement</summary>

#### should reject guest and external capture hash disagreement

- Pair the guest receipt with another framebuffer
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `guest-capture-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair the guest receipt with another framebuffer")
val evidence = target_evidence("qemu", "", "", OTHER_HASH, "boot-1")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("guest-capture-mismatch")
```

</details>


</details>

<details>
<summary>Advanced: should reject a missing guest rendering-buffer hash</summary>

#### should reject a missing guest rendering-buffer hash

- Remove the guest framebuffer digest from an otherwise valid receipt
- var evidence = target evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-guest-pixel-evidence`
   - Expected: simpleos_render_target_status(evidence) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the guest framebuffer digest from an otherwise valid receipt")
var evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
evidence.guest_pixel_hash = ""
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-guest-pixel-evidence")
expect(simpleos_render_target_status(evidence)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should reject a CPU mirror labeled as guest readback</summary>

#### should reject a CPU mirror labeled as guest readback

- Replace device-origin guest pixels with a CPU mirror
- var evidence = target evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `not-guest-device-readback`
   - Expected: simpleos_render_target_status(evidence) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace device-origin guest pixels with a CPU mirror")
var evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
evidence.guest_readback_source = "cpu_mirror"
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("not-guest-device-readback")
expect(simpleos_render_target_status(evidence)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should reject a noncanonical rendering-buffer format</summary>

#### should reject a noncanonical rendering-buffer format

- Relabel ARGB evidence as an incompatible pixel format
- var evidence = target evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `unsupported-pixel-format`
   - Expected: simpleos_render_target_status(evidence) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Relabel ARGB evidence as an incompatible pixel format")
var evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
evidence.format = "rgb565"
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("unsupported-pixel-format")
expect(simpleos_render_target_status(evidence)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should reject device readback without guest driver identity</summary>

#### should reject device readback without guest driver identity

- Remove the driver identity from an otherwise valid guest receipt
- var evidence = target evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-driver-identity`
   - Expected: simpleos_render_target_status(evidence) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the driver identity from an otherwise valid guest receipt")
var evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
evidence.driver_id = ""
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-driver-identity")
expect(simpleos_render_target_status(evidence)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should reject a missing external capture pixel hash</summary>

#### should reject a missing external capture pixel hash

- Remove the decoded capture framebuffer digest
- var evidence = target evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-capture-pixel-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the decoded capture framebuffer digest")
var evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
evidence.capture_pixel_hash = ""
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-capture-pixel-evidence")
```

</details>


</details>

<details>
<summary>Advanced: should require complete guest display-path identity</summary>

#### should require complete guest display-path identity

- Remove each controller, scanout, and resource identity field
- var controller = target evidence
   - Expected: controller_result.code equals `missing-display-path-identity`
   - Expected: controller_result.path equals `display_controller`
- var scanout = target evidence
   - Expected: scanout_result.code equals `missing-display-path-identity`
   - Expected: scanout_result.path equals `scanout_id`
- var resource = target evidence
   - Expected: resource_result.code equals `missing-display-path-identity`
   - Expected: resource_result.path equals `resource_id`
   - Expected: simpleos_render_target_status(resource) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove each controller, scanout, and resource identity field")
var controller = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
controller.display_controller = ""
val controller_result = validate_simpleos_render_target_evidence(controller)
expect(controller_result.code).to_equal("missing-display-path-identity")
expect(controller_result.path).to_equal("display_controller")

var scanout = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
scanout.scanout_id = 0
val scanout_result = validate_simpleos_render_target_evidence(scanout)
expect(scanout_result.code).to_equal("missing-display-path-identity")
expect(scanout_result.path).to_equal("scanout_id")

var resource = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
resource.resource_id = 0
val resource_result = validate_simpleos_render_target_evidence(resource)
expect(resource_result.code).to_equal("missing-display-path-identity")
expect(resource_result.path).to_equal("resource_id")
expect(simpleos_render_target_status(resource)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should require complete guest memory-path identity</summary>

#### should require complete guest memory-path identity

- Remove each DMA, cache, and IOMMU mode
- var dma = target evidence
   - Expected: dma_result.code equals `missing-memory-path-identity`
   - Expected: dma_result.path equals `dma_mode`
- var cache = target evidence
   - Expected: cache_result.code equals `missing-memory-path-identity`
   - Expected: cache_result.path equals `cache_mode`
- var iommu = target evidence
   - Expected: iommu_result.code equals `missing-memory-path-identity`
   - Expected: iommu_result.path equals `iommu_mode`
   - Expected: simpleos_render_target_status(iommu) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove each DMA, cache, and IOMMU mode")
var dma = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
dma.dma_mode = ""
val dma_result = validate_simpleos_render_target_evidence(dma)
expect(dma_result.code).to_equal("missing-memory-path-identity")
expect(dma_result.path).to_equal("dma_mode")

var cache = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
cache.cache_mode = ""
val cache_result = validate_simpleos_render_target_evidence(cache)
expect(cache_result.code).to_equal("missing-memory-path-identity")
expect(cache_result.path).to_equal("cache_mode")

var iommu = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
iommu.iommu_mode = ""
val iommu_result = validate_simpleos_render_target_evidence(iommu)
expect(iommu_result.code).to_equal("missing-memory-path-identity")
expect(iommu_result.path).to_equal("iommu_mode")
expect(simpleos_render_target_status(iommu)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should require boot transport for QEMU and physical boards</summary>

#### should require boot transport for QEMU and physical boards

- Remove the boot mechanism from each runtime kind
- var qemu = target evidence
   - Expected: qemu_result.code equals `missing-boot-transport`
   - Expected: qemu_result.path equals `boot_transport`
   - Expected: board_result.code equals `missing-boot-transport`
   - Expected: simpleos_render_target_status(board) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the boot mechanism from each runtime kind")
var qemu = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
qemu.boot_transport = ""
val qemu_result = validate_simpleos_render_target_evidence(qemu)
expect(qemu_result.code).to_equal("missing-boot-transport")
expect(qemu_result.path).to_equal("boot_transport")

var board = target_evidence(
    "physical-board", "kv260-1", EVIDENCE_HASH, EVIDENCE_HASH, "boot-1")
board.boot_transport = ""
val board_result = validate_simpleos_render_target_evidence(board)
expect(board_result.code).to_equal("missing-boot-transport")
expect(simpleos_render_target_status(board)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should require an external capture tool for every runtime</summary>

#### should require an external capture tool for every runtime

- Remove the QEMU framebuffer capture tool
- var evidence = target evidence
   - Expected: result.code equals `missing-capture-tool`
   - Expected: result.path equals `capture_tool`
   - Expected: simpleos_render_target_status(evidence) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the QEMU framebuffer capture tool")
var evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
evidence.capture_tool = ""
val result = validate_simpleos_render_target_evidence(evidence)
expect(result.code).to_equal("missing-capture-tool")
expect(result.path).to_equal("capture_tool")
expect(simpleos_render_target_status(evidence)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should reject nonpositive geometry with exact field paths</summary>

#### should reject nonpositive geometry with exact field paths

- Invalidate width, height, and stride independently
- var width = target evidence
   - Expected: width_result.code equals `invalid-dimensions`
   - Expected: width_result.path equals `width`
- var height = target evidence
   - Expected: height_result.code equals `invalid-dimensions`
   - Expected: height_result.path equals `height`
- var stride = target evidence
   - Expected: stride_result.code equals `invalid-dimensions`
   - Expected: stride_result.path equals `stride`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invalidate width, height, and stride independently")
var width = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
width.width = 0
val width_result = validate_simpleos_render_target_evidence(width)
expect(width_result.code).to_equal("invalid-dimensions")
expect(width_result.path).to_equal("width")

var height = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
height.height = 0
val height_result = validate_simpleos_render_target_evidence(height)
expect(height_result.code).to_equal("invalid-dimensions")
expect(height_result.path).to_equal("height")

var stride = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
stride.stride = 15
val stride_result = validate_simpleos_render_target_evidence(stride)
expect(stride_result.code).to_equal("invalid-dimensions")
expect(stride_result.path).to_equal("stride")
```

</details>


</details>

<details>
<summary>Advanced: should reject framebuffer byte-size arithmetic overflow</summary>

#### should reject framebuffer byte-size arithmetic overflow

- Overflow row bytes and then total frame bytes
- var row = target evidence
   - Expected: row_result.code equals `invalid-dimensions`
   - Expected: row_result.path equals `width`
- var frame = target evidence
   - Expected: frame_result.code equals `frame-byte-size-overflow`
   - Expected: frame_result.path equals `height`
   - Expected: simpleos_render_target_status(frame) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Overflow row bytes and then total frame bytes")
var row = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
row.width = 2305843009213693952
val row_result = validate_simpleos_render_target_evidence(row)
expect(row_result.code).to_equal("invalid-dimensions")
expect(row_result.path).to_equal("width")

var frame = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
frame.height = 9223372036854775807
val frame_result = validate_simpleos_render_target_evidence(frame)
expect(frame_result.code).to_equal("frame-byte-size-overflow")
expect(frame_result.path).to_equal("height")
expect(simpleos_render_target_status(frame)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should require platform model and revision for every runtime</summary>

#### should require platform model and revision for every runtime

- Remove QEMU machine model and revision independently
- var model = target evidence
   - Expected: model_result.code equals `missing-platform-identity`
   - Expected: model_result.path equals `board_model`
- var revision = target evidence
   - Expected: revision_result.code equals `missing-platform-identity`
   - Expected: revision_result.path equals `board_revision`
   - Expected: simpleos_render_target_status(revision) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove QEMU machine model and revision independently")
var model = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
model.board_model = ""
val model_result = validate_simpleos_render_target_evidence(model)
expect(model_result.code).to_equal("missing-platform-identity")
expect(model_result.path).to_equal("board_model")

var revision = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
revision.board_revision = ""
val revision_result = validate_simpleos_render_target_evidence(revision)
expect(revision_result.code).to_equal("missing-platform-identity")
expect(revision_result.path).to_equal("board_revision")
expect(simpleos_render_target_status(revision)).to_equal("fail")
```

</details>


</details>

<details>
<summary>Advanced: should accept supported targets and reject unknown target identity</summary>

#### should accept supported targets and reject unknown target identity

- Exercise every supported architecture and reject unknown target fields
- var aarch64 = target evidence
   - Expected: validate_simpleos_render_target_evidence(aarch64).code equals `pass`
- var rv64 = target evidence
   - Expected: validate_simpleos_render_target_evidence(rv64).code equals `pass`
- var runtime = target evidence
   - Expected: runtime_result.code equals `invalid-runtime`
   - Expected: runtime_result.path equals `runtime_kind`
- var architecture = target evidence
   - Expected: architecture_result.code equals `invalid-architecture`
   - Expected: architecture_result.path equals `architecture`
- var firmware = target evidence
   - Expected: firmware_result.code equals `invalid-firmware-hash`
   - Expected: firmware_result.path equals `firmware_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise every supported architecture and reject unknown target fields")
var aarch64 = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
aarch64.architecture = "aarch64"
expect(validate_simpleos_render_target_evidence(aarch64).code).to_equal("pass")

var rv64 = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
rv64.architecture = "rv64"
expect(validate_simpleos_render_target_evidence(rv64).code).to_equal("pass")

var runtime = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
runtime.runtime_kind = "host"
val runtime_result = validate_simpleos_render_target_evidence(runtime)
expect(runtime_result.code).to_equal("invalid-runtime")
expect(runtime_result.path).to_equal("runtime_kind")

var architecture = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
architecture.architecture = "armv7"
val architecture_result = validate_simpleos_render_target_evidence(architecture)
expect(architecture_result.code).to_equal("invalid-architecture")
expect(architecture_result.path).to_equal("architecture")

var firmware = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
firmware.firmware_hash = ""
val firmware_result = validate_simpleos_render_target_evidence(firmware)
expect(firmware_result.code).to_equal("invalid-firmware-hash")
expect(firmware_result.path).to_equal("firmware_hash")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing boot correlation</summary>

#### should reject missing boot correlation

- Remove the boot identity from QEMU evidence
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-correlation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the boot identity from QEMU evidence")
val evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-correlation")
```

</details>


</details>

<details>
<summary>Advanced: should reject capture identity disagreement</summary>

#### should reject capture identity disagreement

- Pair a serial receipt with a different captured frame
- var evidence = target evidence
   - Expected: frame_result.code equals `frame-correlation-mismatch`
   - Expected: frame_result.path equals `capture_frame_id`
- Pair a serial receipt with a different captured boot
- var boot evidence = target evidence
   - Expected: boot_result.code equals `frame-correlation-mismatch`
   - Expected: boot_result.path equals `capture_boot_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair a serial receipt with a different captured frame")
var evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
evidence.capture_frame_id = "frame-2"
val frame_result = validate_simpleos_render_target_evidence(evidence)
expect(frame_result.code).to_equal("frame-correlation-mismatch")
expect(frame_result.path).to_equal("capture_frame_id")

step("Pair a serial receipt with a different captured boot")
var boot_evidence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
boot_evidence.capture_boot_id = "boot-2"
val boot_result = validate_simpleos_render_target_evidence(boot_evidence)
expect(boot_result.code).to_equal("frame-correlation-mismatch")
expect(boot_result.path).to_equal("capture_boot_id")
```

</details>


</details>

<details>
<summary>Advanced: should report the exact invalid receipt field</summary>

#### should report the exact invalid receipt field

- Invalidate each field formerly hidden by a compound guard
- var frame id = target evidence
   - Expected: validate_simpleos_render_target_evidence(frame_id).path equals `frame_id`
- var capture frame id = target evidence
   - Expected: validate_simpleos_render_target_evidence(capture_frame_id).path equals `capture_frame_id`
- var surface = target evidence
   - Expected: validate_simpleos_render_target_evidence(surface).path equals `surface_handle`
- var sequence = target evidence
   - Expected: validate_simpleos_render_target_evidence(sequence).path equals `present_sequence`
- var serial hash = target evidence
   - Expected: validate_simpleos_render_target_evidence(serial_hash).path equals `serial_log_hash`
- var capture kind = target evidence
   - Expected: validate_simpleos_render_target_evidence(capture_kind).path equals `capture_kind`
- var capture hash = target evidence
   - Expected: validate_simpleos_render_target_evidence(capture_hash).path equals `capture_hash`
- var oracle hash = target evidence
   - Expected: validate_simpleos_render_target_evidence(oracle_hash).path equals `oracle_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invalidate each field formerly hidden by a compound guard")
var frame_id = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
frame_id.frame_id = ""
expect(validate_simpleos_render_target_evidence(frame_id).path).to_equal("frame_id")

var capture_frame_id = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
capture_frame_id.capture_frame_id = ""
expect(validate_simpleos_render_target_evidence(capture_frame_id).path).to_equal("capture_frame_id")

var surface = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
surface.surface_handle = 0
expect(validate_simpleos_render_target_evidence(surface).path).to_equal("surface_handle")

var sequence = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
sequence.present_sequence = 0
expect(validate_simpleos_render_target_evidence(sequence).path).to_equal("present_sequence")

var serial_hash = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
serial_hash.serial_log_hash = ""
expect(validate_simpleos_render_target_evidence(serial_hash).path).to_equal("serial_log_hash")

var capture_kind = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
capture_kind.capture_kind = ""
expect(validate_simpleos_render_target_evidence(capture_kind).path).to_equal("capture_kind")

var capture_hash = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
capture_hash.capture_hash = ""
expect(validate_simpleos_render_target_evidence(capture_hash).path).to_equal("capture_hash")

var oracle_hash = target_evidence("qemu", "", "", EVIDENCE_HASH, "boot-1")
oracle_hash.oracle_hash = ""
expect(validate_simpleos_render_target_evidence(oracle_hash).path).to_equal("oracle_hash")
```

</details>


</details>

#### should reject non-hex evidence hashes

- Replace a capture digest with a same-length non-hex string
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `missing-capture-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace a capture digest with a same-length non-hex string")
val evidence = target_evidence("qemu", "", "", "gggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg", "boot-1")
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("missing-capture-evidence")
```

</details>

### SimpleOS target-native SIMD evidence

#### should validate x86 AVX2 vector chunks for every operation

- Prepare x86 AVX2 runtime-owner counters and exact pixels
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", required_kernels(), EVIDENCE_HASH)).code equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare x86 AVX2 runtime-owner counters and exact pixels")
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", required_kernels(), EVIDENCE_HASH)).code).to_equal("pass")
```

</details>

#### should report the exact missing guest identity field

- Invalidate each guest identity field independently
- var image = simd evidence
   - Expected: image_result.code equals `missing-guest-identity`
   - Expected: image_result.operation equals `guest_image_hash`
- var boot = simd evidence
   - Expected: boot_result.code equals `missing-guest-identity`
   - Expected: boot_result.operation equals `boot_id`
- var frame = simd evidence
   - Expected: frame_result.code equals `missing-guest-identity`
   - Expected: frame_result.operation equals `frame_id`
- var surface = simd evidence
   - Expected: surface_result.code equals `missing-guest-identity`
   - Expected: surface_result.operation equals `surface_handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invalidate each guest identity field independently")
var image = simd_evidence("x86_64", "avx2", required_kernels(), EVIDENCE_HASH)
image.guest_image_hash = ""
val image_result = validate_simpleos_simd_render_evidence(image)
expect(image_result.code).to_equal("missing-guest-identity")
expect(image_result.operation).to_equal("guest_image_hash")

var boot = simd_evidence("x86_64", "avx2", required_kernels(), EVIDENCE_HASH)
boot.boot_id = ""
val boot_result = validate_simpleos_simd_render_evidence(boot)
expect(boot_result.code).to_equal("missing-guest-identity")
expect(boot_result.operation).to_equal("boot_id")

var frame = simd_evidence("x86_64", "avx2", required_kernels(), EVIDENCE_HASH)
frame.frame_id = ""
val frame_result = validate_simpleos_simd_render_evidence(frame)
expect(frame_result.code).to_equal("missing-guest-identity")
expect(frame_result.operation).to_equal("frame_id")

var surface = simd_evidence("x86_64", "avx2", required_kernels(), EVIDENCE_HASH)
surface.surface_handle = 0
val surface_result = validate_simpleos_simd_render_evidence(surface)
expect(surface_result.code).to_equal("missing-guest-identity")
expect(surface_result.operation).to_equal("surface_handle")
```

</details>

#### should validate AArch64 NEON vector chunks

- Prepare AArch64 NEON runtime-owner counters
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "neon", required_kernels(), EVIDENCE_HASH)).code equals `pass`
- Distinguish detected ISA disagreement from an incompatible ISA
- var detected = simd evidence
   - Expected: detected_result.code equals `isa-mismatch`
   - Expected: detected_result.operation equals `detected_isa`
   - Expected: pair_result.code equals `isa-mismatch`
   - Expected: pair_result.operation equals `actual_arch.detected_isa`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare AArch64 NEON runtime-owner counters")
expect(validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "neon", required_kernels(), EVIDENCE_HASH)).code).to_equal("pass")

step("Distinguish detected ISA disagreement from an incompatible ISA")
var detected = simd_evidence("aarch64", "neon", required_kernels(), EVIDENCE_HASH)
detected.detected_isa = "rvv"
val detected_result = validate_simpleos_simd_render_evidence(detected)
expect(detected_result.code).to_equal("isa-mismatch")
expect(detected_result.operation).to_equal("detected_isa")

val pair_result = validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "rvv", required_kernels(), EVIDENCE_HASH))
expect(pair_result.code).to_equal("isa-mismatch")
expect(pair_result.operation).to_equal("actual_arch.detected_isa")
```

</details>

#### should validate RV64 RVV vector chunks

- Prepare vector-enabled RV64 runtime-owner counters
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)).code equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare vector-enabled RV64 runtime-owner counters")
expect(validate_simpleos_simd_render_evidence(simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)).code).to_equal("pass")
```

</details>

<details>
<summary>Advanced: should reject wrapper dispatch without actual vector chunks</summary>

#### should reject wrapper dispatch without actual vector chunks

- Set fill dispatch positive while its vector chunks remain zero
   - Expected: result.code equals `zero-vector-chunks`
   - Expected: result.operation equals `fill.vector_chunks`
- Report the exact invalid dispatch and lane counters
- var dispatch = make simd kernel evidence
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", dispatch_kernels, EVIDENCE_HASH)).operation equals `fill.dispatch_calls`
- var lanes = make simd kernel evidence
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", lane_kernels, EVIDENCE_HASH)).operation equals `fill.vector_lanes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set fill dispatch positive while its vector chunks remain zero")
val kernels = [make_simd_kernel_evidence("fill", 0, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, ""), make_simd_kernel_evidence("scroll", 4, 0, "")]
val result = validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", kernels, EVIDENCE_HASH))
expect(result.code).to_equal("zero-vector-chunks")
expect(result.operation).to_equal("fill.vector_chunks")

step("Report the exact invalid dispatch and lane counters")
var dispatch = make_simd_kernel_evidence("fill", 4, 0, "")
dispatch.dispatch_calls = 0
val dispatch_kernels = [dispatch, make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, ""), make_simd_kernel_evidence("scroll", 4, 0, "")]
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", dispatch_kernels, EVIDENCE_HASH)).operation).to_equal("fill.dispatch_calls")

var lanes = make_simd_kernel_evidence("fill", 4, 0, "")
lanes.vector_lanes = 0
val lane_kernels = [lanes, make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, ""), make_simd_kernel_evidence("scroll", 4, 0, "")]
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", lane_kernels, EVIDENCE_HASH)).operation).to_equal("fill.vector_lanes")
```

</details>


</details>

<details>
<summary>Advanced: should reject required scalar fallback</summary>

#### should reject required scalar fallback

- Report the exact alpha fallback counter
   - Expected: counter_result.code equals `required-operation-scalar-fallback`
   - Expected: counter_result.operation equals `alpha.scalar_fallback_calls`
- Report the exact alpha fallback reason
   - Expected: reason_result.code equals `required-operation-scalar-fallback`
   - Expected: reason_result.operation equals `alpha.fallback_reason`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Report the exact alpha fallback counter")
val counter_kernels = [make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 1, ""), make_simd_kernel_evidence("scroll", 4, 0, "")]
val counter_result = validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "neon", counter_kernels, EVIDENCE_HASH))
expect(counter_result.code).to_equal("required-operation-scalar-fallback")
expect(counter_result.operation).to_equal("alpha.scalar_fallback_calls")

step("Report the exact alpha fallback reason")
val reason_kernels = [make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, "scalar"), make_simd_kernel_evidence("scroll", 4, 0, "")]
val reason_result = validate_simpleos_simd_render_evidence(simd_evidence("aarch64", "neon", reason_kernels, EVIDENCE_HASH))
expect(reason_result.code).to_equal("required-operation-scalar-fallback")
expect(reason_result.operation).to_equal("alpha.fallback_reason")
```

</details>


</details>

<details>
<summary>Advanced: should reject exact-pixel disagreement</summary>

#### should reject exact-pixel disagreement

- Change the SIMD output hash while counters remain positive
   - Expected: output_result.code equals `simd-oracle-mismatch`
   - Expected: output_result.operation equals `simd_output_hash`
- var qmp = simd evidence
   - Expected: qmp_result.code equals `simd-oracle-mismatch`
   - Expected: qmp_result.operation equals `qmp_capture_hash`
- var mismatch = simd evidence
   - Expected: mismatch_result.code equals `simd-oracle-mismatch`
   - Expected: mismatch_result.operation equals `mismatch_count`
- Report the exact malformed pixel-evidence hash
- var scalar hash = simd evidence
   - Expected: scalar_result.code equals `invalid-output-hash`
   - Expected: scalar_result.operation equals `scalar_oracle_hash`
- var simd hash = simd evidence
   - Expected: simd_result.code equals `invalid-output-hash`
   - Expected: simd_result.operation equals `simd_output_hash`
- var capture hash = simd evidence
   - Expected: capture_result.code equals `invalid-output-hash`
   - Expected: capture_result.operation equals `qmp_capture_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the SIMD output hash while counters remain positive")
val output_result = validate_simpleos_simd_render_evidence(simd_evidence("rv64", "rvv", required_kernels(), OTHER_HASH))
expect(output_result.code).to_equal("simd-oracle-mismatch")
expect(output_result.operation).to_equal("simd_output_hash")

var qmp = simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)
qmp.qmp_capture_hash = OTHER_HASH
val qmp_result = validate_simpleos_simd_render_evidence(qmp)
expect(qmp_result.code).to_equal("simd-oracle-mismatch")
expect(qmp_result.operation).to_equal("qmp_capture_hash")

var mismatch = simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)
mismatch.mismatch_count = 1
val mismatch_result = validate_simpleos_simd_render_evidence(mismatch)
expect(mismatch_result.code).to_equal("simd-oracle-mismatch")
expect(mismatch_result.operation).to_equal("mismatch_count")

step("Report the exact malformed pixel-evidence hash")
var scalar_hash = simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)
scalar_hash.scalar_oracle_hash = ""
val scalar_result = validate_simpleos_simd_render_evidence(scalar_hash)
expect(scalar_result.code).to_equal("invalid-output-hash")
expect(scalar_result.operation).to_equal("scalar_oracle_hash")

var simd_hash = simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)
simd_hash.simd_output_hash = ""
val simd_result = validate_simpleos_simd_render_evidence(simd_hash)
expect(simd_result.code).to_equal("invalid-output-hash")
expect(simd_result.operation).to_equal("simd_output_hash")

var capture_hash = simd_evidence("rv64", "rvv", required_kernels(), EVIDENCE_HASH)
capture_hash.qmp_capture_hash = ""
val capture_result = validate_simpleos_simd_render_evidence(capture_hash)
expect(capture_result.code).to_equal("invalid-output-hash")
expect(capture_result.operation).to_equal("qmp_capture_hash")
```

</details>


</details>

<details>
<summary>Advanced: should reject duplicate SIMD operations</summary>

#### should reject duplicate SIMD operations

- Duplicate fill while omitting scroll
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", kernels, EVIDENCE_HASH)).code equals `duplicate-required-operation`
- Report each missing required operation
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", no_fill, EVIDENCE_HASH)).operation equals `fill`
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", no_copy, EVIDENCE_HASH)).operation equals `copy`
   - Expected: validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", no_alpha, EVIDENCE_HASH)).operation equals `alpha`
   - Expected: missing_result.code equals `missing-required-operation`
   - Expected: missing_result.operation equals `scroll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Duplicate fill while omitting scroll")
val kernels = [make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, "")]
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", kernels, EVIDENCE_HASH)).code).to_equal("duplicate-required-operation")

step("Report each missing required operation")
val no_fill = [make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, ""), make_simd_kernel_evidence("scroll", 4, 0, "")]
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", no_fill, EVIDENCE_HASH)).operation).to_equal("fill")

val no_copy = [make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, ""), make_simd_kernel_evidence("scroll", 4, 0, "")]
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", no_copy, EVIDENCE_HASH)).operation).to_equal("copy")

val no_alpha = [make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("scroll", 4, 0, "")]
expect(validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", no_alpha, EVIDENCE_HASH)).operation).to_equal("alpha")

val no_scroll = [make_simd_kernel_evidence("fill", 4, 0, ""), make_simd_kernel_evidence("copy", 4, 0, ""), make_simd_kernel_evidence("alpha", 4, 0, "")]
val missing_result = validate_simpleos_simd_render_evidence(simd_evidence("x86_64", "avx2", no_scroll, EVIDENCE_HASH))
expect(missing_result.code).to_equal("missing-required-operation")
expect(missing_result.operation).to_equal("scroll")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/renderdoc/simpleos_render_evidence_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS portable rendering evidence
- SimpleOS target-native SIMD evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
