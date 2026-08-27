# RV64 SimpleOS WM font and input evidence

> Defines the separate RV64 QEMU dev-board evidence gate. The generic RV64

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 SimpleOS WM font and input evidence

Defines the separate RV64 QEMU dev-board evidence gate. The generic RV64

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Defines the separate RV64 QEMU dev-board evidence gate. The generic RV64
display-smoke result is not font or input proof: this lane additionally pins
the exact guest font identity, crops guest pixels, calibrates rejection with an
independently corrupted crop, and correlates QMP keyboard and pointer delivery
with guest IRQ, WM-state, and later frame markers.

The production entry now owns the pinned font mount and VirtIO input route.
The live scenario remains deliberately red until a current RV64 ELF proves
those owners and a fresh RV64 crop hash is pinned. x86_64 captures and hashes
cannot satisfy this lane.

## Scenarios

### RV64 SimpleOS WM font and input

#### should keep the RV64 gate separate and fail closed on every required proof

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should keep the RV64 gate separate and fail closed on every required proof
- Inspect the canonical RV64 QMP evidence contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the RV64 gate separate and fail closed on every required proof")
step("Inspect the canonical RV64 QMP evidence contract")
val source = wrapper_source()
expect(source).to_contain("--wm-font-input")
expect(source).to_contain("build/os/simpleos_riscv64_display_smoke.elf")
expect(source).to_contain("build/os/fat32-riscv64-desktop.img")
expect(source).to_contain("virtio-blk-pci,drive=rvdesktop")
expect(source).to_contain("FONT_GUEST_PATH=/SYS/FONTS/NOTOSANS")
expect(source).to_contain("FONT_ASSET_EXPECTED_BYTES=1708408")
expect(source).to_contain("2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081")
expect(source).to_contain("mtype -i \"$FONT_DISK\" ::/SYS/FONTS/NOTOSANS")
expect(source).to_contain("reason=font-disk-asset-mismatch")
expect(source).to_contain("[rv64-font-evidence] guest_path=$FONT_GUEST_PATH")
expect(source).to_contain("grep -Fqx \"$FONT_GUEST_MARKER\"")
expect(source).to_contain("unavailable_marker_seen=1")
expect(source).to_contain("reason=unavailable-marker-accepted")
expect(source).to_contain("FONT_REGION_EXPECTED_BYTES=8064")
expect(source).to_contain("RV64_WM_FONT_REGION_EXPECTED_SHA256")
expect(source).to_contain("'pmemsave %d %d \"%s\"'")
expect(source).to_contain("scanout receipt invalid")
expect(source).to_contain("scanout_capture_origin=qemu-pmemsave")
expect(source).to_contain("input_frame_changed=1")
expect(source).to_contain("reason=missing-scanout-receipt-accepted")
expect(source).to_not_contain("\"command-line\": \"screendump ")
expect(source).to_contain("for y in range(height - 48, height):")
expect(source).to_contain("start = (y * width + width - 56) * 3")
expect(source).to_contain("corrupt[0] ^= 1")
expect(source).to_contain("virtio-keyboard-pci")
expect(source).to_contain("virtio-mouse-pci")
expect(source).to_contain("\"execute\": \"input-send-event\"")
expect(source).to_contain("host_nonce=%s")
expect(source).to_contain("rv64-qmp-%d")
expect(source).to_contain("baseline_input_seq")
expect(source).to_contain("[wm-input-irq]")
expect(source).to_contain("[wm-pointer-irq]")
expect(source).to_contain("keyboard_seq\" -gt \"$input_baseline_seq")
expect(source).to_contain("pointer_seq\" -gt \"$keyboard_seq")
expect(source).to_contain("keyboard_generation\" -gt \"$scanout_generation")
expect(source).to_contain("pointer_generation\" -gt \"$keyboard_generation")
expect(source).to_contain("type=1 code=15 value=1")
expect(source).to_contain("button_code=1 kind_code=1")
expect(source).to_contain("button_code=1 kind_code=2")
expect(source).to_contain("correlated pointer down missing")
expect(source).to_contain("^\\[wm-state\\] input_seq=$keyboard_seq action=cycle-focus window=[1-9][0-9]* .*")
expect(source).to_contain("^\\[wm-pointer-state\\] input_seq=$pointer_seq window=[1-9][0-9]* .*handled=true")
expect(source).to_contain("correlated pointer frame missing")
expect(source).to_contain("required_generation")
expect(source).to_contain("font_corrupt_rejected=1")
expect(source).to_contain("rv64-font-crop-oracle-unpinned")
```

</details>

#### should connect RV64 PCI input through the shared production backend

- should connect RV64 PCI input through the shared production backend
- Inspect the canonical RV64 input owner and desktop entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should connect RV64 PCI input through the shared production backend")
step("Inspect the canonical RV64 input owner and desktop entry")
val entry = rv64_entry_source()
val facade = rv64_input_facade_source()
val runtime = rv64_input_runtime_source()
val backend = shared_virtio_input_backend_source()
expect(entry).to_contain("use os.desktop.shell.{DesktopShell}")
expect(entry).to_contain("source=shared-wm-draw-ir-engine2d")
expect(entry).to_contain("fatal reason=scanout-generation")
expect(entry).to_contain("scanout-present address={address}")
expect(entry).to_contain("format=bgra8888 generation={display_generation}")
expect(entry).to_contain("vfs_boot_init_riscv64_virtio_fat32")
expect(entry).to_contain("simpleos_desktop_register_selected_fonts_from_vfs")
expect(entry).to_contain("fatal reason=font-media-mount")
expect(entry).to_contain("fatal reason=font-register")
expect(entry).to_contain("[rv64-font-evidence] guest_path=/SYS/FONTS/NOTOSANS asset_bytes=1708408")
expect(entry).to_not_contain("[rv64-font-evidence-unavailable]")
expect(entry).to_contain("VirtioInputBackend.create_with_poller")
expect(entry).to_contain("riscv64_virtio_input_poll")
expect(entry).to_contain("delivery=poll+irq-ack+refill")
expect(entry).to_contain("[wm-input-irq] input_seq={key_sequence}")
expect(entry).to_contain("[wm-state] input_seq={key_sequence}")
expect(entry).to_contain("[wm-frame] input_seq={key_sequence}")
expect(entry).to_contain("[wm-pointer-irq] input_seq={pointer_sequence}")
expect(entry).to_contain("[wm-pointer-state] input_seq={pointer_sequence}")
expect(entry).to_contain("[wm-pointer-frame] input_seq={pointer_sequence}")
expect(facade).to_contain("extern fn rt_riscv64_virtio_input_init()")
expect(facade).to_contain("VirtioInputEvent(")
expect(runtime).to_contain("RT_VIRTIO_INPUT_LEGACY_DEVICE_ID 0x1012")
expect(runtime).to_contain("RT_VIRTIO_INPUT_MODERN_DEVICE_ID 0x1052")
expect(runtime).to_contain("RT_VIRTIO_PCI_CAP_DEVICE_CFG")
expect(runtime).to_contain("rt_riscv64_virtio_input_start_modern")
expect(runtime).to_contain("rt_setup_virtqueue(")
expect(runtime).to_contain("RT_VIRTIO_MODERN_QUEUE_SIZE")
expect(runtime).to_contain("RT_VIRTIO_PCI_ISR_STATUS")
expect(runtime).to_contain("rt_avail_push(dev->avail")
expect(backend).to_contain("poll_event: fn() -> VirtioInputEvent?")
expect(backend).to_contain("delivered_pointer_irq_status")
```

</details>

#### should bridge only RV64 PCI sectors into the shared FAT32 path

- should bridge only RV64 PCI sectors into the shared FAT32 path
- Inspect the RV64 read-only VirtIO block adapter contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bridge only RV64 PCI sectors into the shared FAT32 path")
step("Inspect the RV64 read-only VirtIO block adapter contract")
val storage = rv64_font_storage_source()
expect(storage).to_contain("class Riscv64VirtioBlkAdapter")
expect(storage).to_contain("rt_riscv64_virtio_blk_fat32_init")
expect(storage).to_contain("rt_riscv64_virtio_blk_fat32_read_sector_bytes")
expect(storage).to_contain("riscv64 virtio-blk FAT32 media is read-only")
expect(storage).to_not_contain("rt_arm_virtio_blk")
```

</details>

#### should reject a one-byte-corrupted crop in the parser calibration

- should reject a one-byte-corrupted crop in the parser calibration
- Run the RV64 font and input evidence parser self-test


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a one-byte-corrupted crop in the parser calibration")
step("Run the RV64 font and input evidence parser self-test")
expect(run_wrapper_contract_self_test()).to_contain(
    "rv64_display_smoke_qmp_self_test=pass"
)
```

</details>

#### should render the pinned font and correlate QMP input on live RV64

- should render the pinned font and correlate QMP input on live RV64
   - Artifact capture: after_step
- Load the pinned multilingual font manifest
   - Artifact capture: after_step
- Accept exact-face-bound simple-script shaping
   - Artifact capture: after_step
- Trace the production font and event boundary
   - Artifact capture: after_step
- Prepare one shared font batch for 2D and 3D
   - Artifact capture: after_step
- Emit the selected font composite program and plan compilation
   - Artifact capture: after_step
- Submit the boundary output to its canonical consumer
   - Artifact capture: after_step
- Prove native submission and device readback
   - Artifact capture: after_step
- Boot the canonical pure-Simple RV64 production desktop in QEMU
   - Artifact capture: after_step
- Inject keyboard and pointer events through QMP VirtIO input
   - Artifact capture: after_step
- Correlate visible pixels and input with one frame identity
   - Artifact capture: after_step
- Correlate guest IRQ WM state and later frame generations
   - Artifact capture: after_step
- Reject disconnected stale or replayed evidence
   - Artifact capture: after_step
- Capture and verify the exact RV64 glyph crop and corrupt-copy rejection
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render the pinned font and correlate QMP input on live RV64")
step("Load the pinned multilingual font manifest")
step("Accept exact-face-bound simple-script shaping")
step("Trace the production font and event boundary")
step("Prepare one shared font batch for 2D and 3D")
step("Emit the selected font composite program and plan compilation")
step("Submit the boundary output to its canonical consumer")
step("Prove native submission and device readback")
step("Boot the canonical pure-Simple RV64 production desktop in QEMU")
step("Inject keyboard and pointer events through QMP VirtIO input")
step("Correlate visible pixels and input with one frame identity")
step("Correlate guest IRQ WM state and later frame generations")
step("Reject disconnected stale or replayed evidence")
step("Capture and verify the exact RV64 glyph crop and corrupt-copy rejection")
val (out, err, code) = process_run(
    "/usr/bin/env",
    [
        "RV64_DISPLAY_SMOKE_BUILD=0",
        "/bin/sh",
        "scripts/check/check-rv64-display-smoke-qmp-evidence.shs",
        "--wm-font-input"
    ]
)
expect(code).to_equal(0)
expect(out).to_contain("rv64_display_smoke_qmp_status=pass")
expect(out).to_contain("rv64_display_smoke_qmp_scanout_capture_origin=qemu-pmemsave")
expect(out).to_contain("rv64_wm_guest_font_marker=1")
expect(out).to_contain("rv64_wm_unavailable_marker_seen=0")
expect(out).to_contain("rv64_wm_font_corrupt_crop_rejected=1")
expect(out).to_contain("rv64_wm_keyboard_correlated=1")
expect(out).to_contain("rv64_wm_pointer_correlated=1")
expect(out).to_contain("rv64_wm_input_frame_changed=1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-7`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `71db44f5b6a565d7864279fbd83b2b7d733145ec6903f219bb7981c03254897c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71db44f5b6a565d7864279fbd83b2b7d733145ec6903f219bb7981c03254897c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71db44f5b6a565d7864279fbd83b2b7d733145ec6903f219bb7981c03254897c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl
mirror: doc/06_spec/03_system/os/wm/rv64_simpleos_wm_font_input_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=75 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/os/wm/rv64_simpleos_wm_font_input_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/wm/rv64_simpleos_wm_font_input_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the RV64 gate separate and fail closed on every required proof' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should connect RV64 PCI input through the shared production backend' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should connect RV64 PCI input through the shared production backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:148:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bridge only RV64 PCI sectors into the shared FAT32 path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bridge only RV64 PCI sectors into the shared FAT32 path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:159:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a one-byte-corrupted crop in the parser calibration' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a one-byte-corrupted crop in the parser calibration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl:170:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render the pinned font and correlate QMP input on live RV64' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
