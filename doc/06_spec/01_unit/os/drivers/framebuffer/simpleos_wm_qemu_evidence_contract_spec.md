# Simpleos Wm Qemu Evidence Contract Specification

> Tests covering SimpleOS WM QEMU evidence wrapper contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wm Qemu Evidence Contract Specification

## Scenarios

### SimpleOS WM QEMU evidence wrapper contract

#### hashes every executable artifact and rechecks it before pass

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hashes every executable artifact and rechecks it before pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("hashes every executable artifact and rechecks it before pass")
val src = _wrapper_source()
expect(src).to_contain("simpleos_wm_fullscreen_wrapper=$WRAPPER")
expect(src).to_contain("simpleos_wm_fullscreen_wrapper_sha256=$WRAPPER_SHA256")
expect(src).to_contain("simpleos_wm_fullscreen_wrapper_bundle_sha256=$WRAPPER_BUNDLE_SHA256")
expect(src).to_contain("wrapper_bundle_sha256=$WRAPPER_BUNDLE_SHA256")
expect(src).to_contain("wrapper_bundle_sha256_now=\"$(wrapper_bundle_sha256 || true)\"")
expect(src).to_contain("simpleos_wm_fullscreen_kernel=$KERNEL_OUTPUT")
expect(src).to_contain("simpleos_wm_fullscreen_kernel_sha256=$KERNEL_SHA256")
expect(src).to_contain("simpleos_wm_fullscreen_disk_image=$DISK_IMAGE")
expect(src).to_contain("simpleos_wm_fullscreen_disk_image_sha256=$DISK_IMAGE_SHA256")
expect(src).to_contain("WRAPPER_SHA256=\"$(file_sha256 \"$WRAPPER\")\"")
expect(src).to_contain("KERNEL_SHA256=\"$(file_sha256 \"$KERNEL_OUTPUT\")\"")
expect(src).to_contain("DISK_IMAGE_SHA256=\"$(file_sha256 \"$DISK_IMAGE\")\"")
expect(src).to_contain("if [ \"$status\" = pass ]; then")
expect(src).to_contain("wrapper_sha256_now=\"$(file_sha256 \"$WRAPPER\")\"")
expect(src).to_contain("kernel_sha256_now=\"$(file_sha256 \"$KERNEL_OUTPUT\")\"")
expect(src).to_contain("disk_image_sha256_now=\"$(file_sha256 \"$DISK_IMAGE\")\"")
expect(src).to_contain("reason=artifact-sha256-mismatch")
```

</details>

#### invalidates a cached kernel when any owned source dependency changes

- invalidates a cached kernel when any owned source dependency changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("invalidates a cached kernel when any owned source dependency changes")
val src = _wrapper_source()
expect(src).to_contain("find src/os src/lib build/os/generated examples/09_embedded/simple_os/arch/x86_64")
expect(src).to_contain("-newer \"$KERNEL_OUTPUT\"")
```

</details>

#### derives pmem capture geometry from validated guest scanout metadata

- derives pmem capture geometry from validated guest scanout metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("derives pmem capture geometry from validated guest scanout metadata")
val src = _wrapper_source()
expect(src).to_contain("marker_line \"$SERIAL_LOG\" \"[scanout-evidence]\"")
expect(src).to_contain("scanout_size=$((scanout_stride * scanout_height))")
expect(src).to_contain("scanout_end=$((scanout_address + scanout_size))")
expect(src).to_contain("'pmemsave %d %d")
expect(src).to_contain("for y in range(height)")
expect(src).to_contain("row = y * pitch")
expect(src.contains("pmemsave 0xfd000000 3145728")).to_be(false)
expect(src.contains("P6\\n1024 768")).to_be(false)
```

</details>

#### should require the cross-verified canonical taskbar clock DrawIR crop

- should require the cross-verified canonical taskbar clock DrawIR crop


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should require the cross-verified canonical taskbar clock DrawIR crop")
val src = _wrapper_source()
val guest = rt_file_read_text(GUEST_ENTRY)
val native = rt_file_read_text(NATIVE_FONT_EVIDENCE)
val expected_hash = "addf76edf6d23ca9bea6d698ca1d30bc4bd8dd684bb50ff3158ef755bd2854fc"
expect(src).to_contain("FONT_REGION_EXPECTED_BYTES=8064")
expect(src).to_contain("for y in range(height - 48, height)")
expect(src).to_contain("for x in range(width - 56, width)")
expect(src).to_contain("FONT_REGION_EXPECTED_SHA256=" + expected_hash)
expect(src).to_contain("[font-evidence] guest_path=$FONT_GUEST_PATH asset_bytes=$FONT_ASSET_EXPECTED_BYTES family=Noto Sans Mono asset_sha256=$FONT_ASSET_EXPECTED_SHA256 raster=pure-sfnt-glyf route=shared-wm-draw-ir component_id=taskbar-clock font_size=12 text=00:00 region=right56,bottom48 region_rgb_sha256=$FONT_REGION_EXPECTED_SHA256")
expect(guest).to_contain("route=shared-wm-draw-ir component_id=taskbar-clock")
expect(guest).to_contain("fn taskbar_clock_region_rgb_sha256_pin() -> text:")
expect(guest).to_contain("    \"" + expected_hash + "\"")
expect(guest).to_contain("val pinned_region_sha256: text = taskbar_clock_region_rgb_sha256_pin()")
expect(guest).to_contain("region_sha256 == pinned_region_sha256")
expect(native).to_contain("val FONT_REGION_RGB_SHA256 = \"" + expected_hash + "\"")
expect(guest).to_contain("[font-evidence] guest_path={font_guest_path} asset_bytes={font_blob.len()} family=Noto Sans Mono asset_sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081 raster=pure-sfnt-glyf route=shared-wm-draw-ir component_id=taskbar-clock font_size=12 text=00:00 region=right56,bottom48 region_rgb_sha256={region_sha256}")
expect(guest.contains("engine.draw_text(64, 64")).to_be(false)
```

</details>

#### injects emulated input and maps host nonce to guest sequence evidence

- injects emulated input and maps host nonce to guest sequence evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("injects emulated input and maps host nonce to guest sequence evidence")
val src = _wrapper_source()
expect(src).to_contain("\"execute\":\"input-send-event\"")
expect(src).to_contain("data\":\"f11\"")
expect(src).to_contain("\"type\":\"rel\"")
expect(src).to_contain("\"type\":\"btn\"")
expect(src).to_contain("baseline_seq = max_input_seq()")
expect(src).to_contain("wait_correlation(baseline_seq, \"maximize\")")
expect(src).to_contain("wait_correlation(max_seq, \"restore\", target_window)")
expect(src).to_contain("wait_pointer_correlation(restore_seq, 1)")
expect(src).to_contain("wait_pointer_correlation(pointer_seq, 2)")
expect(src).to_contain("ENTRY=\"examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl\"")
expect(src).to_contain("host_nonce=%s baseline_seq=%d maximize_seq=%d restore_seq=%d")
expect(src.contains("marker_line \"$SERIAL_LOG\" \"[wm-demo] fullscreen-enter\"")).to_be(false)
expect(src.contains("marker_line \"$SERIAL_LOG\" \"[wm-demo] fullscreen-exit\"")).to_be(false)
```

</details>

#### fails closed on QMP input capture and metadata errors

- fails closed on QMP input capture and metadata errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed on QMP input capture and metadata errors")
val src = _wrapper_source()
expect(src).to_contain("dynamic-scanout-metadata-invalid")
expect(src).to_contain("dynamic-scanout-bounds-or-byte-pitch-invalid")
expect(src).to_contain("dynamic-scanout-address-range-invalid")
expect(src).to_contain("capture-input-or-guest-correlation-failed")
expect(src).to_contain("if \"error\" in reply")
```

</details>

#### distinguishes a self-hosted compiler crash from an ordinary build rejection

- distinguishes a self-hosted compiler crash from an ordinary build rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("distinguishes a self-hosted compiler crash from an ordinary build rejection")
val src = _wrapper_source()
expect(src).to_contain("if [ \"$build_code\" -eq 124 ] or [ \"$build_code\" -eq 137 ]")
expect(src).to_contain("elif [ \"$build_code\" -eq 139 ]; then")
expect(src).to_contain("KERNEL_BUILD_STATUS=compiler-crash-signal-11-cache-preserved")
```

</details>

#### loads the OVMF video modules before GRUB hands off to the kernel

- loads the OVMF video modules before GRUB hands off to the kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("loads the OVMF video modules before GRUB hands off to the kernel")
val src = _wrapper_source()
expect(src).to_contain("insmod efi_gop")
expect(src).to_contain("insmod all_video")
expect(src).to_contain("set gfxpayload=text")
expect(src).to_contain("--modules=\"multiboot normal echo part_gpt fat efi_gop efi_uga all_video gfxterm video_bochs video_fb\"")
```

</details>

#### uses guest monotonic input sequence for live F11 maximize and restore

- uses guest monotonic input sequence for live F11 maximize and restore


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses guest monotonic input sequence for live F11 maximize and restore")
val entry = rt_file_read_text(GUEST_ENTRY)
val compositor = rt_file_read_text(GUEST_COMPOSITOR)
val shell = rt_file_read_text(GUEST_SHELL)
expect(entry).to_contain("shell.run_baremetal(wm_frame_executor)")
expect(compositor).to_contain("elif sc == 0x57")
expect(compositor).to_contain("self.input_sequence = self.input_sequence + 1")
expect(shell).to_contain("[wm-input-irq] input_seq=")
expect(shell).to_contain("self.compositor.maximize_window")
expect(shell).to_contain("self.compositor.restore_window")
expect(shell).to_contain("[wm-frame] input_seq=")
```

</details>

#### routes AUX pointer packets through the shared guest sequence and frame owner

- routes AUX pointer packets through the shared guest sequence and frame owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes AUX pointer packets through the shared guest sequence and frame owner")
val wrapper = _wrapper_source()
val compositor = rt_file_read_text(GUEST_COMPOSITOR)
val shell = rt_file_read_text(GUEST_SHELL)
expect(compositor).to_contain("if ((status as i32) & 0x20) != 0:")
expect(compositor).to_contain("self.input_sequence = self.input_sequence + 1")
expect(shell).to_contain("[wm-pointer-irq] input_seq=")
expect(shell).to_contain("[wm-pointer-state] input_seq=")
expect(shell).to_contain("[wm-pointer-frame] input_seq=")
expect(shell).to_contain("handled={handled_text}")
expect(shell).to_contain("maximized={maximized_text} x={state_x} y={state_y} width={state_width} height={state_height}")
expect(wrapper).to_contain("guest-pointer-irq-state-frame-correlation-missing")
expect(wrapper).to_contain("window_focus|window_drag_begin")
expect(wrapper).to_contain("window=\\1 handled=true")
expect(wrapper).to_contain("command=ignored target= app= window= handled=false")
expect(wrapper).to_contain("simpleos_wm_fullscreen_pointer_input_seq=")
expect(wrapper).to_contain("simpleos_wm_fullscreen_pointer_release_input_seq=")
```

</details>

#### rejects a one-byte corrupt copy through the production font crop oracle

- rejects a one-byte corrupt copy through the production font crop oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a one-byte corrupt copy through the production font crop oracle")
val wrapper = _wrapper_source()
expect(wrapper).to_contain("corrupt_region[0] ^= 1")
expect(wrapper).to_contain("font_region_oracle_status()")
expect(wrapper).to_contain("font_region_corrupt_copy_bytes")
expect(wrapper).to_contain("font_region_oracle_status \"$FONT_REGION_CORRUPT_COPY\"")
expect(wrapper).to_contain("font-region-corrupt-copy-calibration-failed")
expect(wrapper).to_contain("simpleos_wm_fullscreen_font_region_corrupt_rejection_status=")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS WM QEMU evidence wrapper contract.
- SimpleOS WM QEMU evidence wrapper contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c54a01a4b1a0ac685cd43d9d60a71aa6184ed6881732a504b634710700219d52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c54a01a4b1a0ac685cd43d9d60a71aa6184ed6881732a504b634710700219d52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c54a01a4b1a0ac685cd43d9d60a71aa6184ed6881732a504b634710700219d52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hashes every executable artifact and rechecks it before pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates a cached kernel when any owned source dependency changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives pmem capture geometry from validated guest scanout metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require the cross-verified canonical taskbar clock DrawIR crop' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
