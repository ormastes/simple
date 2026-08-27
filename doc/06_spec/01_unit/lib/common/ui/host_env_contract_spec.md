# Host Env Contract Specification

> Tests covering host environment evidence contract, render pipeline evidence contract, live framebuffer evidence classification, host evidence classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Env Contract Specification

## Scenarios

### host environment evidence contract

#### accepts exactly the required capability rows and explicit cross-host blockers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts exactly the required capability rows and explicit cross-host blockers
   - Expected: complete_env().validation_reason() equals ``
   - Expected: complete_env().ready() is false
   - Expected: TestHostEnv.create([]).ready() is false
   - Expected: ready.ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts exactly the required capability rows and explicit cross-host blockers")
expect(complete_env().validation_reason()).to_equal("")
expect(complete_env().ready()).to_equal(false)
expect(TestHostEnv.create([]).ready()).to_equal(false)
val ready = TestHostEnv.create([
    row("x86_simd", "pass"),
    row("arm_simd", "pass"),
    row("riscv_simd", "pass"),
    row("vulkan", "pass"),
    row("renderdoc", "pass"),
    row("display_input", "pass"),
    row("framebuffer_readback", "pass")
])
expect(ready.ready()).to_equal(true)
```

</details>

#### rejects missing, duplicate, and unknown capability rows

- rejects missing, duplicate, and unknown capability rows
   - Expected: TestHostEnv.create([]).validation_reason() equals `missing-x86_simd`
   - Expected: duplicated.validation_reason() equals `duplicate-vulkan`
   - Expected: unknown.validation_reason() equals `unknown-cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects missing, duplicate, and unknown capability rows")
expect(TestHostEnv.create([]).validation_reason()).to_equal("missing-x86_simd")
val duplicated = complete_env().with_row(row("vulkan", "pass"))
expect(duplicated.validation_reason()).to_equal("duplicate-vulkan")
val unknown = complete_env().with_row(row("cuda", "pass"))
expect(unknown.validation_reason()).to_equal("unknown-cuda")
```

</details>

#### requires actionable evidence for every capability status

- requires actionable evidence for every capability status
   - Expected: row("vulkan", "maybe").validation_reason() equals `invalid-status`
   - Expected: row("vulkan", "pass", "unexpected").validation_reason() equals `pass-has-reason`
   - Expected: HostCapabilityRow.create("vulkan", "pass", "", "", "").validation_reason() equals `missing-evidence-path`
   - Expected: row("arm_simd", "blocked").validation_reason() equals `blocked-without-reason`
   - Expected: row("x86_simd", "fail").validation_reason() equals `fail-without-reason`
   - Expected: row("arm_simd", "blocked", "arm-host-required").validation_reason() equals `blocked-without-resume-command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires actionable evidence for every capability status")
expect(row("vulkan", "maybe").validation_reason()).to_equal("invalid-status")
expect(row("vulkan", "pass", "unexpected").validation_reason()).to_equal("pass-has-reason")
expect(HostCapabilityRow.create("vulkan", "pass", "", "", "").validation_reason()).to_equal("missing-evidence-path")
expect(row("arm_simd", "blocked").validation_reason()).to_equal("blocked-without-reason")
expect(row("x86_simd", "fail").validation_reason()).to_equal("fail-without-reason")
expect(row("arm_simd", "blocked", "arm-host-required").validation_reason()).to_equal("blocked-without-resume-command")
```

</details>

#### covers accepted fail rows, nested row errors, and aggregate serialization

- covers accepted fail rows, nested row errors, and aggregate serialization
   - Expected: row("x86_simd", "fail", "probe-failed").validation_reason() equals ``
   - Expected: TestHostEnv.create([row("x86_simd", "maybe")]).validation_reason() equals `x86_simd-invalid-status`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers accepted fail rows, nested row errors, and aggregate serialization")
expect(row("x86_simd", "fail", "probe-failed").validation_reason()).to_equal("")
expect(TestHostEnv.create([row("x86_simd", "maybe")]).validation_reason()).to_equal("x86_simd-invalid-status")
val json = complete_env().to_json()
expect(json).to_contain("\"schema\":\"simple-test-host-env-v1\"")
expect(json).to_contain("\"name\":\"framebuffer_readback\"")
```

</details>

#### distinguishes valid invalid and absent retained evidence

- distinguishes valid invalid and absent retained evidence
   - Expected: passed.status equals `pass`
   - Expected: passed.reason equals ``
   - Expected: passed.resume_command equals ``
   - Expected: failed.status equals `fail`
   - Expected: failed.validation_reason() equals ``
   - Expected: blocked.status equals `blocked`
   - Expected: blocked.validation_reason() equals ``
   - Expected: missing_despite_valid.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinguishes valid invalid and absent retained evidence")
val passed = host_capability_row_from_evidence(
    "renderdoc", true, true, "invalid-renderdoc", "build/renderdoc/evidence.env", "rerun-renderdoc")
val failed = host_capability_row_from_evidence(
    "renderdoc", false, true, "invalid-renderdoc", "build/renderdoc/evidence.env", "rerun-renderdoc")
val blocked = host_capability_row_from_evidence(
    "renderdoc", false, false, "missing-renderdoc", "build/renderdoc/evidence.env", "rerun-renderdoc")
val missing_despite_valid = host_capability_row_from_evidence(
    "renderdoc", true, false, "missing-renderdoc", "build/renderdoc/evidence.env", "rerun-renderdoc")
expect(passed.status).to_equal("pass")
expect(passed.reason).to_equal("")
expect(passed.resume_command).to_equal("")
expect(failed.status).to_equal("fail")
expect(failed.validation_reason()).to_equal("")
expect(blocked.status).to_equal("blocked")
expect(blocked.validation_reason()).to_equal("")
expect(missing_despite_valid.status).to_equal("blocked")
```

</details>

### render pipeline evidence contract

#### accepts a correlated completed device readback

- accepts a correlated completed device readback
   - Expected: receipt().validation_reason() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a correlated completed device readback")
expect(receipt().validation_reason()).to_equal("")
```

</details>

#### fails closed on disconnected event, frame, and mutation identities

- fails closed on disconnected event, frame, and mutation identities
   - Expected: receipt(event_id: 0).validation_reason() equals `missing-event-id`
   - Expected: receipt(frame_id: 8).validation_reason() equals `event-frame-mismatch`
   - Expected: RenderPipelineReceipt.create(7, 7, 0, "vulkan", 41, true, "device_readback", 64, 48, 256, "argb8888", 99, 12, false).validation_reason() equals `missing-mutation-revision`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on disconnected event, frame, and mutation identities")
expect(receipt(event_id: 0).validation_reason()).to_equal("missing-event-id")
expect(receipt(frame_id: 8).validation_reason()).to_equal("event-frame-mismatch")
expect(RenderPipelineReceipt.create(7, 7, 0, "vulkan", 41, true, "device_readback", 64, 48, 256, "argb8888", 99, 12, false).validation_reason()).to_equal("missing-mutation-revision")
```

</details>

#### rejects fallback, synthetic, incomplete, and CPU-mirror backend proof

- rejects fallback, synthetic, incomplete, and CPU-mirror backend proof
   - Expected: receipt(fallback: true).validation_reason() equals `fallback-used`
   - Expected: receipt(backend: "cpu").validation_reason() equals `not-vulkan-backend`
   - Expected: receipt(handle: 0).validation_reason() equals `missing-backend-handle`
   - Expected: receipt(completed: false).validation_reason() equals `submission-incomplete`
   - Expected: receipt(source: "cpu_mirror").validation_reason() equals `not-device-readback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects fallback, synthetic, incomplete, and CPU-mirror backend proof")
expect(receipt(fallback: true).validation_reason()).to_equal("fallback-used")
expect(receipt(backend: "cpu").validation_reason()).to_equal("not-vulkan-backend")
expect(receipt(handle: 0).validation_reason()).to_equal("missing-backend-handle")
expect(receipt(completed: false).validation_reason()).to_equal("submission-incomplete")
expect(receipt(source: "cpu_mirror").validation_reason()).to_equal("not-device-readback")
```

</details>

#### rejects malformed or blank framebuffer proof

- rejects malformed or blank framebuffer proof
   - Expected: receipt(width: 0).validation_reason() equals `invalid-dimensions`
   - Expected: receipt(height: 0).validation_reason() equals `invalid-dimensions`
   - Expected: receipt(stride: 64).validation_reason() equals `invalid-stride`
   - Expected: RenderPipelineReceipt.create(7, 7, 3, "vulkan", 41, true, "device_readback", 64, 48, 256, "rgba8888", 99, 12, false).validation_reason() equals `invalid-format`
   - Expected: receipt(checksum: 0).validation_reason() equals `missing-checksum`
   - Expected: receipt(nonblank: 0).validation_reason() equals `blank-frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed or blank framebuffer proof")
expect(receipt(width: 0).validation_reason()).to_equal("invalid-dimensions")
expect(receipt(height: 0).validation_reason()).to_equal("invalid-dimensions")
expect(receipt(stride: 64).validation_reason()).to_equal("invalid-stride")
expect(RenderPipelineReceipt.create(7, 7, 3, "vulkan", 41, true, "device_readback", 64, 48, 256, "rgba8888", 99, 12, false).validation_reason()).to_equal("invalid-format")
expect(receipt(checksum: 0).validation_reason()).to_equal("missing-checksum")
expect(receipt(nonblank: 0).validation_reason()).to_equal("blank-frame")
```

</details>

### live framebuffer evidence classification

#### accepts only a forward Vulkan device frame tied to the screen event receipt

- accepts only a forward Vulkan device frame tied to the screen event receipt
   - Expected: baseline_path equals `/tmp/baseline.ppm`
   - Expected: baseline_sha equals `aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa`
   - Expected: input_path equals `/tmp/input.ppm`
   - Expected: input_sha equals `bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb`
   - Expected: duplicate_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only a forward Vulkan device frame tied to the screen event receipt")
val complete = complete_readback_evidence()
val (baseline_path, baseline_sha, input_path, input_sha) = host_readback_capture_bindings(complete)
expect(baseline_path).to_equal("/tmp/baseline.ppm")
expect(baseline_sha).to_equal("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
expect(input_path).to_equal("/tmp/input.ppm")
expect(input_sha).to_equal("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
val (duplicate_path, _, _, _) = host_readback_capture_bindings(
    complete + "\nlinux_hosted_wm_live_window_baseline_capture=/tmp/stale.ppm")
expect(duplicate_path).to_equal("")
expect(host_readback_evidence_passes(complete)).to_be(true)
expect(host_readback_evidence_passes(complete.replace("event_origin=screen", "event_origin=synthetic"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("framebuffer_status=pass", "framebuffer_status=fail"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("glyph_crop_status=pass", "glyph_crop_status=fail"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("glyph_crop_expected_sha256=cccc", "glyph_crop_expected_sha256=dddd"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("glyph_crop_live_match=true", "glyph_crop_live_match=false"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("baseline_nonce=1", "baseline_nonce=2"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_revision=8", "input_revision=7"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_revision=8", "input_revision=6"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("baseline_revision=7", "baseline_revision=999999999999999999999999999999"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_frame_checksum=101", "input_frame_checksum=99"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_backend=vulkan", "input_backend=cpu"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("baseline_backend=vulkan", "baseline_backend=cpu").replace("input_backend=vulkan", "input_backend=cpu"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("baseline_readback_source=device_readback", "baseline_readback_source=cpu_mirror"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_backend_handle=41", "input_backend_handle=42"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_render_event_id=7", "input_render_event_id=8"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_render_mutation_revision=1", "input_render_mutation_revision=2"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_composition_id=wm-composite", "input_composition_id=other"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_web_content_image_count=1", "input_web_content_image_count=0"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_readback_completed=true", "input_readback_completed="))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_readback_width=1024", "input_readback_width=1023"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_readback_height=720", "input_readback_height=719"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_readback_stride=4096", "input_readback_stride=4092"))).to_be(false)
expect(host_readback_evidence_passes(complete.replace("input_readback_format=argb8888", "input_readback_format=rgba8888"))).to_be(false)
expect(host_readback_evidence_passes(complete + "\nlinux_hosted_wm_live_window_input_composition_id=wm-composite")).to_be(false)
expect(host_readback_evidence_passes(complete + "\nlinux_hosted_wm_live_window_input_web_content_image_count=1")).to_be(false)
expect(host_readback_evidence_passes(complete.replace(
    "input_capture_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
    "input_capture_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
))).to_be(false)
expect(host_readback_evidence_passes(complete + "\nlinux_hosted_wm_live_window_input_revision=9")).to_be(false)
```

</details>

### host evidence classification

#### admits only retained native SIMD receipts across coordinator architectures

- admits only retained native SIMD receipts across coordinator architectures
   - Expected: arm.status equals `pass`
   - Expected: riscv.status equals `pass`
   - Expected: emulated.status equals `blocked`
   - Expected: emulated.reason equals `complete-retained-native-aarch64-simd-frame-evidence-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits only retained native SIMD receipts across coordinator architectures")
val arm = host_simd_capability_row(
    "arm_simd", complete_simd_evidence("aarch64", "neon"),
    "aarch64", "neon", "build/evidence/arm.env"
)
val riscv = host_simd_capability_row(
    "riscv_simd", complete_simd_evidence("riscv64", "rvv"),
    "riscv64", "rvv", "build/evidence/riscv.env"
)
val emulated = host_simd_capability_row(
    "arm_simd",
    complete_simd_evidence("aarch64", "neon").replace("execution_environment=native_host", "execution_environment=emulated"),
    "aarch64", "neon", "build/evidence/arm.env"
)
expect(arm.status).to_equal("pass")
expect(riscv.status).to_equal("pass")
expect(emulated.status).to_equal("blocked")
expect(emulated.reason).to_equal("complete-retained-native-aarch64-simd-frame-evidence-required")
```

</details>

#### requires the complete retained x86 SIMD rendering receipt

- requires the complete retained x86 SIMD rendering receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires the complete retained x86 SIMD rendering receipt")
val complete = complete_simd_evidence()
expect(host_x86_simd_evidence_passes(complete)).to_be(true)
expect(host_x86_simd_evidence_passes(complete.replace("feature=avx2", "feature=sse42"))).to_be(true)
expect(host_simd_evidence_passes(complete_simd_evidence("aarch64", "neon"), "aarch64", "neon")).to_be(true)
expect(host_simd_evidence_passes(complete_simd_evidence("riscv64", "rvv"), "riscv64", "rvv")).to_be(true)
expect(host_simd_evidence_passes(complete, "unknown", "avx2")).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("status=pass", "status=fail"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("simple_bin_status=pass", "simple_bin_status=fail"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("arch=x86_64", "arch=aarch64"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("feature=avx2", "feature=scalar"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("execution_environment=native_host", "execution_environment=emulated"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("native_simd_executed=true", "native_simd_executed=false"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("native_simd_bit_exact=true", "native_simd_bit_exact=false"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("native_simd_hits=2", "native_simd_hits=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("canonical_source_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "canonical_source_sha256=bad"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("compiler_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", "compiler_sha256=0000000000000000000000000000000000000000000000000000000000000000"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("frame_receipt_sha256=cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc", "frame_receipt_sha256=CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("evidence_checksum=99", "evidence_checksum=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("fill_actual_checksum=101", "fill_actual_checksum=102"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("copy_actual_checksum=202", "copy_actual_checksum=203"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("alpha_actual_checksum=303", "alpha_actual_checksum=304"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("alpha_edge_actual_checksum=404", "alpha_edge_actual_checksum=405"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("scroll_actual_checksum=505", "scroll_actual_checksum=506"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("fill_mismatch_count=0", "fill_mismatch_count=1"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("copy_mismatch_count=0", "copy_mismatch_count=1"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("alpha_mismatch_count=0", "alpha_mismatch_count=1"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("alpha_edge_mismatch_count=0", "alpha_edge_mismatch_count=1"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("scroll_mismatch_count=0", "scroll_mismatch_count=1"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("diagram_pixel_count=192", "diagram_pixel_count=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("diagram_actual_checksum=606", "diagram_actual_checksum=607"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("diagram_mismatch_count=0", "diagram_mismatch_count=1"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("diagram_fill_hits=5", "diagram_fill_hits=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("diagram_copy_hits=3", "diagram_copy_hits=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("diagram_alpha_hits=5", "diagram_alpha_hits=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("diagram_blit_hits=1", "diagram_blit_hits=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("diagram_scroll_hits=3", "diagram_scroll_hits=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("facade_draw_image_clip_mask_status=pass", "facade_draw_image_clip_mask_status=fail"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("facade_draw_image_clip_mask_examples=2", "facade_draw_image_clip_mask_examples=0"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("facade_draw_image_clip_mask_failures=0", "facade_draw_image_clip_mask_failures=1"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("policy=exact-bitmap-no-blur-no-tolerance", "policy=tolerant"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete.replace("blur_or_tolerance_used=false", "blur_or_tolerance_used=true"))).to_be(false)
expect(host_x86_simd_evidence_passes(complete + "\ncpu_simd_evidence_status=pass")).to_be(false)
```

</details>

#### binds SIMD artifacts and the exact frame receipt payload without duplicate keys

- binds SIMD artifacts and the exact frame receipt payload without duplicate keys
   - Expected: compiler_path equals `/tmp/simple-simd-compiler`
   - Expected: source_sha equals `aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa`
   - Expected: compiler_sha equals `bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb`
   - Expected: receipt_sha equals `cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc`
   - Expected: duplicate_compiler_path equals ``
   - Expected: duplicate_source_sha equals ``
   - Expected: duplicate_compiler_sha equals ``
   - Expected: duplicate_payload equals ``
   - Expected: duplicate_receipt_sha equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds SIMD artifacts and the exact frame receipt payload without duplicate keys")
val complete = complete_simd_evidence()
val (compiler_path, source_sha, compiler_sha) = host_simd_artifact_bindings(complete)
val (payload, receipt_sha) = host_simd_frame_receipt_binding(complete)
expect(compiler_path).to_equal("/tmp/simple-simd-compiler")
expect(source_sha).to_equal("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
expect(compiler_sha).to_equal("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
expect(payload).to_equal(
    "arch=x86_64\n" +
    "feature=avx2\n" +
    "execution_environment=native_host\n" +
    "diagram_actual_checksum=606\n" +
    "canonical_source_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n" +
    "compiler_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"
)
expect(receipt_sha).to_equal("cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
val duplicate_path = complete + "\ncpu_simd_evidence_simple_bin=/tmp/other-simple"
val (duplicate_compiler_path, duplicate_source_sha, duplicate_compiler_sha) =
    host_simd_artifact_bindings(duplicate_path)
expect(duplicate_compiler_path).to_equal("")
expect(duplicate_source_sha).to_equal("")
expect(duplicate_compiler_sha).to_equal("")
val duplicate_receipt = complete + "\ncpu_simd_evidence_arch=x86_64"
val (duplicate_payload, duplicate_receipt_sha) = host_simd_frame_receipt_binding(duplicate_receipt)
expect(duplicate_payload).to_equal("")
expect(duplicate_receipt_sha).to_equal("")
```

</details>

#### requires complete Vulkan device readback evidence

- requires complete Vulkan device readback evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires complete Vulkan device readback evidence")
val complete = "vulkan_engine2d_readback_status=pass\n" +
    "vulkan_engine2d_readback_spec_status=pass\n" +
    "vulkan_engine2d_readback_available=true\n" +
    "vulkan_engine2d_readback_backend_name=vulkan\n" +
    "vulkan_engine2d_readback_present_exercised=true\n" +
    "vulkan_engine2d_readback_readback_exercised=true\n" +
    "vulkan_engine2d_readback_clear_status=pass\n" +
    "vulkan_engine2d_readback_rect_status=pass\n" +
    "vulkan_engine2d_readback_clear_pixels=256\n" +
    "vulkan_engine2d_readback_rect_pixels=256\n" +
    "vulkan_engine2d_readback_clear_expected_checksum=140735349260160\n" +
    "vulkan_engine2d_readback_clear_actual_checksum=140735349260160\n" +
    "vulkan_engine2d_readback_rect_expected_checksum=140781974135910\n" +
    "vulkan_engine2d_readback_rect_actual_checksum=140781974135910\n" +
    "vulkan_engine2d_readback_clear_mismatches=0\n" +
    "vulkan_engine2d_readback_rect_mismatches=0\n" +
    "vulkan_engine2d_readback_clear_source=device_readback\n" +
    "vulkan_engine2d_readback_rect_source=device_readback\n" +
    "vulkan_engine2d_readback_clear_backend_handle=41\n" +
    "vulkan_engine2d_readback_rect_backend_handle=42\n" +
    "vulkan_engine2d_readback_clear_device_identity=7\n" +
    "vulkan_engine2d_readback_rect_device_identity=7\n" +
    "vulkan_engine2d_readback_blur_or_tolerance_used=false\n" +
    "vulkan_engine2d_readback_vulkan_strict_exit_code=0\n" +
    "vulkan_engine2d_readback_cpu_vulkan_parity_exit_code=0"
expect(host_vulkan_evidence_passes(complete)).to_be(true)
expect(host_vulkan_evidence_passes(complete.replace("readback_status=pass", "readback_status=fail"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("spec_status=pass", "spec_status=fail"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("available=true", "available=false"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("backend_name=vulkan", "backend_name=cpu"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("present_exercised=true", "present_exercised=false"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("readback_exercised=true", "readback_exercised=false"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_status=pass", "clear_status=fail"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_status=pass", "rect_status=fail"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_pixels=256", "clear_pixels=255"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_pixels=256", "clear_pixels=257"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_pixels=256", "rect_pixels=255"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_pixels=256", "rect_pixels=257"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_actual_checksum=140735349260160", "clear_actual_checksum=140735349260161"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_actual_checksum=140781974135910", "rect_actual_checksum=140781974135911"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_expected_checksum=140735349260160", "clear_expected_checksum=140735349260161").replace("clear_actual_checksum=140735349260160", "clear_actual_checksum=140735349260161"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_expected_checksum=140781974135910", "rect_expected_checksum=140781974135911").replace("rect_actual_checksum=140781974135910", "rect_actual_checksum=140781974135911"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_mismatches=0", "clear_mismatches=1"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_mismatches=0", "rect_mismatches=1"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_source=device_readback", "clear_source=cpu_mirror"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_source=device_readback", "rect_source=cpu_mirror"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_backend_handle=41", "clear_backend_handle=0"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_backend_handle=41", "clear_backend_handle=-1"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_backend_handle=41", "clear_backend_handle=41x"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_backend_handle=41", "clear_backend_handle="))).to_be(false)
expect(host_vulkan_evidence_passes(complete + "\nvulkan_engine2d_readback_clear_backend_handle=43")).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_backend_handle=42", "rect_backend_handle=0"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("clear_device_identity=7", "clear_device_identity=0"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_device_identity=7", "rect_device_identity=0"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("rect_device_identity=7", "rect_device_identity=8"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("blur_or_tolerance_used=false", "blur_or_tolerance_used=true"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("vulkan_strict_exit_code=0", "vulkan_strict_exit_code=1"))).to_be(false)
expect(host_vulkan_evidence_passes(complete.replace("cpu_vulkan_parity_exit_code=0", "cpu_vulkan_parity_exit_code=1"))).to_be(false)
expect(host_vulkan_evidence_passes(complete + "\nvulkan_engine2d_readback_status=fail")).to_be(false)
```

</details>

#### requires browser Vulkan backing and exact three-way ARGB parity

- requires browser Vulkan backing and exact three-way ARGB parity
- Reject incomplete or non-Vulkan browser receipts
- Reject unbound, mismatched, or blank ARGB artifacts
- Reject any missing or nonzero pairwise result and aggregate failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires browser Vulkan backing and exact three-way ARGB parity")
val browser = complete_browser_vulkan_evidence()
val run = complete_browser_vulkan_parity_run_evidence()
expect(host_browser_vulkan_parity_evidence_passes(browser, run)).to_be(true)

step("Reject incomplete or non-Vulkan browser receipts")
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("browser_backing_mode=gpu-feature-status", "browser_backing_mode=unknown"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("gui_web_2d_vulkan_browser_backing_status=pass", "gui_web_2d_vulkan_browser_backing_status=fail"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_status=pass", "electron_browser_backing_status=fail"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_browser_target_gpu_info_status=pass", "electron_browser_backing_browser_target_gpu_info_status=fail"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_vulkan=enabled", "electron_browser_backing_vulkan=disabled"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_gpu_compositing=enabled", "electron_browser_backing_gpu_compositing=disabled"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_hardware_supports_vulkan=true", "electron_browser_backing_hardware_supports_vulkan=false"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_source=/tmp/electron-proof.json", "electron_browser_backing_source="), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_source_file_status=pass", "electron_browser_backing_source_file_status=symlink"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_argb_source=/tmp/electron-argb.json", "electron_browser_backing_argb_source="), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("electron_browser_backing_argb_source_file_status=pass", "electron_browser_backing_argb_source_file_status=hardlink"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("chrome_browser_backing_status=pass", "chrome_browser_backing_status=fail"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("chrome_browser_backing_gpu_compositing=enabled", "chrome_browser_backing_gpu_compositing=disabled"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("chrome_browser_backing_hardware_supports_vulkan=true", "chrome_browser_backing_hardware_supports_vulkan=false"), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("chrome_browser_backing_source=/tmp/chrome-proof.json", "chrome_browser_backing_source="), run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser.replace("chrome_browser_backing_source_file_status=pass", "chrome_browser_backing_source_file_status=empty"), run)).to_be(false)

step("Reject unbound, mismatched, or blank ARGB artifacts")
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("gui_web_2d_vulkan_width=1280", "gui_web_2d_vulkan_width=0"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("gui_web_2d_vulkan_height=720", "gui_web_2d_vulkan_height=0"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_status=pass", "electron_argb_status=fail"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_path=/tmp/electron-argb.json", "electron_argb_path="))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_width=1280", "electron_argb_width=1279"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_height=720", "electron_argb_height=719"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_format=argb-u32", "electron_argb_format=rgba-u8"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_pixel_count=921600", "electron_argb_pixel_count=0"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_pixel_count=921600", "electron_argb_pixel_count=921599"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_nonblank_pixel_count=900000", "electron_argb_nonblank_pixel_count=0"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_argb_nonblank_pixel_count=900000", "electron_argb_nonblank_pixel_count=921601"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_status=pass", "chrome_argb_status=fail"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_path=/tmp/chrome-argb.json", "chrome_argb_path="))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_width=1280", "chrome_argb_width=1279"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_height=720", "chrome_argb_height=719"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_format=argb-u32", "chrome_argb_format=rgba-u8"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_pixel_count=921600", "chrome_argb_pixel_count=0"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_pixel_count=921600", "chrome_argb_pixel_count=921599"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_nonblank_pixel_count=900000", "chrome_argb_nonblank_pixel_count=0"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_argb_nonblank_pixel_count=900000", "chrome_argb_nonblank_pixel_count=921601"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_status=pass", "simple_argb_status=fail"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_backend=vulkan", "simple_argb_backend=cpu"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_path=/tmp/simple-argb.json", "simple_argb_path="))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_width=1280", "simple_argb_width=1279"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_height=720", "simple_argb_height=719"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_format=argb-u32", "simple_argb_format=rgba-u8"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_pixel_count=921600", "simple_argb_pixel_count=0"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_pixel_count=921600", "simple_argb_pixel_count=921599"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_nonblank_pixel_count=900000", "simple_argb_nonblank_pixel_count=0"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("simple_argb_nonblank_pixel_count=900000", "simple_argb_nonblank_pixel_count=921601"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run + "\ngui_web_2d_vulkan_electron_argb_pixel_count=921600")).to_be(false)

step("Reject any missing or nonzero pairwise result and aggregate failure")
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_chrome_diff_path=/tmp/electron-chrome.ppm", "electron_chrome_diff_path="))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_chrome_pairwise_diff_status=pass", "electron_chrome_pairwise_diff_status=fail"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_chrome_mismatch_count=0", "electron_chrome_mismatch_count=1"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_simple_diff_path=/tmp/electron-simple.ppm", "electron_simple_diff_path="))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_simple_pairwise_diff_status=pass", "electron_simple_pairwise_diff_status=fail"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("electron_simple_mismatch_count=0", "electron_simple_mismatch_count=1"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_simple_diff_path=/tmp/chrome-simple.ppm", "chrome_simple_diff_path="))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_simple_pairwise_diff_status=pass", "chrome_simple_pairwise_diff_status=fail"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("chrome_simple_mismatch_count=0", "chrome_simple_mismatch_count=1"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("pixel_comparison_mode=pairwise-argb-diff", "pixel_comparison_mode=unknown"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run.replace("pixel_comparison_status=pass", "pixel_comparison_status=fail"))).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser + "\ngui_web_2d_vulkan_browser_backing_status=pass", run)).to_be(false)
expect(host_browser_vulkan_parity_evidence_passes(browser, run + "\ngui_web_2d_vulkan_pixel_comparison_status=pass")).to_be(false)
```

</details>

#### requires genuine correlated RenderDoc replay evidence

- requires genuine correlated RenderDoc replay evidence
   - Expected: capture_path equals `/tmp/frame.rdc`
   - Expected: capture_sha256 equals `eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee`
   - Expected: duplicate_path equals ``
   - Expected: duplicate_sha256 equals ``
   - Expected: missing_path equals ``
   - Expected: missing_sha256 equals ``
   - Expected: xml_path equals `/tmp/frame.xml`
   - Expected: xml_sha256 equals `dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd`
   - Expected: duplicate_xml_path equals ``
   - Expected: duplicate_xml_sha256 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires genuine correlated RenderDoc replay evidence")
val complete = complete_renderdoc_gate_evidence()
val (capture_path, capture_sha256) = host_renderdoc_capture_binding(complete)
expect(capture_path).to_equal("/tmp/frame.rdc")
expect(capture_sha256).to_equal("eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee")
val (duplicate_path, duplicate_sha256) = host_renderdoc_capture_binding(
    complete + "\nrdoc_simple_gate_capture_file=/tmp/stale.rdc")
expect(duplicate_path).to_equal("")
expect(duplicate_sha256).to_equal("")
val (missing_path, missing_sha256) = host_renderdoc_capture_binding(
    complete.replace("rdoc_simple_gate_capture_file=/tmp/frame.rdc\n", ""))
expect(missing_path).to_equal("")
expect(missing_sha256).to_equal("")
val (xml_path, xml_sha256) = host_renderdoc_replay_xml_binding(complete)
expect(xml_path).to_equal("/tmp/frame.xml")
expect(xml_sha256).to_equal("dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd")
val (duplicate_xml_path, duplicate_xml_sha256) = host_renderdoc_replay_xml_binding(
    complete + "\nrdoc_simple_gate_replay_xml_path=/tmp/stale.xml")
expect(duplicate_xml_path).to_equal("")
expect(duplicate_xml_sha256).to_equal("")
expect(host_renderdoc_evidence_passes(complete)).to_be(true)
expect(host_renderdoc_evidence_passes(complete.replace("\n", "\r\n"))).to_be(true)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_status=pass", "rdoc_simple_gate_status=fail"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_capture_file_magic=RDOC", "rdoc_simple_gate_capture_file_magic=bad"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_capture_sha256=eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee", "rdoc_simple_gate_capture_sha256=ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_capture_hash_status=pass", "rdoc_simple_gate_capture_hash_status=fail"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_renderdoc_capturing_before_end=1", "rdoc_simple_gate_renderdoc_capturing_before_end=0"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_renderdoc_device=41", "rdoc_simple_gate_renderdoc_device=0"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_record_valid=1", "rdoc_simple_gate_record_valid=0"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_semantic_hash=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "rdoc_simple_gate_semantic_hash=AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_record_hash=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", "rdoc_simple_gate_record_hash=0000000000000000000000000000000000000000000000000000000000000000"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete + "\nrdoc_simple_gate_pixel_hash=cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_capture_frame_id=frame-7", "rdoc_simple_gate_capture_frame_id=frame-8"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_capture_identity_status=pass", "rdoc_simple_gate_capture_identity_status=fail"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_status=pass", "rdoc_simple_gate_replay_status=fail"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_driver=vulkan", "rdoc_simple_gate_replay_driver=d3d12"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_capture_path=/tmp/frame.rdc", "rdoc_simple_gate_replay_capture_path=/tmp/other.rdc"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_xml_path=/tmp/frame.xml", "rdoc_simple_gate_replay_xml_path="))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_xml_hash=dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd", "rdoc_simple_gate_replay_xml_hash=bad"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_xml_file_status=pass", "rdoc_simple_gate_replay_xml_file_status=missing"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_xml_file_sha256=dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd", "rdoc_simple_gate_replay_xml_file_sha256=eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_xml_file_bytes=4096", "rdoc_simple_gate_replay_xml_file_bytes=4095"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_relevant_action_count=1", "rdoc_simple_gate_replay_relevant_action_count=0"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_pipeline_count=1", "rdoc_simple_gate_replay_pipeline_count=0"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_shader_count=1", "rdoc_simple_gate_replay_shader_count=0"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_replay_resource_count=1", "rdoc_simple_gate_replay_resource_count=0"))).to_be(false)
expect(host_renderdoc_evidence_passes(complete.replace("rdoc_simple_gate_owner_agreement_status=pass", "rdoc_simple_gate_owner_agreement_status=fail"))).to_be(false)
```

</details>

#### accepts only a complete screen-to-WM semantic frame receipt

- accepts only a complete screen-to-WM semantic frame receipt
- Classify one complete screen-to-WM semantic frame receipt
- Reject receipts with any missing or inconsistent hop


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only a complete screen-to-WM semantic frame receipt")
"""A screen event is evidence only when its WM target names the
retained compositor window and all later receipts agree."""
step("Classify one complete screen-to-WM semantic frame receipt")
val complete = complete_display_input_evidence()
expect(host_display_input_evidence_passes(complete)).to_be(true)

step("Reject receipts with any missing or inconsistent hop")
val legacy_partial = "linux_hosted_wm_live_window_event_origin=screen\nlinux_hosted_wm_live_window_semantic_target_id=host-proof\nlinux_hosted_wm_live_window_mutation_revision=1"
expect(host_display_input_evidence_passes(legacy_partial)).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("linux_hosted_wm_live_window_status=pass", "linux_hosted_wm_live_window_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("input_receipt_status=pass", "input_receipt_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("semantic_status=pass", "semantic_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("text_status=pass", "text_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("focus_status=pass", "focus_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("pointer_status=pass", "pointer_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("keyboard_status=pass", "keyboard_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("move_status=pass", "move_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("maximize_status=pass", "maximize_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("restore_status=pass", "restore_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("origin=screen", "origin=synthetic"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("event_id=7", "event_id=0"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("wm_target_id=41", "wm_target_id=-1"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace(
    "\nlinux_hosted_wm_live_window_wm_target_id=41\n",
    "\nlinux_hosted_wm_live_window_wm_target_id=42\n"
))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("semantic_target_id=host-proof", "semantic_target_id=other"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("callback_count=1", "callback_count=0"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("mutation_revision=1", "mutation_revision=0"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("replay_rejection_status=pass", "replay_rejection_status=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("frame_marker=pass", "frame_marker=fail"))).to_be(false)
expect(host_display_input_evidence_passes(complete.replace("frame_correlation_status=pass", "frame_correlation_status=fail"))).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/host_env_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering host environment evidence contract, render pipeline evidence contract, live framebuffer evidence classification, host evidence classification.
- host environment evidence contract
- render pipeline evidence contract
- live framebuffer evidence classification
- host evidence classification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `466885a17faf9fae6bfea6bb624d0ee749ccd1bdb746cd0fdaf17efc5609e168`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `466885a17faf9fae6bfea6bb624d0ee749ccd1bdb746cd0fdaf17efc5609e168`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `466885a17faf9fae6bfea6bb624d0ee749ccd1bdb746cd0fdaf17efc5609e168`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/host_env_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/host_env_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/host_env_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/host_env_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/host_env_contract_spec.spl:272:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts exactly the required capability rows and explicit cross-host blockers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/host_env_contract_spec.spl:289:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing, duplicate, and unknown capability rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/host_env_contract_spec.spl:298:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires actionable evidence for every capability status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
