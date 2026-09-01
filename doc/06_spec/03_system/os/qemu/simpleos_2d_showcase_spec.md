# simpleos_2d_showcase_spec

> SimpleOS 2D showcase and shared contract composition across draw, input, and audio.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_2d_showcase_spec

## Parser contract targets
- Board checker matrix validates:
  - missing board,
  - unsupported board,
  - runner-not-yet-implemented,
  - board-not-connected when UNO Q is unattached.
- Host GPU checker validates pass row contract (Linux row pass + render backend matrix).
- Audio checker validates keyboard/pointer/controller receipts and playback/capture non-silent traces.
- Host GPU metrics contract validates render sample count + p95 + RSS evidence (no hardcoded synthetic values).
- RV64 checker validates font route, marker parsing, and keyboard/pointer correlation.
- Showcase source contract validates DrawIR/event entrypoints plus keyboard modifier state routing (`alt_held`, `ctrl_held`) and host-side animation hooks (`web_animation_dirty_due`, `animation_frame_due`).

## Lane status at handoff
- Lane 1 (Linux/QEMU Vulkan): parser/self-test complete, live pass blocked by compiler/runtime admission.
- Lane 2 (ARM64/QEMU event): parser/self-test complete, live pass blocked by compiler/runtime admission.
- Lane 3 (macOS HVF): parser/test harness complete, emulator-only in this host context.
- Lane 4 (UNO Q + showcase): parser/matrix complete; board pass intentionally blocked unless hardware is attached.

## What is done vs. still blocked
- ✅ Done:
  - 4-lane structure and artifacts exist.
  - Board fail-closed matrix reasons are explicit.
  - Linux QEMU rows are Vulkan-bound in parser evidence.
  - Host/event/audio/font marker contracts are checked from shared checker code.
- ⏸️ Still blocked:
  - Fresh native PASS on this host for Linux/QEMU/ARM64 rows because pure-Simple compiler admission/runtime still needs to be installed end-to-end.
  - macOS/uno-q native row execution cannot be completed on this host; macOS remains emulator-only here, and UNO Q is not attached.
    - On this host, macOS row must stay `unsupported` or `blocked` and must only be promoted after a prepared-macOS host run with native contracts.
  - No live animation frame counter proof yet in this environment (existing animation fixtures are contract-level only in this lane).

SimpleOS 2D showcase and shared contract composition across draw, input, and audio.

## Scenarios

### SimpleOS 2D showcase contracts

#### validates no-hardware proof contracts for board, host GPU, audio, and RV64 font/input

- validates no-hardware proof contracts for board, host GPU, audio, and RV64 font/input
   - Log capture: after_step
- Run board fail-closed self-test matrix
   - Log capture: after_step
   - Evidence: log output verified by 3 expected checks
   - Expected: code equals `0`
   - Expected: err equals ``
   - Expected: out does not contain `simpleos_native_board_gpu_unattached_status=pass`
- Reject UNO Q promotion when no board identity is admitted
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: uno_code equals `1`
   - Expected: uno_err equals ``
- Run host GPU wrapper parser contract
   - Log capture: after_step
   - Evidence: log output verified by 3 expected checks
   - Expected: host_code equals `0`
   - Expected: host_err equals ``
   - Expected: host_out does not contain `simpleos_qemu_host_gpu_2d_macos_status=pass`
- Run shared audio contract self-test
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: audio_code equals `0`
   - Expected: audio_err equals ``
- Run shared RV64 font and input contract self-test
   - Log capture: after_step
   - Evidence: log output verified by 4 expected checks
   - Expected: font_code equals `0`
   - Expected: font_err equals ``
   - Expected: perf_code equals `0`
   - Expected: perf_err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates no-hardware proof contracts for board, host GPU, audio, and RV64 font/input")
step("Run board fail-closed self-test matrix")
val (out, err, code) = run_board_self_test()
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("simpleos_native_board_gpu_self_test=pass")
expect(out).to_contain("simpleos_native_board_gpu_reason=missing-board")
expect(out).to_contain("simpleos_native_board_gpu_reason=unsupported-board")
expect(out).to_contain("simpleos_native_board_gpu_reason=runner-not-yet-implemented")
expect(out).to_contain("simpleos_native_board_gpu_reason=board-not-connected")
expect(out).to_contain("simpleos_native_board_gpu_unattached_status=blocked")
expect(out).to_contain("simpleos_native_board_gpu_unattached_reason=board-not-connected")
expect(out.contains("simpleos_native_board_gpu_unattached_status=pass")).to_equal(false)
step("Reject UNO Q promotion when no board identity is admitted")
val (uno_out, uno_err, uno_code) = run_uno_q_fail_closed()
expect(uno_code).to_equal(1)
expect(uno_err).to_equal("")
expect(uno_out).to_contain("simpleos_native_board_gpu_status=blocked")
expect(uno_out).to_contain("simpleos_native_board_gpu_board=uno-q")
expect(uno_out).to_contain("simpleos_native_board_gpu_strict=1")
expect(uno_out).to_contain("simpleos_native_board_gpu_reason=board-not-connected")
step("Run host GPU wrapper parser contract")
val (host_out, host_err, host_code) = run_host_gpu_self_test()
expect(host_code).to_equal(0)
expect(host_err).to_equal("")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_self_test=pass")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_status=pass")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_rows=3")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_x86_64_render_backend=vulkan")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_aarch64_render_backend=vulkan")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_riscv64_render_backend=vulkan")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_x86_64_render_readback_p95_us=")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_aarch64_render_readback_p95_us=")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_riscv64_render_readback_p95_us=")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_x86_64_processing_backend=cuda-preferred-vulkan-fallback")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_aarch64_processing_backend=cuda-preferred-vulkan-fallback")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_riscv64_processing_backend=cuda-preferred-vulkan-fallback")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_host=linux")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_reason=all-linux-host-gpu-rows-pass")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_x86_64_status=pass")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_aarch64_status=pass")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_riscv64_status=pass")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_linux_aarch64_render_backend=vulkan")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_macos_status=unsupported")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_macos_reason=requires-macos-host")
expect(host_out).to_contain("simpleos_qemu_host_gpu_2d_macos_execution=emulator-only")
expect(host_out.contains("simpleos_qemu_host_gpu_2d_macos_status=pass")).to_equal(false)
step("Run shared audio contract self-test")
val (audio_out, audio_err, audio_code) = run_io_audio_self_test()
expect(audio_code).to_equal(0)
expect(audio_err).to_equal("")
expect(audio_out).to_contain("simpleos_io_audio_qemu_self_test=pass")
expect(audio_out).to_contain("simpleos_io_audio_qemu_status=pass")
step("Run shared RV64 font and input contract self-test")
val (font_out, font_err, font_code) = run_rv64_font_input_self_test()
expect(font_code).to_equal(0)
expect(font_err).to_equal("")
expect(font_out).to_contain("rv64_display_smoke_qmp_self_test=pass")
expect(font_out).to_contain("rv64_wm_keyboard_correlated=1")
expect(font_out).to_contain("rv64_wm_pointer_correlated=1")
expect(font_out).to_contain("rv64_wm_input_frame_changed=1")
expect(font_out).to_contain("rv64_wm_font_input_mode=1")
val (perf_out, perf_err, perf_code) = run_host_gpu_metrics_self_test()
expect(perf_code).to_equal(0)
expect(perf_err).to_equal("")
expect(perf_out).to_contain("simpleos_qemu_host_gpu_2d_linux_x86_64_render_sample_count=20")
expect(perf_out).to_contain("simpleos_qemu_host_gpu_2d_linux_aarch64_render_sample_count=20")
expect(perf_out).to_contain("simpleos_qemu_host_gpu_2d_linux_riscv64_render_sample_count=20")
expect(perf_out).to_contain("simpleos_qemu_host_gpu_2d_linux_x86_64_processing_cpu_us=")
expect(perf_out).to_contain("simpleos_qemu_host_gpu_2d_linux_aarch64_processing_device_us=")
```

</details>

#### keeps draw/input/audio semantics on shared source contracts

- keeps draw/input/audio semantics on shared source contracts
   - Protocol capture: after_step
- Assert shared shortcut and shortcut-target routing contains modifier contracts
   - Protocol capture: after_step
- Verify host and renderer contracts stay shared
   - Protocol capture: after_step
- Verify shared WM host core has mouse, keyboard, and animation entrypoints
   - Protocol capture: after_step
- Keep all draw work on DrawIR-bound contracts
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps draw/input/audio semantics on shared source contracts")
step("Assert shared shortcut and shortcut-target routing contains modifier contracts")
val shortcut_source = file_read_text("src/os/gui/shortcut.spl")
val input_event_source = file_read_text("src/os/gui/input_event.spl")
expect(shortcut_source).to_contain("alt_held")
expect(shortcut_source).to_contain("ctrl_held")
expect(shortcut_source).to_contain("SC_LEFT_ALT")
expect(shortcut_source).to_contain("SC_LEFT_CTRL")
expect(input_event_source).to_contain("enum WmAction")
expect(input_event_source).to_contain("CycleFocus")
expect(input_event_source).to_contain("Close")

step("Verify host and renderer contracts stay shared")
val host_gpu_source = file_read_text("scripts/check/check-simpleos-qemu-host-gpu-2d.shs")
val audio_source = file_read_text("scripts/check/check-simpleos-io-audio-qemu.shs")
val rv64_source = file_read_text("scripts/check/check-rv64-display-smoke-qmp-evidence.shs")
expect(host_gpu_source).to_contain("HOST_GPU_FIXTURE_WIDTH")
expect(host_gpu_source).to_contain("host_gpu_ivshmem_submit_draw_ir")
expect(host_gpu_source).to_contain("simpleos_qemu_host_gpu_2d_render_readback_p95_us")
expect(audio_source).to_contain("SIMPLEOS_INPUT_EVENT")
expect(audio_source).to_contain("kind=pointer")
expect(rv64_source).to_contain("[wm-pointer-irq]")
expect(rv64_source).to_contain("[wm-input-irq]")
step("Verify shared WM host core has mouse, keyboard, and animation entrypoints")
val compositor_source = host_compositor_core_source()
expect(compositor_source).to_contain("me dispatch_gui_key_event")
expect(compositor_source).to_contain("me dispatch_gui_pointer_event")
expect(compositor_source).to_contain("me handle_mouse_move")
expect(compositor_source).to_contain("me handle_mouse_button")
expect(compositor_source).to_contain("me handle_mouse_wheel")
expect(compositor_source).to_contain("web_animation_dirty_due")
expect(compositor_source).to_contain("animation_frame_due")

step("Keep all draw work on DrawIR-bound contracts")
val showcase = file_read_text("test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl")
expect(showcase).to_contain("host_gpu_ivshmem_submit_draw_ir")
expect(showcase).to_contain("engine2d_draw_ir_adv_composition_present_with_images")
expect(showcase).to_contain("simpleos_qemu_host_gpu_2d_linux_x86_64_render_readback_p95_us")
expect(showcase).to_contain("simpleos_qemu_host_gpu_2d_rows=3")
```

</details>

<details>
<summary>Advanced: keeps macOS emulation-only and UNO Q board expectations explicit</summary>

#### keeps macOS emulation-only and UNO Q board expectations explicit

- keeps macOS emulation-only and UNO Q board expectations explicit
- Do not claim a native PASS from this environment
   - Expected: board_blocked_code equals `0`
   - Expected: board_blocked_err equals ``
   - Expected: board_blocked does not contain `simpleos_native_board_gpu_status=pass`
- Keep the UNO Q dispatcher fail-closed until live board-owned evidence exists
- Keep non-macOS hosts from claiming macOS-native evidence
- Keep the final four-lane gate blocked until physical receipts exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps macOS emulation-only and UNO Q board expectations explicit")
step("Do not claim a native PASS from this environment")
val (board_blocked, board_blocked_err, board_blocked_code) = run_board_self_test()
expect(board_blocked_code).to_equal(0)
expect(board_blocked_err).to_equal("")
expect(board_blocked).to_contain("simpleos_native_board_gpu_reason=board-not-connected")
expect(board_blocked).to_contain("simpleos_native_board_gpu_status=blocked")
expect(board_blocked.contains("simpleos_native_board_gpu_status=pass")).to_equal(false)

step("Keep the UNO Q dispatcher fail-closed until live board-owned evidence exists")
val board_runner = file_read_text("scripts/check/check-simpleos-native-board-gpu-2d.shs")
val todo_db = file_read_text("doc/08_tracking/todo/todo_db.sdn")
expect(board_runner).to_contain('emit_row "blocked" "board-not-connected"')
expect(board_runner).to_contain('emit_row "blocked" "live-qrb2210-simpleos-runner-required-offline-preflight-only"')
expect(todo_db).to_contain("658, TODO, simpleos")
expect(todo_db).to_contain("Run UNO Q native board GPU pass with board-attached runner and native DrawIR parity")
expect(todo_db).to_contain("board-not-connected` without hardware and `live-qrb2210-simpleos-runner-required-offline-preflight-only")
expect(todo_db).to_contain("Close TODO658 only after board-attached execution proves identity")
expect(todo_db).to_contain(", open, true")

step("Keep non-macOS hosts from claiming macOS-native evidence")
val host_gpu_runner = file_read_text("scripts/check/check-simpleos-qemu-host-gpu-2d.shs")
expect(host_gpu_runner).to_contain('emit_row "$report_host" "$report_isa" unsupported "requires-$report_host-host" none')
expect(todo_db).to_contain("660, TODO, simpleos")
expect(todo_db).to_contain("Run the emulator-ready macOS Simple2D contract on a prepared macOS host; keep this Linux host fail-closed")
expect(todo_db).to_contain("Linux provides static/unit evidence only and claims no native macOS PASS")
expect(todo_db).to_contain("shared DrawIR-to-Engine2D-to-Vulkan")
expect(todo_db).to_contain("Metal or a private renderer is not admissible proof")
expect(todo_db).to_contain("661, TODO, simpleos")
expect(todo_db).to_contain("Complete Simple2D showcase 4-lane proof with animation, event handling (mouse/keyboard/ctrl/alt), font rendering, and sound once board host is attached")
expect(todo_db).to_contain("macOS-emulator lanes are parser/tests-only in this host")

step("Keep the final four-lane gate blocked until physical receipts exist")
expect(todo_db).to_contain("664, TODO, simpleos")
expect(todo_db).to_contain("Close the Simple2D 4-lane session only after one attached UNO Q board run provides native DrawIR+ProcessingIR exactness")
expect(todo_db).to_contain("every canonical capability remains PORT_UNAVAILABLE and no board execution exists")
expect(todo_db).to_contain("captured native artifacts (identity, receipt hash, animation frames, event traces, font and audio parity)")
```

</details>


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

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-007`
- `REQ-015`
- `REQ-016`
- `REQ-017`
- `REQ-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6d5b93d99284cc19d41ab1bb9d0a16dc565a65552d825c8d64beb26e3a26a2bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d5b93d99284cc19d41ab1bb9d0a16dc565a65552d825c8d64beb26e3a26a2bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d5b93d99284cc19d41ab1bb9d0a16dc565a65552d825c8d64beb26e3a26a2bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/qemu/simpleos_2d_showcase_spec.spl
mirror: doc/06_spec/03_system/os/qemu/simpleos_2d_showcase_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/os/qemu/simpleos_2d_showcase_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/simpleos_2d_showcase_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/simpleos_2d_showcase_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/simpleos_2d_showcase_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 8 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/qemu/simpleos_2d_showcase_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates no-hardware proof contracts for board, host GPU, audio, and RV64 font/input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/simpleos_2d_showcase_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps draw/input/audio semantics on shared source contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/simpleos_2d_showcase_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps macOS emulation-only and UNO Q board expectations explicit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
