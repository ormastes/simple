# SimpleOS WM guest: web render budget expires before style loop (TCG wall-clock starvation)

- **Status:** OPEN (mitigated 2026-07-26: platform budget floor knob, guest floors at 300s)
- **Severity:** high (guest windows render with default styles; material provenance fails)
- **Found:** SimpleOS-WM fullscreen evidence lane, rerun20/21 receipt
  `[web-style-producer] budget-break at=0 of=11` — `compute_styles` broke on its
  wall-clock budget before processing a single node, so every style stayed
  `renderer_default_style()` (bg=0), the WM solid-material contract was never
  realized, and all three windows failed the content-provenance gate with
  `material=` empty (reruns 14-21).

## Root cause (corrected 2026-07-26, second pass)

**First attribution (WRONG, disproven by disassembly):** the
`src/os/kernel/net/tls_shim.spl` baremetal stub `rt_time_now_unix_micros`
advances a fake counter 1000us per read, which would burn budgets ~1000x fast.
Its advance was reduced to 1us/call — but rerun21 still broke at node 0.
Disassembly of the production desktop ELF showed the linker resolves
`rt_time_now_unix_micros` to the **strong C definition in
`examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c`**, which is a
properly calibrated TSC clock (CPUID leaf 0x15/0x16, PIT channel-2 fallback).
The tls_shim stub is dead code in this kernel. Lesson: verify WHICH definition
the linker picked (objdump the callee) before patching a clock.

**Actual cause:** guest time is real. Under QEMU TCG (~30x slower than native),
parse_html + extract_css + rule-bucket construction of the WM chrome stylesheet
genuinely consume more than 70% of the native-tuned render budget
(`max(area/16 ms, WEB_RENDER_BUDGET_MS=10s)`, style slice 70%) before the style
loop starts. The budget mechanism works exactly as designed; the tuning is
wrong for an emulated platform.

Misattribution warning (first pass): this presented for six lane runs as an
aggregate/array data-channel loss (`bg=0` through every [Style] hop) because the
material reducer scans `nodes` (attr visible) while `styles` legitimately held
defaults. Receipts gated on the corrupted value stayed silent and looked like
channel loss. The unconditional `budget-break` receipt cracked it.

## Fix shipped

- `simple_web_html_layout_renderer_foundation.spl`: platform budget floor —
  `simple_web_layout_set_render_budget_floor_ms(ms)` raises begin-time budgets
  to at least `ms`, and `_web_budget_rearm` never lowers the deadline below the
  begin-time floor deadline. 0 = no floor (default; hosted lanes unchanged).
  This is a calibration knob, not a bypass: budgets still expire past the floor.
- `gui_entry_desktop.spl` (x86_64): floors the budget at 300000ms at boot.
- Budget-break receipt now prints `now_us`/`deadline_us` for direct elapsed
  attribution.

## Remaining

- arm64 gui_entry_desktop should get the same floor when its WM lane is next
  exercised.
- tls_shim fake clock (1us/call after mitigation) is still a stub on kernels
  that DO link it (no rt_extras strong def); wiring it to the calibrated TSC
  (`arch/x86_64/timer.spl` exports `rt_time_now_ns`, needs `timer_init` at
  boot) remains the durable fix there.
- Board note (board-runnable rule): a slow real board can hit the same
  starvation; the floor knob is per-platform-entry, which is the right shape.
