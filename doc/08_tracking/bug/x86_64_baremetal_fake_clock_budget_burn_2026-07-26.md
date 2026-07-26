# x86_64 baremetal clock is a 1ms-per-call fake — wall-clock budgets burn ~1000x fast

- **Status:** OPEN (mitigated 2026-07-26: fake advance reduced 1000us -> 1us per call)
- **Severity:** high (any time-budgeted code path silently degrades to zero work in-guest)
- **Found:** SimpleOS-WM fullscreen evidence lane, rerun20 receipt
  `[web-style-producer] budget-break at=0 of=11` — `compute_styles` broke on its
  wall-clock budget before processing a single node, so every style stayed
  `renderer_default_style()` (bg=0), the WM solid-material contract was never
  realized, and all three windows failed the content-provenance gate with
  `material=` empty (reruns 14-20).

## Root cause

`src/os/kernel/net/tls_shim.spl` `rt_time_now_unix_micros()` (`@cfg(not(riscv64))`
baremetal stub) advanced a fake counter by **1000us on every read**. Reading the
clock therefore cost 1ms of fake time. The web render budget samples the clock in
its inner loops (`_web_budget_expired()` in
`simple_web_html_layout_renderer_foundation.spl`), so parse/CSS/style consumed the
entire multi-second budget in a few thousand clock reads — before the style loop
started.

Misattribution warning: this presented for six lane runs as an aggregate/array
data-channel loss (`bg=0` through every [Style] hop) because the reducer scans
`nodes` (attr visible) while `styles` legitimately held defaults. Receipts gated
on the corrupted value stayed silent and looked like channel loss. The
unconditional `budget-break` receipt was what cracked it.

## Real fix (pending)

The kernel already has a calibrated monotonic clock:
`src/os/kernel/arch/x86_64/timer.spl` — `_read_tsc()` (RDTSC), `_calibrate_tsc()`
(HPET -> PMTMR -> PIT ch2 fallback chain), and a C-ABI export `rt_time_now_ns()`.
But the desktop kernel never calls `timer_init`, so `tsc_frequency == 0` and
`rt_time_now_ns()` returns 0.

Plan:
1. Call the x86_64 timer init/calibration during desktop kernel boot (before the
   WM starts; PIT fallback needs only port I/O).
2. Wire `rt_time_now_unix_micros()` to `rt_time_now_ns()/1000` (+ epoch offset),
   keeping the fake counter only as an uncalibrated fallback.
3. Same audit for arm64/x86_32 baremetal (their `timer.spl` files also export
   `rt_time_now_ns`).
4. Board note (board-runnable rule): TSC + PIT calibration works on real x86
   hardware, not just QEMU; keep the calibration source selectable
   (HPET/PMTMR/PIT) as the tuning knob.

## Mitigation shipped

Fake advance reduced to 1us/call: budgets become effectively inert on the fake
clock (a 30s budget needs 30M reads), monotonicity for receipts/entropy mixing is
preserved. `thread_shim.spl` sleep loops spin 1000x more iterations (still
sub-second real time under QEMU).
