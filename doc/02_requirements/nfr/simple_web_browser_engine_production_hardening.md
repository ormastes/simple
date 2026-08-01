# Simple Web Browser Engine Production Hardening — NFR Requirements

Selection: NFR Option B — Production interactive baseline

All evidence binds production binary/revision/host/fixture/sample data; seed,
stale, raw-source, marker, or missing-capture evidence is not equivalent.

- NFR-WEB-BROWSER-001: Warm startup p95 <= 1,000 ms; cold p95 <= 2,000 ms.
- NFR-WEB-BROWSER-002: Warm local first contentful render p95 <= 250 ms; warm
  same-origin navigation p95 <= 500 ms.
- NFR-WEB-BROWSER-003: Reference animation delivers >=55 FPS with p95 frame
  <=16.7 ms and time-evolving production pixels.
- NFR-WEB-BROWSER-004: Input-to-paint p95 <=50 ms for pointer, keyboard, focus,
  text, scroll, and navigation controls.
- NFR-WEB-BROWSER-005: Browser plus one renderer RSS <=384 MiB after 60 minutes.
- NFR-WEB-BROWSER-006: After 10,000 cycles, live heap and retained browser
  resources return within 10% of post-warmup baseline after bounded quiescence.
- NFR-WEB-BROWSER-007: GC pause p95 <=8 ms and p99 <=16.7 ms without unbounded
  frame backlog or stale callback execution.
- NFR-WEB-BROWSER-008: Navigation/close/cancel leaves no unreachable cycles,
  post-cancel commits, stale callbacks, or unreleased renderer/Engine2D handles.
- NFR-WEB-BROWSER-009: Stop/cancel is visible within 100 ms and no canceled
  result commits afterward.
- NFR-WEB-BROWSER-010: Renderer crash/limit/sandbox kill does not terminate
  chrome, corrupt profile state, or terminate another site renderer.
- NFR-WEB-BROWSER-011: Every security-negative case passes on each claimed
  platform; the security gate requires 100%.
- NFR-WEB-BROWSER-012: Every pinned claimed WPT/Test262 test passes;
  unsupported rows remain visible outside the claim.
- NFR-WEB-BROWSER-013: Changed parser/URL/script/IPC/resource boundaries receive
  >=8 CPU-hours fuzzing or equivalent retained corpus evidence with zero
  reproducible crash, hang, unbounded allocation, use-after-free, or bypass.
- NFR-WEB-BROWSER-014: 10,000 navigation/interaction cycles complete without
  corruption and with process RSS growth <=10% after quiescence.
- NFR-WEB-BROWSER-015: Startup/render/frame/input/allocation/heap/RSS regression
  above 5% is fixed or remains a release blocker with reproducer.
- NFR-WEB-BROWSER-016: Hot paths do not scan the repository/tree, spawn
  subprocesses, recreate Engine2D/device/font state per frame, or unconditionally
  read back full frames outside evidence mode.
- NFR-WEB-BROWSER-017: Each final gate runs once and verification stops after
  three fix cycles, reporting remaining failures.
