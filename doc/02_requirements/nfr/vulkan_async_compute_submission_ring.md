# NFR: Vulkan async compute submission ring

**Status:** selected; implementation and hardware evidence pending
**Selection:** N2 tunable bounded ring, with B runtime ownership

- **NFR-VKASYNC-001 — capacity:** Support session capacities 3, 8, and 16 in
  the acceptance matrix. Metadata is allocated at construction and peak
  retained device bytes do not exceed live-slot declarations plus fixed session
  resources.
- **NFR-VKASYNC-002 — pressure:** A ring-full event performs one oldest-slot
  poll and at most one caller-configured bounded wait. No busy polling, implicit
  growth, or normal-path `wait_idle`; count every backpressure event and wait.
- **NFR-VKASYNC-003 — overlap:** The positive live-device run submits three
  commands before any host wait, retires one slot, and submits command four
  without device idle. Record maximum in-flight slots and CPU wait count/duration.
- **NFR-VKASYNC-004 — contention:** A second thread can poll another slot or
  query counters while one slot performs its bounded wait; the global registry
  mutex is not held during that wait.
- **NFR-VKASYNC-005 — retirement:** Report attempted/accepted/rejected
  submits, poll outcomes, retirements, cancellation, unknown completion,
  retained/released bytes, device-idle recoveries, and terminal owner counts.
  Normal-path device-idle recoveries must be zero.
- **NFR-VKASYNC-006 — reproducibility:** Use monotonic host timestamps and
  report p50/p95 offer, poll, wait, retirement, and total frame latency. GPU
  timestamp values are separate and only reported when availability is proven.

The C blocking and finite pre-recorded-batch rows remain diagnostic baselines;
they cannot satisfy NFR-VKASYNC-003.
