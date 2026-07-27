# WM/GUI/Web/2D Host Environment Hardening Requirements

Selected feature option: **B — One Real Linux End-to-End Slice**.

## Functional Requirements

- REQ-001: Provide a canonical `test_host_env()` result that reports x86 SIMD,
  ARM SIMD, RISC-V vector/SIMD, Vulkan, RenderDoc, display/input, and
  framebuffer-readback capability rows with stable status and concrete reasons.
- REQ-002: Reuse the current production host, WM, GUI/Web, Draw IR, Engine2D,
  SIMD, Vulkan, readback, and RenderDoc owners; do not add a parallel renderer,
  event driver, fixture-only bypass, raw runtime alias, or mock middle.
- REQ-003: On Linux, inject a real screen-originated event through the existing
  hosted input boundary and correlate it through WM hit-testing, semantic
  GUI/Web target dispatch, application state mutation, damage/composition,
  Engine2D submission, and the resulting framebuffer readback.
- REQ-004: The correlated receipt must preserve one event/frame identity and
  report focus, keyboard/text, pointer down/up, window move/maximize, target,
  application callback, render revision, backend, handle, completion, readback
  source, dimensions, stride, format, and checksum.
- REQ-005: Production frame evidence must use
  `SharedWmScene -> DrawIrComposition -> Engine2D`; compatibility renderers and
  CPU mirrors may be diagnostic only and cannot satisfy production acceptance.
- REQ-006: Deterministic fixtures must prove nonblank output and an absolute
  Draw IR or pixel oracle; comparable Simple/Chrome/Electron ARGB artifacts must
  have equal dimensions and zero pairwise mismatches.
- REQ-007: Available x86 SIMD paths must prove executed-path identity and exact
  scalar-oracle parity. ARM and RISC-V native rows remain active with explicit
  prerequisites, artifacts, owners, and resume commands until run on those hosts.
- REQ-008: Available Vulkan paths must prove validated module use, real queue
  submission, completion, positive native handle, and device-origin readback.
  Software/fallback/cache/CPU-mirror results must be labeled and rejected as
  Vulkan proof.
- REQ-009: RenderDoc evidence must use the existing shared helpers, retain the
  capture log and `.rdc` path, and validate `RDOC` magic. Missing native capture
  remains blocked rather than becoming screenshot evidence.
- REQ-010: Unit, component/integration, and modern SSpec system tests must cover
  capability classification, event correlation, render receipt validation,
  failure modes, and the real Linux vertical slice.
- REQ-011: Every reproduced rendering performance regression, missing route, or
  wrong fallback/provenance path must be fixed once at its shared owner boundary
  or recorded as a concrete tracked bug with a bounded reproducer.
- REQ-012: Generated SSpec manuals and relevant architecture, design, plan, and
  operator-guide artifacts must describe the same production route and blocked
  host rows.

## Acceptance

The Linux production slice is accepted only when its real input, semantic
dispatch, canonical rendering, and framebuffer receipt correlate in one run.
The umbrella goal remains incomplete while required ARM, RISC-V, Vulkan, or
RenderDoc native rows lack fresh evidence.
