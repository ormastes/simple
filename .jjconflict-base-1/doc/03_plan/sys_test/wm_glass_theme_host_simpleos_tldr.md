# WM Glass Theme System Test Plan — TLDR

- 2026-07-25: no production admission yet. The hosted 16x16 local-raster
  capture has no manifest/event binding, and x86/ARM checks were
  preflight-only. Keep the aggregate spec fail-fast pending exact-current host
  and QEMU evidence.

- Seven scenarios cover canonical parity, interaction, CSS, accessibility,
  fail-closed behavior, performance/provenance and ownership.
- Every REQ-001..010 and NFR-001..008 is traced.
- Evidence combines structured semantics with host/QEMU framebuffer captures.
- Missing helpers fail explicitly; no placeholder pass is allowed.
- Before runtime switching can be tested, focused protocol tests must pin the
  parent-owned exact `(revision, wire_text)` store, codec-owned public UTF-8
  bound checker (with no feature-local `rt_*` conversion), exact init/apply
  envelopes, migrated-parent admission before notification, explicit frame
  revision/hash, and replay-payload restart fence. This is planned only, not a
  runtime PASS.

```text
theme -> host/CSS/QEMU -> interaction -> evidence -> fail-closed verdict
```
