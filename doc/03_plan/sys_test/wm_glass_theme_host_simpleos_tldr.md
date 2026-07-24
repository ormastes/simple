# WM Glass Theme System Test Plan — TLDR

- Seven scenarios cover canonical parity, interaction, CSS, accessibility,
  fail-closed behavior, performance/provenance and ownership.
- Every REQ-001..010 and NFR-001..008 is traced.
- Evidence combines structured semantics with host/QEMU framebuffer captures.
- Missing helpers fail explicitly; no placeholder pass is allowed.

```text
theme -> host/CSS/QEMU -> interaction -> evidence -> fail-closed verdict
```
