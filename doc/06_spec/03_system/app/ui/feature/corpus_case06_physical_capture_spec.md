# Corpus case 06 physical capture boundary

Manual companion to
`test/03_system/app/ui/feature/corpus_case06_physical_capture_spec.spl`.
Generated SPipe output is pending a trustworthy Simple runner.

## Scenarios

1. The authored case 06 HTML and independent HTML reference retain their
   pinned SHA-256 digests.
2. After Web admission, a caller-constructed Skia frame without a completed
   native readback fails before becoming a physical capture artifact.

Requirement links: REQ-2D-006, NFR-2D-002. This negative control does not
substitute for the separate Linux Vulkan dual-backend run.
