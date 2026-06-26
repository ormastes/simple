# Graphical Backend Equality — NFR Requirements

Date: 2026-06-03

Selected scope: NFR Option 2, portable GPU/Web diagnostics.

## Requirements

- NFR-001: Equality reports must fail closed when capture metadata is missing,
  dimensions are invalid, scale factor is invalid, or pixel buffers do not match
  physical dimensions.
- NFR-002: Exact CPU/software policy must require exact pixel equality.
- NFR-003: GPU/Web/native policy may record thresholded diagnostics, but
  tolerance acceptance must remain explicit in the report.
- NFR-004: Reports must preserve artifact paths for expected, actual, diff, and
  metadata outputs when those paths are available.
- NFR-005: Backend unavailability must be reported separately from drawing
  equality so missing hardware does not look like a graphical pass.
- NFR-006: Work sessions must run `jj git fetch` before starting, before agent
  integration, and before release handoff; push remains user-approved.
