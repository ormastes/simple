# Metal MSL Processing Backend Requirements

- REQ-001 (AC-1/AC-4): Generate deterministic MSL from validated shared
  `ProcessingIr` through `ProcessingBackendArtifact`, without a Metal renderer
  public API.
- REQ-002 (AC-4): Preserve the fixed Metal ABI: output buffer 0, unused buffer
  1, parameters buffer 2, and `thread_position_in_grid` bounds checking.
- REQ-003 (AC-6): Reject invalid or unsupported IR before source compilation;
  failed generation, compilation, device selection, submission, or readback
  must not claim GPU completion or provenance.
- REQ-004 (AC-5/AC-7): Host-independent tests cover deterministic generation,
  binding metadata, invalidation, and fail-closed behavior.  macOS tests compile
  and run the generated source and compare device readback exactly to the CPU
  oracle.
- REQ-005 (AC-5/AC-8): When macOS is unavailable, retain an explicit blocked
  native row with prerequisites, exact resume command, artifacts, owner, and
  final reviewer.
- REQ-006 (AC-11): Metal-to-Metal drawing access preserves output/parameter
  bindings, two-dimensional coordinates, row-major pixel indexing, and exact
  CPU-oracle pixels; unsupported or out-of-bounds translations fail closed.
