<!-- codex-research -->
# NFR Requirements: Evidence Showcase

## Status

Selected by the user on 2026-07-30: `N1-B` through `N10-B`.

## Requirements

### NFR-EVS-001 — Honest freshness

Required evidence shall contain source revision, exact command, producer and
host/target identity, artifact checksum, status, and freshness policy.
Missing or stale evidence shall become `blocked` or `historical-pass`, never
`live-pass`.

### NFR-EVS-002 — Versioned compatibility

Evidence manifests shall use a versioned SDN schema. Readers shall reject
unsupported major versions, tolerate unknown minor fields, and fail closed when
required fields are missing or malformed.

### NFR-EVS-003 — Safe artifact handling

Docgen shall accept evidence only beneath canonical tracked or ephemeral roots,
reject traversal and absolute paths, validate kind/MIME/suffix compatibility,
escape Markdown and code fences, redact secret-like values, and keep HTML inert
unless rendered through the selected strict local sandbox.

### NFR-EVS-004 — Storage and retention

Text, SVG, and manifests shall remain normal Git files. Selected binary
still/motion formats shall use Git LFS according to repository policy.
Ephemeral/failure detail shall remain under
`build/test-artifacts/<spec-relative>/`; retained PASS review artifacts shall
live under `doc/06_spec/image/<spec-relative>/`.

### NFR-EVS-005 — Bounded media

Retained still artifacts shall be at most 2 MiB each. Review motion shall be at
most 10 seconds and 8 MiB, with at least two keyframes and an event transcript.
Larger raw captures may be retained as linked diagnostics but shall not be
embedded in generated manuals.

### NFR-EVS-006 — Incremental performance

When capture is not executed and artifacts are unchanged, focused docgen
manifest processing shall add no more than 1 second median overhead. Full
showcase generation shall perform one manifest scan and add no more than 10
seconds on the reference workspace. Hot request handlers shall not rescan the
repository or spawn evidence subprocesses.

### NFR-EVS-007 — Actionable text diagnostics

Text verification failures shall identify the first missing/out-of-order line,
the active normalization and masks, nearby actual lines, and bounded raw and
normalized transcript paths. Captured stdout/stderr shall respect the existing
4 MiB per-stream bounded-process policy.

### NFR-EVS-008 — Portable blocker contract

The manifest/status vocabulary shall be portable across Linux, macOS, Windows,
QEMU, and physical boards. Every unavailable row shall retain target,
prerequisites, exact resume command, artifacts, owner, and final reviewer.

### NFR-EVS-009 — Accessible manuals

Every still or motion item shall have descriptive alt/summary text; every motion
item shall have a transcript; color/highlighting shall have a textual status.
Generated manuals shall pass a human review in which the primary flow is
understandable without opening the source spec.

### NFR-EVS-010 — Complete traceability

Every critical showcase row shall link a requirement, modern executable SSpec,
generated manual, latest receipt/status, and artifact or blocker. Traceability
coverage for critical rows shall be 100%.

## Measurement notes

- Performance excludes QEMU, board, GPU, LLM, and media capture execution; it
  measures manifest discovery/validation/rendering only.
- Media limits apply to retained review artifacts, not raw diagnostic traces.
- A missing host prerequisite is a blocker state, not a skipped or passing test.
