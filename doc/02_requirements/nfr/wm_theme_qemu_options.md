# WM theme + QEMU NFR options

## NFR-1: Evidence strength

### Option A — visual and event-correlated proof

Require an artifact-backed desktop/window color capture plus correlated pointer
and keyboard receipt on every available target.

- Pros: proves the requested visible behavior rather than source intent.
- Cons: needs real QEMU/device readiness.
- Effort: M, 3–6 wrappers/specs/reports.

### Option B — visual proof only

Require a captured themed framebuffer but retain input separately.

- Pros: simpler capture pipeline.
- Cons: does not meet the requested WM event-handling validation.
- Effort: S, 2–4 artifacts.

## NFR-2: Web cache isolation

### Option A — material-aware CSS and revisions

Require Web CSS text and every retained revision/cache key to vary when an
override changes material without changing package source.

- Pros: correct visible Web parity and no stale frames.
- Cons: additional snapshot/CSS contract coverage.
- Effort: M, 4–7 files.

### Option B — identity-only invalidation

Require only cache IDs to change.

- Pros: smaller patch.
- Cons: permits unchanged client CSS pixels; insufficient for this bug.
- Effort: S, 2–3 files.

User selection is required before final requirements are written.
