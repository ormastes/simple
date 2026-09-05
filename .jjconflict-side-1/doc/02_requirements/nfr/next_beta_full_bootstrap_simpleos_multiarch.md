<!-- codex-research -->
# Next Beta, Full Bootstrap, and SimpleOS Multiarch NFRs

Date: 2026-07-30
Selection: user selected NFR Option A on 2026-07-30.

### NFR-001 — Reproducibility

Every release asset SHALL bind the exact tag commit, version, architecture,
bootstrap producer, source revision, and SHA-256 digest. Release jobs consume
verified artifacts; they do not rebuild with weaker settings.

### NFR-002 — Resource bounds

Each full-bootstrap and SimpleOS evidence job SHALL have an explicit timeout,
record elapsed wall time and peak RSS, and retain the measurement with the
artifact. OOM, timeout, missing measurement, or a same-runner regression above
10% after baseline establishment SHALL fail.

### NFR-003 — Reliability

All required matrix rows SHALL fail closed. Missing tools, binaries, images,
transcripts, checksums, compiler-in-filesystem evidence, or formal proof SHALL
be failures, not warnings or source-only fallbacks.

### NFR-004 — Performance-path discipline

Release and request hot paths SHALL not add repeated full-tree scans, repeated
source rereads, retry sleeps, or per-request subprocesses. Release-maintenance
scans may run once per job and SHALL be bounded.

### NFR-005 — Observability

Every matrix row SHALL emit a compact machine-readable receipt containing
platform, architecture, producer, status, reason, elapsed time, peak RSS,
artifact paths, and digests. Failure logs SHALL be uploaded even when the row
fails.

### NFR-006 — Security and integrity

The release SHALL reject unsafe archive paths, escaping links, missing notices,
unexpected payload roots, stale/seed binaries, and digest mismatches. No token
or credential SHALL be written to logs, artifacts, release notes, or remote
URLs.

### NFR-007 — Maintainability

Existing platform catalogs, scenario runners, payload checkers, and workflow
artifact mechanisms SHALL be extended in place. No parallel target registry,
release service, or new dependency is permitted without evidence that the
existing owner cannot express the requirement.
