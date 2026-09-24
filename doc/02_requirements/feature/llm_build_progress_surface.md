# LLM Build Progress Surface Requirements

- **REQ-BPS-001:** Publish one bounded machine-readable current snapshot under the centralized worktree storage root.
- **REQ-BPS-002:** Include schema/build identity, phase/subphase, state/verdict, all file counters, bounded current files, last completion, errors, link status, elapsed/heartbeat/rate/ETA, cancellation, and evidence paths.
- **REQ-BPS-003:** Atomically replace snapshots and reject sequence/time regression or a stale build writer.
- **REQ-BPS-004:** Preserve the append-only detailed event stream as separate evidence.
- **REQ-BPS-005:** Provide a concise reader API and `simple build-progress` command; neither may scrape logs.
- **REQ-BPS-006:** Integrate first at the compiler `log_build_progress` seam and bootstrap native-build path.

