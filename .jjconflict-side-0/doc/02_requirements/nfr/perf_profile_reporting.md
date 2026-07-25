# Performance Profile Reporting NFRs

**Date:** 2026-06-06

## Non-Functional Requirements

- **NFR-PPR-001:** Report generation must be deterministic in file layout: default reports go under `doc/09_report/*.md`.
- **NFR-PPR-002:** The profile-report contract test must run quickly and validate report structure without rerunning expensive benchmarks.
- **NFR-PPR-003:** The profile scripts must preserve existing environment knobs such as `RUNS`, `BUILD_DIR`, `REPORT_PATH`, `WIDTH`, `HEIGHT`, and `FRAMES`.
- **NFR-PPR-004:** Reports must be readable as standalone evidence docs, including limitations and reproducibility commands.
- **NFR-PPR-005:** Headless GUI hosts should be handled explicitly; GTK should use `xvfb-run` when available and otherwise record the failure/unavailability.
