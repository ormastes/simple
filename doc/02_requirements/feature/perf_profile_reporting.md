# Performance Profile Reporting Requirements

**Date:** 2026-06-06
**Selection basis:** The user explicitly requested Markdown profile reports, README links, TUI startup scope checking, web research, and common tests under `test/`.

## Requirements

- **REQ-PPR-001:** The cross-language profile script must generate a Markdown report under `doc/09_report`.
- **REQ-PPR-002:** The GUI profile script must generate a Markdown report under `doc/09_report`.
- **REQ-PPR-003:** The generated reports must describe methodology, environment, reproducibility, limitations, and profile script path.
- **REQ-PPR-004:** README.md must link to both profile scripts and their generated reports.
- **REQ-PPR-005:** The GUI/language profile reports must state whether TUI startup speed is measured and link to the canonical startup-size audit.
- **REQ-PPR-006:** Common profile-report validation must live under `test/` and profile scripts must call it.
- **REQ-PPR-007:** Failed, unavailable, skipped, or startup-only lanes must not be presented as performance wins.
