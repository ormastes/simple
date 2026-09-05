<!-- codex-design -->
# Project Statistics and Quality Reporting NFRs

- NFR-STAT-001: Default inventory shall not invoke duplicate or coupling scans; full scans require an explicit quality flag.
- NFR-STAT-002: Every report records generator identity, scope, exclusions and evidence freshness.
- NFR-STAT-003: Default inventory target is under five seconds on a warm repository; quick mode target is under one second.
- NFR-STAT-004: JSON keys and project/test row ordering are deterministic.
- NFR-STAT-005: Markdown tables are at most five columns and the TLDR/deck present one conclusion per section for reliable PPT conversion.
- NFR-STAT-006: The deck uses the repository SimpleOS default theme, with no host GUI or network requirement to generate it.
- NFR-STAT-007: New pure-Simple reporting logic targets 80% branch coverage and has no placeholder assertions or silent fallbacks.
