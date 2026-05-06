# Chrome Modern Web Platform Compatibility NFRs

Date: 2026-05-06

NFR-001: Determinism

Migrated WPT and Test262 subset tests shall be deterministic in local runs. Pixel tests shall pin viewport, fixture source, and comparison method.

NFR-002: Traceability

Each migrated compatibility case shall record its local SSpec location and, when derived from WPT or Test262, the source-suite reference.

NFR-003: Bounded Scope

The compatibility workflow shall use curated subsets before claiming broad compatibility. Full Chrome compatibility shall not be claimed from proxy checks or small smoke suites.

NFR-004: Automation

Verification shall be runnable from repository commands and shall not depend on manual visual inspection as the only success signal.
