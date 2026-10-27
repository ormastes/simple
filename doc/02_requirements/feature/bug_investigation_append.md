# Canonical bug investigation append

Scope selected by the 2026-10-27 bug audit: persist classifications in canonical investigation records without changing bug status. This is a local owner repair, not a replacement database or general codec redesign.

- REQ-BUG-NOTE-001: Append a single investigation note through both existing BugDatabase owners. Start at zero or one above the maximum existing line for that bug; preserve every existing main, auxiliary and unknown table row. Create the canonical log table when absent.
- REQ-BUG-NOTE-002: Identical content for the same bug succeeds without another row, including after save/reload. Other bugs may record the same content.
- REQ-BUG-NOTE-003: Reject unknown bugs, incompatible log schemas, malformed/duplicate target line numbers and input that the existing SDN codec cannot preserve, without mutation.

Explicit non-goals: modifying update_bug multiline semantics, status transitions, missing token accounting methods, general SDN parser hardening, concurrent writers, or touching the live bug database. Each audit writer must validate the input database before loading and remain the sole writer.

Acceptance evidence: real-owner integration specs for both sync and async profiles, a scratch save/reload with CRC validation, preservation comparisons and independent review. Runtime evidence is required before qualification; source review alone does not authorize canonical DB writes.
