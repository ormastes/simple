# Bootstrap ad-hoc quick check NFRs

- NFR-ADHOC-001: frontend compilation is capped at 120 seconds and 2 GiB.
- NFR-ADHOC-002: HIR/MIR compilation is capped at 300 seconds and 4 GiB.
- NFR-ADHOC-003: backend compilation is capped at 420 seconds and 6 GiB.
- NFR-ADHOC-004: subprocess output is bounded at 4 MiB and capsule execution
  at 60 seconds/1 GiB.
- NFR-ADHOC-005: parallel sessions use authority-hash-specific directories.
