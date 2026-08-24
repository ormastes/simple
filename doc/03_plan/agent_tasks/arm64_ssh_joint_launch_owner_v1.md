# ARM64 SSH Joint Launch Owner V1 Tasks

- Owner prerequisite: exact request-bound SSH lease consumption and terminal
  quarantine — implemented in this change.
- Loader prerequisite: pure exact validation of Armed identity, token,
  canonical path, ARM64 entry, and pristine consumer — implemented here.
- Deferred blocker: opaque bounded loader joint reservation and scheduler
  adoption of that reservation; must preserve the failure matrix in the design.
- Wiring: connect only the authenticated SSH exec request owner after the
  reservation lands; do not expose a direct architecture spawn API.
- Scope: ARM64 only. x86, x86_64, ARM32, RISC-V32, and RISC-V64 remain untouched.
- Merge owner: SimpleOS loader/SSH hardening lane.
- Final reviewer: independent highest-capability static owner-safety review.
- Verification: intentionally not run in this user-directed no-verify wave.
