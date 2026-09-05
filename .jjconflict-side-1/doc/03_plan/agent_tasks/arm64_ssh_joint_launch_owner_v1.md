# ARM64 SSH Joint Launch Owner V1 Tasks

- Owner prerequisite: exact request-bound SSH lease consumption and terminal
  quarantine — implemented in this change.
- Loader prerequisite: pure exact validation of Armed identity, token,
  canonical path, ARM64 entry, and pristine consumer — implemented here.
- Loader prerequisite: opaque bounded joint reservation, exact rollback,
  terminal revoke, and scheduler adoption of the matching lease — implemented.
- Deferred integration: compose reservation with exact SSH bound consumption
  in the loader-owned coordinator after this prerequisite is reviewed.
- Wiring: connect only the authenticated SSH exec request owner after the
  reservation lands; do not expose a direct architecture spawn API.
- Scope: ARM64 only. x86, x86_64, ARM32, RISC-V32, and RISC-V64 remain untouched.
- Merge owner: SimpleOS loader/SSH hardening lane.
- Final reviewer: independent highest-capability static owner-safety review.
- Verification: intentionally not run in this user-directed no-verify wave.
