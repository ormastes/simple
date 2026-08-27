# Local Research: Release Process Hardening

**Date:** 2026-08-26

**Status:** Complete companion index

The full repository audit is
[`doc/01_research/infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md`](../infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md).

Local evidence established that release version strings were independently
maintained, authoring guidance conflicted with typed VCS policy, GitHub did not
enforce the documented protected refs, tag creation preceded admission, release
CI tolerated fallback artifacts, and bootstrap qualification was serialized.
The selected implementation therefore uses isolated sessions, protected CAS
integration, canonical version projections (including Cargo manifest and lock),
reviewed bidirectional maintenance convergence, immutable candidate attempts,
promote-without-rebuild publication, and speculative-but-quarantined bootstrap
descendants.

Current verification evidence and remaining blockers are maintained in
[`doc/09_report/release_process_hardening_verification_2026-08-26.md`](../../09_report/release_process_hardening_verification_2026-08-26.md).
