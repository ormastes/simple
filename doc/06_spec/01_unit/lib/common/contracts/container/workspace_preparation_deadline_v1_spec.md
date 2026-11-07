# Workspace preparation deadline

Source: `test/01_unit/lib/common/contracts/container/workspace_preparation_deadline_v1_spec.spl`.
Three authored scenarios, **NOT_RUN**. Manually reviewed mirror, not docgen.

1. Correlate the exact distinct stage digest and operation; reject a mapping or
   keeper/workload operation substituted for the preparation operation.
2. Require current time strictly before expiry. Equality, expired time and
   unavailable clock observations refuse admission.
3. Reject malformed digest/operation and nonpositive expiry before constructing
   the data carrier. Construction does not verify signatures or grant authority.

The actual native storage consumer must additionally derive a monotonic deadline
from real clock samples, check it while hashing, and recheck real time immediately
before a mode effect. These source contract tests do not establish native clock,
filesystem, signature, staged execution or cleanup qualification.
