# Block backend capsule owner v1 test plan

- Bind a memory backend to one authenticated controller identity and prove
  relative reads/writes map only inside its exact LBA region.
- Attempt acquisition with a different valid device identity and require
  rejection before dispatch.
- Copy an I/O lease, release one copy, and prove the other cannot dispatch or
  consume the pin again.
- Hold an operation reservation across teardown and require `Busy`; release it,
  flush, and then retire the capsule generation.
- Inject backend flush failure and provider-unpin uncertainty in system fixtures
  when fault-injection ports become available; require bounded quarantine and
  exact retry rather than implicit release.

The unit spec is intentionally present but unexecuted in this no-verification
work session.
