# System Test Plan: Vulkan Async Compute Submission Ring

**Status:** selected B/N2; blocked only pending runtime implementation and
provider admission.

## Planned evidence

The future integration spec will run one host-aware matrix with explicit skip
on hosts lacking an admitted Vulkan device. It will cover the positive
three-submit ring, command-four slot recycling, pending poll, exact retirement,
resource-owner retention, stale-token rejection, unknown-completion quarantine,
bounded capacity/backpressure, deterministic receipt order, cooperative
cancellation, and teardown idempotence described in the design. A separate
finite pre-recorded-batch case proves why the existing API is not a recyclable
ring and must not satisfy the positive case.

The device-free portion can be added before hardware admission, but it must not
claim the three-submit behavior. The live portion must reject a false skip and
must record device identity, queue family, ring capacity,
attempted/accepted/rejected submits, poll outcomes, CPU waits and duration,
backpressure events, retired slots, maximum in-flight slots, cancellation,
device-idle recoveries, retained/released bytes, monotonic host timestamps,
optional available GPU timestamps, and checksum/readback proof.
For selected N2, a two-thread case must prove that one bounded fence wait does not hold
the global Vulkan registry mutex or prevent another slot poll/counter query.

## Failure policy

Any unresolved owner, early physical resource release, fabricated fence,
unbounded ring, stale-token/slot reuse, unknown-completion reuse, busy polling,
hidden helper call to device idle, or device-wide wait on the normal async path
is a failure. A missing Vulkan host is an explicit skip, not a pass. The
existing blocking C/Simple row and any finite pre-recorded batch remain
diagnostic baselines only. A bounded wait that serializes unrelated registry
operations is also a failure.
