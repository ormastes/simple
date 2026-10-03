# Grouped memory reservation and enforcement

The grouped manager previously passed one positive byte limit through admission,
native enforcement, and charge validation. Disabling only native enforcement
would reject legitimate observations above the reservation and could undercharge
the next concurrent group.

The admitted policy is `enforce` (default) or `monitor`. The existing
`memory_limit_bytes` field remains a positive admission reservation in both modes.
Only the argument to the SOSIX native process owner becomes zero in monitor mode.
Process-tree ownership, cancellation, finite control/cleanup operations and
post-collect publication remain in force.

Enforced manifests, runs and broker requests retain their exact V1 encoding.
Monitor uses V2 with an explicit policy scalar, including each embedded manifest.
Unknown policy, zero reservation and run/manifest policy mismatch are rejected.
The manifest digest consequently binds policy into results and charge traces.

An active monitor task charges the larger of its reservation and observed current
memory. Where current Job charge is unavailable, its lifetime Job commit peak is
used conservatively. The reservation is retained when observations are smaller.
Admission still checks both physical memory and measured commit headroom plus the
host reserve. This is sampled admission, not a guarantee that uncapped workloads
cannot subsequently exhaust memory.

Both native brokers publish `broker-memory.sdn` before terminal authority. It
separates requested policy, positive reservation, actual native enforcement,
observed peak and provider metric. The collector binds that receipt to the
installed host launcher (not the compilation target), exact broker identity and
terminal peak. Monitor cannot settle without it. Legacy enforced attempts may
retain their original reap bytes without a new memory receipt.

Tests authored: old/V2 wire round trips and identities; both host path forms;
positive reservation; Linux current and Windows conservative peak overshoot;
physical/commit equality and one-byte refusal; terminal peak preservation;
canonical provider metrics; collector refusal for missing/opposite-provider,
stale identity/peak and wrong policy receipts before any retained reap.

Verification: source review and scoped shell audit only. SPL/native tests and
cross-host runtime qualification are UNRUN pending an admitted producer/slot.
Integration requires the generic memory-policy owner's canonical helper and
native zero-enforcement implementation. This change alone is not a deployment
or release qualification.
