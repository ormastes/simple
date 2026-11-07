# Windows Docker process provider local research

2026-11-07 source baseline: `862d9e361534c1a13f83a2f43da06e07847df5af`.

The existing `std.common.contracts.container.runtime_v1` module supplies lifecycle
identity, observations and operation envelopes; its provider trait covers probe.
The Linux OCI leaf owns Linux requests and cannot serve as a Windows adapter.
The release baseline includes a historical Windows HCS intent-builder leaf. Its
probe advertised capability from a CLI version and its lifecycle returned OK for
command admission without executing it. The new source preserves its pure intent
helpers but withdraws those false capability/success claims. A source caller scan
found only unit and cross-host specs; no production caller depends on that claim. The current controller dispatch is explicitly Linux-specific.

The historical Windows architecture proposes containerd/runhcs. The user's current
selection changes the first bridge to Docker with explicit process isolation.
The new Windows leaf retains common lifecycle envelopes and its own request type.
No common or Linux schema is modified by this slice.

Existing Windows requirements `REQ-WPC-001` through `REQ-WPC-005` remain relevant.
The prior Windows 11 Enterprise 23H2 build 22631.3527 / Server Core 2022 fixture is
historical context, not current evidence. No live Windows fixture is available.
Compiler execution is also NOT_RUN because the parent lane exhausted its bounded
compiler repair budget. Source review cannot establish native execution support.
