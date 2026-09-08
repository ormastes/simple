# Slang paged-KV backend local research

Date: 2026-09-08. Review: Astra. Baseline: `c573d677ac8`.

S3 owns independent llama contexts, samplers, buffers, generation handles, and
immutable serialized-prefix leases. Its prefix objects remain whole-sequence
opaque llama state blobs. Splitting those bytes would not create token-addressable
KV pages, page tables, or paged attention.

The current Simple adapter can negotiate optional ABI groups atomically. That is
the correct migration seam: retain S3 as fallback and add a distinct physical-page
backend group. The serial owner remains authoritative for requests, reservations,
commits, cancellation, and reclamation.

The master plan must distinguish three levels: opaque S3 snapshots; an optional
llama shared-sequence precursor; and true Slang-owned pages consumed directly by
attention kernels. Only the third closes A4/S4.
