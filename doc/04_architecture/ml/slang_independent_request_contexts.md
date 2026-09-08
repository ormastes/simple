# Slang independent request-context architecture

Date: 2026-09-08. Status: accepted S3 implementation contract.

One model owner retains weights and a bounded request table. Every live table
record owns all request-mutable state: llama context, sampler, prompt and output
buffers, token storage, evaluation cursor, lifecycle state, and at most one
prefix lease. A `(model_generation, slot_generation, slot)` opaque handle is
the only cross-SFFI identity. Native pointers remain private.

Simple is the serial scheduling owner. It may interleave request operations but
never runs two native operations simultaneously in S3. Children produce only
request results; the engine validates the handle and commits terminal state.
This follows the repository's parent-authoritative ownership model without
claiming parallel transport.

The prefix store remains model-owned and immutable after publication. Match
acquisition increments a pin count before restore. The request owns that lease
until one terminal helper releases it exactly once. Eviction and limit changes
operate only on unpinned entries. If no admissible victim exists, caching is
skipped rather than violating the bound or failing inference.

Legacy calls route through a compatibility request that consumes a real table
slot. The optional S3 symbol group is all-or-nothing; S1/S2 libraries retain
their existing serial path. Native teardown can return busy. Simple must honor
that result and cannot `dlclose` until every request is closed.

S3 isolates mutable contexts but still serializes execution and serializes full
llama sequence snapshots. A4 begins only with immutable physical page identity,
reference counts/leases, request-private COW tails, and paged attention.
