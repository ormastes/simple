# Selective native MIR process ownership

Status: implementation candidate; runtime qualification UNRUN. This document
does not admit a release, a compiler build, a measured worker footprint, or a
performance result.

The existing MIR shard path runs the entire frontend and whole-program mono in
every worker before claiming modules. The declaration-summary producer already
encodes complete post-mono HIR, but its first version discards those bytes.
Increasing that path's worker count multiplies frontend resident memory.

The selective route is opt-in with `SIMPLE_MIR_SELECTIVE=1`. One producer runs
the ordinary frontend and mono, freezes the complete ordered declaration
inventory, persists each complete post-mono body, and publishes a sealed
manifest last. The manifest binds source identity, actual compiler/frontend
cache framing, target, semantic options, provider order, physical emission
order, body/declaration digests, and exact mono placement publications. The
direct-process seal is separate from full0 archive authority.

After the producer is reaped, the existing bounded process ledger schedules one
physical emission per process, with at most fifteen active processes. A job
includes its physical primary and all actual logical specialization bodies.
The worker crosses the source-admission/fingerprint boundary, then bypasses
parse, HIR, typecheck and mono. It admits declarations, claims its job, and
decodes only that job's complete bodies inside transient scopes. A codec round
trip, exact body identity, declaration reprojection and original mono placement
evidence must all agree before lowering.

Every process owns its mutable lowering, symbol tables, provider caches,
bootstrap registries, generated symbols and transient arenas. Sealed declaration
symbol tables are copied through the existing codec before mutable use. Primary
and secondary bodies use the same lowering owner; raw MIR is never combined
between processes. Existing borrow, async, optimization, weaving, debug,
typed-storage validation and native object emission remain the post-MIR chain.
Unsupported frontend-owned state is refused explicitly rather than omitted.

The serial canonical type allocator remains unchanged. A fresh lowering for
every physical job makes its allocation history independent of worker count and
completion order. LLVM and Cranelift native codegen erase nominal handles to
their existing pointer ABI; consistent references within one emission still
matter for MIR equality and verification. The selective cache namespace binds a
versioned object-owner context and the complete declaration repository. The
existing capsule identity and object witness still validate emitted objects.
Serial cache namespaces retain their existing spelling.
An explicit `backend_plugin_path` is refused by the shared producer, worker and
link eligibility predicate: dynamic resolution can override a builtin backend
before its name is selected, so a matching name cannot establish that boundary.

Workers publish object sidecars before terminal PASS records. Their ledger key
is the object-owner context, including source and semantic/declaration identity.
The final process independently admits the same bundle, bypasses the frontend,
validates every terminal/object, and links in the manifest's physical order.
The parent remains the authority for launch, aggregate verdict and publication.
Selective failures never authorize a full-frontend or serial fallback.

Admission requires explicit parent, worker and exporter RSS estimates, a phase
allocation, an enclosing enforced process-tree ceiling, host headroom, and a
disk allocation plus reserve. The larger of producer/link memory and the
concurrent worker sum must fit beside the parent. Calculations use subtraction
and division to avoid overflow. No-fit remains zero. Disk admission includes
temporary and final files, logs, expression artifacts and native object cache
growth in the declared reserve; write failures remain fatal. These are
estimates and a space snapshot, not proof of a worker's actual maximum RSS or a
disk quota. The existing process-tree watchdog enforces aggregate RSS.

Actual post-claim body/lowering intervals are recorded per job with its process
ID and object context. Qualification must show overlapping real child work,
semantic equivalence for both native backends, schedule-independent ordered
link inputs and context, cold/warm cache behavior, provider enum/layout/default
and alias specialization behavior, and refusal/reaping on malformed/stale data
or child failure. Unit arithmetic and source inspection alone cannot satisfy
these gates.
