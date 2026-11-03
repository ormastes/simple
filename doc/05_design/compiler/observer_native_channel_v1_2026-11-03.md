# Resident observer channel V1

Status: implementation candidate; Simple execution and concurrent native qualification pending.

The native channel is a private transport component beneath the existing observer facade. It does not implement a provider, enable a target, establish a manifest, or make caller-supplied identities authoritative. The public facade and canonical event schema are unchanged.

## Ownership

The future process session owner provisions disjoint resident arenas before callbacks become reachable. Each arena belongs to one generation and one logical context; its immutable metadata and storage remain resident until process exit. The owner must enforce the process-wide total storage/metadata cap and the maximum retained generations. This component performs no allocation and cannot enforce a process-wide cap on storage supplied elsewhere.

Initialization takes an **unsafe exclusive unpublished arena loan**, not a public handle. The caller proves its actual allocation extent and 8-byte alignment. Initialization checks bounded size arithmetic and the selected runtime's lock-free capability at each atomic cell. It does not test arbitrary address validity. Publishing occurs only after successful initialization. Reinitializing or recycling a published arena is prohibited even after drain.

Callback access is an **unsafe frozen arena reference plus a producer reservation**. All mutable publication/index/counter cells use the existing sequentially consistent raw atomic owner. Ordinary payload words have one producer and one consumer, with ownership transferred by the indices. Handle-backed atomics are deliberately not used: their registry/provider can lock. The single producer reservation also rejects synchronous reentry and competing producer calls without blocking.

Polling takes a separate **unsafe writable output loan**; arithmetic and alias checks reject overlap with the channel's header and payload. A consumer reservation serializes competing poll operations. The caller retains and bounds the output allocation. No integer input establishes a mapping or memory-safety authority.

## Linearization and publication

The gate has four states: open `0`, open with one producer `1`, closed `2`, closed with one producer `3`. Producer admission is a single compare-exchange `0 -> 1`. Close sets bit 1 with compare-exchange. A successful producer always releases exactly one reservation by subtraction, yielding `1 -> 0` or `3 -> 2`; close cannot be lost by this release. There is no reopen operation or generation recycling.

Close is bounded and may return Busy if contention prevents its CAS. A success means admission is closed; it does not mean callbacks or buffered output drained. Drain requires closed without a producer, no active consumer, and equal published/released cursors. Resident lifetime still applies after drain, so a late rejected callback cannot access reclaimed gate storage.

This is **transport drain**, not callback quiescence or a final loss snapshot. A rejected producer can observe gate `1`, pause before updating loss, then resume after the admitted producer completes and transport drain returns true. The loss update remains memory-safe because the arena is resident, but it can change statistics after transport drain. Before final statistics, a final loss record, or completion/flush claims, the session owner must independently join or exclude callback activity. There is no reclamation or complete-session guarantee from this predicate alone.

A producer writes all twelve event words before release-publishing the write cursor. A consumer acquires that cursor before reading and copies the complete record before release-publishing its read cursor. The producer cannot overwrite the slot before acquiring the released read cursor. The raw atomic provider currently uses SeqCst, which is stronger than these release/acquire requirements.

The native producer entry accepts fixed scalar words, not a language-owned record or byte array. This avoids requiring aggregate allocation or boxing inside a callback. A separate cold typed adapter bridges `TraceEventV1` for consumers/tests; it is not the machine-hook entrypoint. The scalar transport checks the schema/record size/event tag and immutable generation/context, while manifest selection, clock and event semantics remain the callback owner's responsibility.

Monotonic signed cursors stop before overflow; exhaustion closes admission and reports failure. A full queue rejects the event without advancing publication or overwriting unread data. Reentry/full/exhaustion losses use a bounded saturating CAS counter. If counting loses precision through contention or saturation, a sticky flag marks the count as a lower bound. The future collector must emit canonical loss/control records and expose this distinction; it must not claim exact counts from this component alone.

## Verification and remaining integration

The executable specification uses real raw storage and runtime atomics. It checks full-field/high-bit encoding, FIFO wrapping, overflow, wrong context/generation, reentry, close with an outstanding reservation, output aliasing, cursor exhaustion, and drain versus queued output. Deterministically installed rare states are test-only and are not evidence of native concurrent execution.

The record transport stores native scalar words in canonical field order. A wire boundary must use the canonical little-endian codec rather than memcpy a native representation. The transport does not grant paired-span semantics or validate an event against a selected manifest.

Still required: actual session-owned retained allocation and memory accounting, safe thread/context attachment, a resident callback connected to this channel, immutable map selection, loss/control-record policy, clock ownership, target/profile admission, and compiler/linker emission. The existing LLVM callback remains a strong unresolved dependency until that actual owner is present. No fallback callback or available profile is introduced.
