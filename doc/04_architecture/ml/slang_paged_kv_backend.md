<!-- codex-design -->
# Slang physical paged-KV architecture

Date: 2026-09-08. Architecture reviewer: Astra.

## Decision

Add a backend-neutral physical page provider below Slang's serial request owner.
The provider owns tensor storage and kernels; Slang owns page identities, block
tables, reservations, prefix records, reference accounting, and transactions.
Opaque llama sequence snapshots remain the S3 adapter and cannot implement this
interface by slicing serialized bytes.

## Ownership

`KvPoolId`, `KvPageId`, and request handles combine pool/model generation, slot
generation, and slot. A request table contains ordered sealed prefix pages plus a
private tail. Cache records and request mappings each hold explicit references.
The owner releases storage only when the combined count reaches zero.

## Transaction boundary

Admission reserves descriptors and physical bytes first. Execution writes only
to transaction-exclusive staging pages that cannot alias a published table,
cache record, or another transaction. A successful, logits-producing commit
atomically publishes table, cursor, and request-owned logits. Failure consumes
or aborts staging, preserves the old table/cursor, and invalidates sampling.

## Provider variants

- Physical page provider: attention consumes a Slang-supplied block table; this
  is the only S4 completion path.
- Pinned llama extension: acceptable only if it exposes equivalent allocation,
  page-table, copy, decode, and failure contracts.
- Stock llama shared-sequence precursor: separate capability and telemetry;
  requires unified KV, explicit sequence/position batches, supported models, and
  request-owned logits. It is not S4.

## Nonclaims

No simultaneous execution, continuous batching, GPU residency, spill, remote
transport, or speedup is claimed by the architecture alone.
