# Concurrency Architecture — Lockless by Default

**Status:** Normative. **Adopted:** 2026-11-04 (owner decision).
**Scope:** all Simple code: compiler, stdlib, runtime, tooling, userland
services and apps. Kernel/driver HAL code may use locks only under the explicit
exception rule in §3.

## 1. Rule

Concurrency in Simple is **lockless by default**. Shared state is either
**immutable** or updated by **compare-and-swap (CAS)-style** publication. A lock,
mutex, or file lock is a documented exception. It is never the default tool.

## 2. Default primitives (in order of preference)

1. **Immutable / persistent data and content-addressed values.** Readers never
   block and never see torn state. Updates build a new value. Equal content
   means an equal name.
2. **Message passing / actors with ownership transfer.** This is the existing
   actor and async model
   ([async infrastructure](../async_infrastructure.md),
   [SimpleRing](../../simple_ring_async_base.md)). Rings stay single-owner.
   Values cross a boundary by move, not by shared mutation.
3. **Atomic CAS on small cells.** Atomically swap a pointer to an immutable
   value, use a versioned compare-and-swap, or append to a log whose entries
   are unique.
4. **Per-owner private state merged at read time.** Each writer owns its own
   shard. Readers fold the shards together, so there is no shared write cell.

### 2.1 Files and IPC across processes

- Write to a private temp file, then **publish with an atomic rename**.
- Use **content-addressed names**. Two writers producing identical content is a
  benign race: either rename wins and the result is the same.
- **No in-place writes** to a published file.
- Logs are **append-only, one file per event**, with unique names. Never use a
  shared append handle.
- Mutable "current" state is an **atomic pointer-file swap**: write a new
  pointer file and rename it over the old one. The pointer names an immutable
  object.

## 3. Locks: explicit exception only

Locks, mutexes, and file locks are allowed **only** where they are explicitly
specified and justified. Examples are an OS/driver HAL, a hardware register
sequence, or an external API that requires a lock. Every lock must:

- carry an explicit annotation or a documented exception with a named **owner**;
- be **bounded**, with a timeout or a bounded critical section;
- **fail closed** when acquisition fails or times out;
- **never be held across `await` or I/O**.

**Review rule:** a new lock without a documented exception is rejected in
review.

## 4. Correctness requirements

- **ABA:** every CAS cell that can recycle a value uses a version counter or a
  tag. A bare pointer compare is not enough when nodes are reused.
- **Progress:** lock-free is the baseline. Use wait-free where a real-time or
  kernel-adjacent path needs bounded steps per operation. State which guarantee
  the code provides.
- **Memory ordering:** publish with release and observe with acquire. Use
  relaxed ordering only for counters that publish nothing. Name the ordering
  at each atomic site.
- **Bounded retry:** CAS loops have a retry bound with backoff. Exhausting the
  bound returns a typed result. It never spins forever.
- **Panic-free (ADR-006):** a CAS failure is a typed retry/result
  (`Result`/`Option`, for example a `Contended` variant), never a panic.

## 5. Testing

- **Stress specs** run many writers against one cell or file and check for lost
  updates, torn reads, and duplicate or missing entries.
- **Interleaving tests** force the race windows (check-then-act,
  publish-then-read, ABA reuse) deterministically.
- **Every concurrency bug is P0.** Root-cause it, add a stress spec, and audit
  sibling claim/publish paths for the same shape.

## 6. Motivating case

The compiler/SCV refresh path previously serialized on shared mutable state and
locks. Its lockless redesign is the reference application of this document:
[`doc/05_design/compiler/scv/lockless_refresh.md`](../../../05_design/compiler/scv/lockless_refresh.md).

## 7. Relation to MDSOC+

For MDSOC+, cross-concern state is shared only as immutable snapshots. Concerns
communicate by CAS or by message passing, and locks live only at the
kernel/driver HAL boundary. See
[MDSOC+ § Concurrency](../../compiler/mdsoc/mdsoc_architecture_tobe.md#concurrency-lockless-by-default).
