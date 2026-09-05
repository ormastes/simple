<!-- codex-design -->
# Compiler loader script cross-language performance architecture

Status: **DECISION-READY, NOT ACCEPTED**. Feature and NFR option documents exist,
but the mandatory user selection has not occurred. This document records the
architecture common to all options; it must be reviewed against the selected
scope before design completion is claimed.

## Layer ownership

1. The loader resolution layer owns cache keys, lookup order, negative results,
   and invalidation. It calls the file facade and never owns probe counters.
2. The file facade owns existence-probe admission and accounting. Native
   providers use generation/lease atomics; the interpreter provider is
   explicitly single-thread and fail-closed.
3. Interpreter collection owners implement packed-byte value semantics,
   copy-on-write mutation, freezing, widening, clone, and equality.
4. The SFFI adapter owns foreign descriptors and temporary capabilities. No
   raw packed-storage pointer becomes a language value or outlives one call.
5. The performance harness owns executable identity, actual-mode receipts,
   bounded process execution, semantic equivalence, samples, and report schema.
6. SPipe and focused native/Rust tests consume these owners as evidence; they
   do not reimplement product behavior.

This is a layered capsule rather than an MDSOC feature transform: the behavior
has stable semantic owners and should not be woven through unrelated modules.
Cross-cutting provenance and measurement are report metadata, not mutations to
loader or collection semantics.

## Data and control flow

For resolution, a request is normalized, checked against the appropriate cache,
and on miss probes candidate paths through `rt_file_exists`. The resolved path
or exact miss is cached. Reset clears every resolver cache and its diagnostic
uncached counter.

For failed-probe evidence, `begin` opens one generation. Each facade call first
acquires a lease, performs the existence operation, records total/failed under
that captured generation, and releases the lease. `end` closes admission,
drains leases, and packs counts. Stale/overlap/overflow states return negative
errors.

For packed bytes, byte-preserving operations return packed storage. Mutation
uses the receiver/place owner so aliases obey copy-on-write and projected
places write the rebuilt root back. A non-byte insertion widens once. Foreign
calls receive a descriptor `{base, byte_length, access}` backed by storage held
alive in call scope; descriptor validation precedes every pointer exposure.

For performance, the harness admits path/hash/provenance and actual execution
mode before starting samples. Every peer produces a semantic receipt. Only
successful, equivalent, correctly sized samples enter the retained table.
Timeout and tool absence are terminal dispositions, not numeric samples.

## Cache and invalidation strategy

Module-only cache entries are limited to caller-independent roots. Relative
lookups use a caller-sensitive key. Explicit reset is authoritative during
tests and compiler lifecycle boundaries. No request-path full-tree scan,
subprocess, retry sleep, or repeated reread is introduced. The harness may run
subprocesses because measurement is its explicit maintenance purpose; each is
bounded.

## Safety and errors

- Probe windows fail closed for overlap, stale generations, overflow, and
  counter overflow.
- Frozen packed receivers reject mutation. Out-of-bounds foreign descriptors
  fail before pointer use. Input-only capabilities cannot write back or escape.
- Harness failures preserve phase, tool, numeric status, and timeout identity.
  A stale report is replaced by `running` before compiler invocation and by one
  terminal status on exit.
- Stage 2/3 and Rust-level tests are labeled diagnostics. They cannot establish
  deployed self-hosted performance or CLI compatibility.

## Observability and provisional budgets

The resolver exposes uncached-resolution counts for deterministic tests; the
file facade exposes total/failed counts for explicit measurement windows. The
harness records path/hash, tool versions, host metadata, actual mode, checksum,
wall samples, p50/p95, maximum RSS, and terminal status. Current thresholds are
provisional until the NFR option is selected: 100/1 uncached counts, cached
failed probes no more than 10% of baseline, 1 MiB below 1 second, 32 MiB below
30 seconds, and RSS no more than four times byte payload.

## Verification boundaries

Focused Rust tests may prove packed-byte representation and SFFI lifetime.
The C selfcheck may prove native probe lifecycle independently. Source contract
scripts may prove fail-closed harness shape. Loader/performance SPipe, compiler
surface checks, and live rows require the identity admitted by the selected
requirements; no earlier bootstrap stage is silently substituted.

## Pending decision

After the user selects one feature option and one NFR option, delete the
unchosen option documents, write final REQ/NFR documents, reconcile this file's
scope and budgets, and obtain highest-capability design review.
