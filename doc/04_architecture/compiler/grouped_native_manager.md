# Grouped native build manager

The admitted Phase 2 compiler is the sole producer for two independent post-Phase-2
lanes. Phase 3 and Phase 4 each run through a build manager; Phase 4 does not wait
for Phase 3. Each phase/backend/producer tuple has its own state, writable cache,
and output authority. LLVM is completed before Cranelift in each lane. The task
inventory covers the five bootstrap binaries and every logical module, including
the OS inventory. No diagnostic object is a completed loadable module.

## Ownership and data flow

1. A compiled preparer validates the Phase 2 producer digest, Stage 2 full-source
   authority, SCV snapshot and receipt, warm package-index generation and its
   compiler-authored seven-field variant receipt. Distinct SCV compile-inventory,
   warm source-inventory, and Stage 2 source-inputs digests retain their domains.
2. The preparer reads the warm index once. It verifies exact full-inventory
   membership and dependency-first complete SCCs, then writes bounded, pinned
   per-group route receipts. Routes contain metadata and archive identities,
   never another full-source copy. The Phase 2 index is read-only; routes are
   write-once manager state. Each group child uses a private writable cache.
3. A group manifest binds phase, producer, source/index/variant identities,
   backend, target, full inventory, complete SCC set, group route, output kinds,
   and memory/thread limits. A broker launches one compiler child per group in
   an isolated process tree. Before spawn it rechecks program, input, receipt,
   route, memory, and disk pins. The compiler loads the selected group and its
   admitted dependencies once, freezes MIR capsules, and emits individual
   results. No manager or child may publish a partially complete SCC.
4. The compiler writes a `.started` marker immediately before each backend
   dispatch, then an atomic typed module result. The manager reads them only
   after the whole child tree is reaped, hashes private outputs, and promotes
   complete successful SCCs. A started member with no result after a crash is
   CRASHED/TIMEOUT; an unstarted one is NOT_RUN. Resume keeps exact pins and
   retries only non-OK complete SCCs. The parent is the only ledger writer.
5. Completion requires exact inventory accounting, terminal process reaps,
   output digest verification, and target-host load qualification of every SMF.
   OBJECT receipts are useful diagnostics but cannot satisfy this gate.

The generic build manager separately owns each binary task. Its compiled
`--job-from-inventory` mode pins a bounded file-based full source list, avoiding
Windows command-line overflow. Canonical bootstrap scripts invoke and verify
manager results for every post-Phase-2 task, with no direct compiler fallback.

## Explicit admission limits

The current SMF driver is not a qualified per-module producer. It concatenates
object sections, emits one synthetic `main` symbol, and does not remap ELF
relocation symbol indices to the SMF export table; Windows COFF extraction is
absent. `link_to_smf` is a file write, not a loader test. The fuller writer is
currently Linux x86_64-specific. Until symbol/section/relocation translation
and target-host loader tests exist, the preparer accepts OBJECT only and the
canonical SMF completion gate remains closed.

Windows JobObject supervision supplies process-tree ownership. The present
POSIX Process Observation V4 supports leader-only observation and cannot
enforce or prove aggregate descendant memory/reap ownership. Linux execution
remains closed until a durable tree owner is implemented. The LLVM two-thread
qualification path is also not a production capability until it runs under an
admitted self-hosted compiler, observes same-process overlapping worker IDs,
and verifies byte parity against the serial objects. A requested `--threads`
value alone never establishes effective parallelism.

These limits are release gates, not exceptions to the completion definition.
They prevent a diagnostic run from being described as an end-to-end build.
