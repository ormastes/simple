# Grouped native build manager

The admitted Phase 2 compiler is the sole producer for two independent post-Phase-2
lanes. Phase 3 and Phase 4 each run through a build manager; Phase 4 does not wait
for Phase 3. Each phase/backend/producer tuple has its own state, writable cache,
and output authority. LLVM is completed before Cranelift in each lane. Phase 4
builds five binaries per backend; Phase 3 builds its bootstrap binary per backend
and separately proves its complete MIR inventory. Both lanes build every included
logical module, including OS modules, through complete V2 index and grouped SMF
routes. No diagnostic object is a completed loadable module.

## Ownership and data flow

1. A compiled Phase 2 authority publishes a complete byte snapshot of the admitted
   source, SCV, full V2 index configurations for each phase/backend, and a typed
   module-role partition. All source bytes remain in the authority. The module
   inventory excludes only exact paths named in the checked-in role policy, with
   each excluded path, source digest, and reason bound in the receipt. OS and real
   unit modules remain included; no historical module count is hardcoded. A
   compiled preparer validates these pins, the package-index generation, and its
   compiler-authored variant receipt.
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

The generic build manager separately owns 12 binary tasks and four full-V2 index
tasks. Its compiled `--job-from-inventory` mode pins a bounded file-based full
source list, avoiding Windows command-line overflow. The canonical script uses
the same admitted Phase 2 producer for both phases, attempts Phase 3 even if
Phase 4 fails, and publishes completion only after all 12 binary results and
four phase/backend index, group, ledger, and output proofs pass read-only
verification. Each backend owns its own mutable roots and result receipts.

An explicit physical host directory may serve as the portable parse CAS on
Windows and WSL through their mapped paths to the same storage. The canonical
script pins that directory for generic manager tasks; the compiled group
preparer rejects source/index/state/output overlap and seals it into each group
worker. Cells contain only bounded immutable flat-pool parser payloads. Their
keys bind raw source, exact target-preprocessed parser input, target decision,
parser/codec source, feature switches, and portable logical source path. Reads
reject reparse/symlink leaves and verify payload hashes. A miss reparses and
hydrates only the worker's private cache. Native objects and mutable indexes
are never shared between operating systems.

## Current qualification boundary

The source includes per-member SMF production and admission, Windows JobObject
and Linux cgroup process-tree owners, typed retry/terminal ledgers, and a bounded
wave scheduler. These implementations have not run under an admitted self-hosted
Phase 2 compiler from this exact source revision. The current older bootstrap
candidate cannot be substituted: its admitted source snapshot differs, and the
canonical image builder checks that equality before building manager images.
The complete V2 semantic index may also exceed the current host cap because it
materializes the full HIR/MIR graph before grouped codegen; its peak has not been
measured under the new runner. A hard-cap failure must remain an incomplete
receipt, not a success claim.

Effective inner-thread overlap and binary parity require an admitted compiler
run; a requested `--threads` value does not prove either. The Windows and WSL
parse-cell reader selfchecks pass, but a real cross-OS parser-cache hit and
end-to-end qualified SMF ledger remain unverified. Release admission requires
the new-source Stage 2 producer, exact terminal results for both phases and
both backends, target-host SMF qualification, and the canonical final verifier.
