# MIR fork children regrow the inherited heap registry (2026-10-25)

**Status:** fixed in the Rust runtime (`value/heap.rs` `HeapRegistry`,
`fork_shared_heap_v1.rs`) and its C twin (`runtime_native.c`,
`runtime_fork.c`). Measured on a relinked Stage 2; see "Evidence".
**Lane:** Phase 3 native-build, `SIMPLE_MIR_FORK_WORKERS=N`.

## Symptom

Runs 23/24/25 (1471 modules, 12 fork workers) were OOM-killed in
`native_compile`. All 12 children grew together to 4.4-5.4 GB
Private_Dirty each. Cgroup anon went from 68.8 GB to 101.6 GB in 84 s.
The growth was deterministic across runs.

## Root cause

Every heap object is recorded in one process-wide membership set.
`HEAP_ALLOCATION_REGISTRY` is a hashbrown `HashSet<usize>` in
`src/compiler_rust/runtime/src/value/heap.rs` (Stage 2 runs on this Rust
runtime). Its C twin is the open-addressing `rt_core_immortal_registry` in
`src/runtime/runtime_native.c`. A fork child inherits the parent's table and
keeps calling `register_heap_ptr` / `unregister_heap_ptr` on it:

1. Each insert and erase writes a control byte and a bucket. Those writes land
   at random pages of the inherited table, so each child gradually makes its
   own private copy of the table.
2. The first time the table grows, the child allocates a fresh table twice the
   size and rehashes every parent entry into it. All children start from the
   same fill level and allocate at the same rate, so they all grow at the
   same module, in lockstep.

Measured on the 2-worker probe (142-module closure, parent heap 1.6 GB): a few
seconds after the fork, each child mapped a new 147,460 kB anonymous region,
all of it private. That is exactly a 2^24-bucket `HashSet<usize>`: 2^24 × 9 B
+ 16, rounded to a page. In the same sample the inherited 73,732 kB region
(2^23 buckets) was freed. Scaled to the Phase 3 parent (~27 GB heap, a 2^28
table), the same step costs about 4.8 GB per child. That matches the
4.4-5.4 GB Private_Dirty per worker in run 25.

## Fix

Right after `fork()`, the child calls
`heap_registry_freeze_for_fork_child()` (C:
`rt_core_immortal_registry_freeze_for_fork_child_v1()`). This makes the
inherited table a read-only frozen layer:

- new objects go into an empty child-local table;
- erasing an inherited pointer records it in a small erased set;
- re-registering an erased inherited address removes it from the erased set;
- `contains = live || (frozen && !erased)`.

Membership, the exactly-once erase, and the count are all unchanged. A nested
fork keeps the first frozen layer.

Tests:
- Rust: `value::heap::fork_registry_tests`.
- C: `src/runtime/test/rt_fork_registry_freeze_selfcheck.c`, which checks a
  real fork child and an in-process freeze.

## Evidence

Stage 2 was not rebuilt. The seed relinked the cached Stage 2 objects
(`reused=1593`) against a rebuilt `libsimple_native_all.a`. Relinking with
the original archive reproduces Stage 2 byte for byte (`63262660...`).

Binaries:
- before: `e7358299...`, the base archive;
- after, registry fix only: `c9234dec...`;
- after, all three fixes: `8a48b98c...`.

The probe: 142-module closure, 2 fork workers, 119 objects.

| run | per-child mappings after the fork | child Private_Dirty at codegen start (sum) |
|---|---|---|
| before | new private 147,460 kB table; inherited 73,732 kB table privatized | 1110-1120 MB |
| after | inherited table stays shared (`pd=32 kB`); child overlay 36-74 MB | 916-945 MB |

For the object check, see
`native_codegen_object_nondeterminism_2026-10-25.md`: every module digest
from an "after" run either matches a digest seen in some "before" run, or
belongs to a module whose object already varies between runs of the
unmodified binary.
