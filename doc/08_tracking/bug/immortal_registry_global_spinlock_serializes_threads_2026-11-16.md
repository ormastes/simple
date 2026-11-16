# C runtime heap-registry lookups took one global spinlock, serializing every native thread (2026-11-16)

Status: verification-pending

## Defect

`rt_core_is_registered_immortal_ptr` (`src/runtime/runtime_native.c`) is the
membership check behind every validated heap access in the C runtime:
`rt_array_get`/`rt_array_push`/`rt_core_array_reserve`,
`rt_typed_words_i64_push`, `rt_enum_check_variant`, text decode, and more. It
took `rt_core_immortal_registry_lock`, a bare `atomic_flag` test-and-set
spinlock with no backoff, shared by the whole process. Every natively built
isolated-thread worker therefore spun on one cache line for every array or
enum access.

## Evidence

Measured on Windows x86_64 with the native `link_driver.exe` from the #9808
lane, linking 200 objects with 120k relocations:

- jobs=1 took 30 s. jobs=16 took 42 s.
- The parallel phases themselves went from about 6.5 s to about 18.5 s.
- With jobs=116, the run took 112 s of wall time and 5182 CPU-s. That is
  about 46 cores busy-spinning.

`lldb bt all` samples taken during the relocation phase found 14 of 16
workers in `rt_core_is_registered_immortal_ptr` or
`rt_core_register_immortal_ptr`.

## Fix

- **Lock-free reads.** Each table is one block `{cap, slots[cap]}`, published
  through an atomic pointer, and slot loads and stores are atomic.
  A resize retires the old block. A later writer frees retired blocks only
  once every striped per-thread reader counter reads zero.
- **Sharded writers.** Pointers are split across 64 shards by the top hash
  bits, the same scheme as `heap.rs`'s `HeapRegistryShard`. Each shard has its
  own lock, table, retired list and fork-child overlay, each on its own cache
  line. `rt_core_immortal_registry_lock` is now shard 0's lock, so the
  try-lock gate in dict scope-read and the fork selfchecks still compile.

Selfcheck: `src/runtime/test/rt_immortal_registry_lockfree_read_selfcheck.c`.

- **Before the fix:** FAIL. A lookup blocks while the writer lock is held.
- **After the fix:** PASS. 8 readers against 4 writers in 1.1 s, with 0
  false negatives across grows and tombstone rehashes. Readers alone took
  7.6 s.

## Results

Same driver and input. Output sha is `892A4B79AE45` at every job count.

| jobs | before ms | before CPU-s | after ms | after CPU-s | peak WS |
|---|---|---|---|---|---|
| 1 | 30059 | ~31 | 29595 | 30.0 | 9.80 GB |
| 2 | 28779 | | 29111 | 31.6 | 9.93 GB |
| 4 | 30659 | | 28757 | 32.5 | 9.93 GB |
| 8 | 34448 | | 27979 | 33.4 | 9.98 GB |
| 16 | 41764 | 104.8 (read fix only) | 28275 | 35.5 | 10.02 GB |

16 jobs are no longer slower than 1, and spin CPU is gone. The remaining
wall time is Amdahl-bound. The serial `elf_relax_tls` phase takes about
21.5 s and grows memory to about 9.3 GB. That is the single-thread lane's
10 GB bug, not a threading cost: RSS is flat across job counts.

## Still open

- This selfcheck is not yet wired into
  `scripts/check/build-core-c-bootstrap-runtime-capsule.shs`. It
  `#include`s `runtime_native.c`, so it needs a link line that does not also
  pull the runtime archive.
- The ucrt process heap (`RtlAllocateHeap`) is a secondary contention point.
- I have not checked natively whether the dropped array/struct worker
  argument bug (`isolated_thread_args_drop_arrays_structs_2026-11-16.md`)
  affects the C spawn path. That path shares data words, so the bug may be
  interpreter-only. Probe: `build/elfpar/argprobe.spl`.
- **Fork no-deadlock selfchecks hold only shard 0.** This affects
  `local_unix_fork_origin_v1_selfcheck.c` and
  `local_unix_listener_now_v1_selfcheck.c`. They still pass, but they no
  longer cover child registrations in the other 63 shards. They need a helper
  that holds all shards.
- **Retired tables can wait a long time to be freed.** Reclaim needs every
  reader stripe at zero at the same moment, so under constant reads retired
  tables may never be freed. The leak is bounded: tables double, so retired
  memory per shard stays under its live table size. A per-shard epoch would
  remove the leak.
