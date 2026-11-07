# Bootstrap host reserve: local research

The mirgen2 Phase 2 native build completed 1592 modules but `p2_add` sanity
failed before generating an executable. Its rejection and producer identity are
retained in `doc/08_tracking/bug/shard_host_reserve_scoped_cap_2026-11-06.md`.

`src/app/cli/shard_mem_clamp.spl` preferred a known compiler RSS cap to host free
memory, then subtracted the host free-memory reserve. That both consumed an
entire 24 GiB compiler cap on a roomy host and ignored low host free memory when
a larger compiler cap was configured. `shard_threads_parent_cap_for` separately
reserves coordinator space and remains unchanged. `file_worker_pool_refusal.spl`
reports the arithmetic used by worker admission.

The focused native fixture imports the production helper. Its unchanged eight
checks fail before the repair and pass afterward. The broader SSpec and Phase 3
admission are separate pending gates; a fixed arithmetic helper cannot admit
the rejected producer.
