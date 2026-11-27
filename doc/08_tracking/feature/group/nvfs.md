# Feature Group: nvfs

| ID | Status | Device | Component | Priority | Title | Pipeline Evidence |
|----|--------|--------|-----------|----------|-------|-------------------|
| FR-STORAGE-0004 | current | nvfs | nvfs | P1 | MountTable.resolve() uses slice() which is broken in baremetal Cranelift | design |
| FR-BENCH-CLOCK-002 | current | nvfs | nvfs | P2 | Replace PIT-ch2 TSC calibration with HPET/PMTMR | design |
| FR-NVFS-N4a-001 | current | nvfs | nvfs | P1 | Scrub repair path: detect + repair from reflink peers | design |
| FR-NVFS-N4b-001 | current | nvfs | nvfs | P2 | Proactive scrub scheduler + META_DURABLE replica repair | design |
| FR-N3-001 | current | nvfs | nvfs | P1 | Replace flat pmap sidecar with B-tree keyed by (arena_id, offset) | design |
| FR-NVFS-N5b-001 | current | nvfs | nvfs | P2 | B-tree rebalancing on delete (merge / rotate) | design |
| FR-BENCH-CLOCK-001 | current | nvfs | nvfs | P1 | Add rt_time_now_ns() for hosted and baremetal targets | design |
| FR-NVFS-N6b-001 | current | nvfs | nvfs | P1 | Raw send / encrypted replication stream (btrfs-send style) | design |
| FR-BENCH-BASELINE-001 | current | nvfs | nvfs | P1 | Run bench harness with real clock and record baseline numbers | design |
| FR-BENCH-ARENA-ITER-001 | current | nvfs | nvfs | P2 | Reduce nvfs_arena_throughput iter counts for interpreter budget | design |
