# SimpleOS Hot-Path Performance Contract — 2026-08-20

Status: **BLOCKED (no admitted Stage 4 self-hosted test/runtime)**

This report defines NFR-002/NFR-003 admission and the executable campaigns for
the hot paths changed in the hardening wave. It contains no measured runtime
result and authorizes no performance PASS. The imported Stage 2 artifact may
compile/native-build only; it cannot run SSpec, benchmarks, or promotion gates.

## Fail-closed evidence contract

`src/lib/common/contracts/execution/simpleos_performance_v1.spl` requires:

- 10–1024 nonzero raw metric samples and the same number of nonzero raw RSS
  samples;
- recomputation of max RSS from the raw repetitions, equal to the submitted
  summary;
- nearest-rank p50/p95/p99/max plus a conservative CV basis-point report;
- an exact population-CV comparison, using
  `n*sum((x-min)^2)-sum(x-min)^2 <= sum(x)^2/400`, so exactly 5% passes and a
  value above 5% fails without a floor-mean approximation;
- checked sums, products, centered squares, regression scaling, and bounded
  metadata/artifact arrays; arithmetic uncertainty returns `Overflow`;
- a distinct, valid, bounded artifact set containing the fixture, benchmarked
  binary, image, configuration, and baseline-identity hashes;
- nonempty CPU, frequency, accelerator, and noise identities, a fixed warmup,
  native execution, explicit external comparability, exact canonical budgets,
  and inclusive 5% metric/RSS regression boundaries.

Missing RSS, a forged max, duplicate/missing campaign artifacts, non-native or
non-comparable evidence, noise above 5%, zero samples, and arithmetic overflow
all reject. `test/01_unit/common/simpleos_performance_v1_spec.spl` contains the
behavioral boundary and counterexample matrix; it is not source introspection.

## Executable hot-path campaigns

Run these only with a receipt-admitted self-hosted Simple runtime. Every timed
campaign must retain the exact argv, source/binary/image/config/fixture/baseline
hashes, CPU model, governor/frequency, accelerator, affinity/noise controls,
warmup count, at least 10 raw metric/RSS pairs, p50/p95/p99/max, max RSS, CV,
exit status, owner, and independent reviewer.

| Lane | Production evidence | Executable gate/campaign | Admission rule |
|---|---|---|---|
| TLS fragmentation | `TlsApplicationRecordStreamV1` cumulative and per-ingest byte-work receipts | `test/01_unit/lib/common/net/tls_application_record_stream_spec.spl` | One-byte fragments exercise the production accumulator; N→2N byte work is linear, retained bytes stay bounded, and rejected/no-progress input adds no work. |
| SSH/SFTP fragmentation | `SftpAccumulatorWorkV3` from the live SFTP owner | `test/01_unit/os/apps/sshd/ssh_sftp_v3_spec.spl` | One-byte ingress asserts actual append/frame/remainder copies, header scans, completed frames, peak retained bytes, and no saturation. A future N→2N fixture must remain linear. |
| NVMe queue/reset | production `NvmeDriver` counters and `src/os/services/vfs/q35_pure_nvme_perf_boot.spl` | `test/01_unit/os/drivers/nvme/nvme_driver_lifecycle_contract_spec.spl`, `nvme_bulk_io_bounds_spec.spl`, `nvme_queue_boundary_spec.spl`, then the Q35 boot entrypoint | One 4 KiB burst submits one command; a batch submits exactly `lbas.len()` commands below queue depth; completion waits equal submitted commands; reset/lease mismatch fails closed. Q35 timing must not accept `skipped`. |
| Filesystem metadata | mount-table `resolve/open/pread/pwrite/fsync` and FAT32/NVFS owners | `test/05_perf/bench/fs_driver_mount_table.spl` and `fat32_microbench.spl` are operation-count/proxy diagnostics; native promotion requires the production device campaign | Fixed image, 4 KiB blocks, at least 10,000 resolve/open operations, 20 warmups, at least 10 measured repetitions, and p95 <=2.5 ms. In-memory/tick proxies cannot promote NFR-002. |
| Filesystem sequential I/O | FAT32 `read_bytes/write`, NVFS `arena_append_impl/arena_readv_impl/arena_fsync_impl`, and mount-table I/O | `test/05_perf/bench/fat32_4k_compare.spl` and `nvfs_arena_throughput.spl` are diagnostics; native promotion requires at least 64 MiB through the production block/device path | Fixed 64 MiB payload, 4 KiB blocks, named cache/direct-I/O and flush mode, >=100 MiB/s median, raw latency/RSS samples, and durability success. In-memory results cannot promote. |

Canonical focused commands after Stage 4 admission are:

```text
SIMPLE_NO_STUB_FALLBACK=1 bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/common/simpleos_performance_v1_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/lib/common/net/tls_application_record_stream_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/os/apps/sshd/ssh_sftp_v3_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/os/drivers/nvme/nvme_driver_lifecycle_contract_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/os/drivers/nvme/nvme_bulk_io_bounds_spec.spl --mode=interpreter
```

Before any command, the binary path/hash/stage/command receipt must authorize
`test`; silent Rust-seed fallback, Stage 2 compile-only admission, missing raw
samples, or a proxy-only result leaves this report `BLOCKED`.
