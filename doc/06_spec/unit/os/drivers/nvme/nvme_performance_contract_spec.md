# Nvme Performance Contract Specification

> Tests covering NVMe production performance contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Performance Contract Specification

## Scenarios

### NVMe production performance contract

#### accepts warmed pure Simple 4K random I/O samples without C bridge or per-I/O allocation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts warmed pure Simple 4K random I/O samples without C bridge or per-I/O allocation
   - Expected: nvme_random_io_perf_sample_reason(sample) equals `ready`
   - Expected: nvme_random_io_perf_sample_ready(sample) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts warmed pure Simple 4K random I/O samples without C bridge or per-I/O allocation")
val sample = _simple_sample(120000u64, 80000u64, 900u64, 1300u64)
expect(nvme_random_io_perf_sample_reason(sample)).to_equal("ready")
expect(nvme_random_io_perf_sample_ready(sample)).to_equal(true)
```

</details>

#### rejects samples that are not measuring the production 4K random NVMe path

- rejects samples that are not measuring the production 4K random NVMe path
   - Expected: nvme_random_io_perf_sample_reason(c_bridge) equals `nvme-perf-c-bridge-used`
   - Expected: nvme_random_io_perf_sample_reason(cold) equals `nvme-perf-not-warm`
   - Expected: nvme_random_io_perf_sample_reason(alloc) equals `nvme-perf-allocation-per-io`
   - Expected: nvme_random_io_perf_sample_reason(wrong_size) equals `nvme-perf-io-size-not-4k`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects samples that are not measuring the production 4K random NVMe path")
val c_bridge = nvme_random_io_perf_sample("simple-driver", "4k-random-read-write", 4096u32, 64u16, 5u32, 120000u64, 80000u64, 900u64, 1300u64, 32768u64, true, true, false)
val cold = nvme_random_io_perf_sample("simple-driver", "4k-random-read-write", 4096u32, 64u16, 1u32, 120000u64, 80000u64, 900u64, 1300u64, 32768u64, false, true, false)
val alloc = nvme_random_io_perf_sample("simple-driver", "4k-random-read-write", 4096u32, 64u16, 5u32, 120000u64, 80000u64, 900u64, 1300u64, 32768u64, false, true, true)
val wrong_size = nvme_random_io_perf_sample("simple-driver", "4k-random-read-write", 512u32, 64u16, 5u32, 120000u64, 80000u64, 900u64, 1300u64, 32768u64, false, true, false)

expect(nvme_random_io_perf_sample_reason(c_bridge)).to_equal("nvme-perf-c-bridge-used")
expect(nvme_random_io_perf_sample_reason(cold)).to_equal("nvme-perf-not-warm")
expect(nvme_random_io_perf_sample_reason(alloc)).to_equal("nvme-perf-allocation-per-io")
expect(nvme_random_io_perf_sample_reason(wrong_size)).to_equal("nvme-perf-io-size-not-4k")
```

</details>

#### requires pure Simple random read and write to beat the C FAT baseline

- requires pure Simple random read and write to beat the C FAT baseline
   - Expected: nvme_c_parity_perf_ready(ready) is true
   - Expected: nvme_c_parity_perf_reason(slow_read) equals `simple-read-iops-not-faster-than-c`
   - Expected: nvme_c_parity_perf_reason(slow_write_p99) equals `simple-write-p99-not-faster-than-c`
   - Expected: nvme_c_parity_perf_reason(equal_read_p99) equals `simple-read-p99-not-faster-than-c`
   - Expected: nvme_c_parity_perf_reason(equal_write_p99) equals `simple-write-p99-not-faster-than-c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires pure Simple random read and write to beat the C FAT baseline")
val ready = nvme_c_parity_perf_comparison(
    _simple_sample(120000u64, 90000u64, 800u64, 1000u64),
    _c_sample(100000u64, 80000u64, 900u64, 1100u64)
)
val slow_read = nvme_c_parity_perf_comparison(
    _simple_sample(100000u64, 90000u64, 800u64, 1000u64),
    _c_sample(100000u64, 80000u64, 900u64, 1100u64)
)
val slow_write_p99 = nvme_c_parity_perf_comparison(
    _simple_sample(120000u64, 90000u64, 800u64, 1200u64),
    _c_sample(100000u64, 80000u64, 900u64, 1100u64)
)
val equal_read_p99 = nvme_c_parity_perf_comparison(
    _simple_sample(120000u64, 90000u64, 900u64, 1000u64),
    _c_sample(100000u64, 80000u64, 900u64, 1100u64)
)
val equal_write_p99 = nvme_c_parity_perf_comparison(
    _simple_sample(120000u64, 90000u64, 800u64, 1100u64),
    _c_sample(100000u64, 80000u64, 900u64, 1100u64)
)

expect(nvme_c_parity_perf_ready(ready)).to_equal(true)
expect(nvme_c_parity_perf_reason(slow_read)).to_equal("simple-read-iops-not-faster-than-c")
expect(nvme_c_parity_perf_reason(slow_write_p99)).to_equal("simple-write-p99-not-faster-than-c")
expect(nvme_c_parity_perf_reason(equal_read_p99)).to_equal("simple-read-p99-not-faster-than-c")
expect(nvme_c_parity_perf_reason(equal_write_p99)).to_equal("simple-write-p99-not-faster-than-c")
```

</details>

#### formats a single hardware-runner report line for acceptance gates

- formats a single hardware-runner report line for acceptance gates
   - Expected: nvme_production_perf_report_ready(report) is true
   - Expected: nvme_production_perf_serial_acceptance_reason(line) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats a single hardware-runner report line for acceptance gates")
val report = nvme_production_perf_report(nvme_c_parity_perf_comparison(
    _simple_sample(120000u64, 90000u64, 800u64, 1000u64),
    _c_sample(100000u64, 80000u64, 900u64, 1100u64)
))
val line = nvme_production_perf_report_line(report)

expect(nvme_production_perf_report_ready(report)).to_equal(true)
expect(line).to_contain("nvme_perf reason=ready")
expect(line).to_contain("simple_provider=simple-driver")
expect(line).to_contain("workload=4k-random-read-write")
expect(line).to_contain("direct_io_path=nvme-lease-shared-dma-4k")
expect(line).to_contain("fs_consumers=fat32,nvfs,dbfs")
expect(line).to_contain("fat32_direct_io=read-write-through")
expect(line).to_contain("nvfs_direct_io=read-write-through")
expect(line).to_contain("dbfs_direct_io=read-write-through")
expect(line).to_contain("fat32_extent_source=freestanding-fat32-extents")
expect(line).to_contain("nvfs_extent_source=freestanding-dbfs-arena")
expect(line).to_contain("dbfs_extent_source=freestanding-dbfs-arena")
expect(line).to_contain("c_bridge_used=false")
expect(line).to_contain("c_baseline_device=same-nvme")
expect(line).to_contain("c_baseline_scope=in-guest")
expect(line).to_contain("c_baseline_cache=direct")
expect(line).to_contain("vfat_baseline_device=same-nvme")
expect(line).to_contain("vfat_baseline_scope=in-guest")
expect(line).to_contain("vfat_baseline_cache=direct")
expect(line).to_contain("vfat_baseline_filesystem=vfat")
expect(line).to_contain("common_logic_shared=true")
expect(line).to_contain("allocation_per_io=false")
expect(line).to_contain("simple_read_iops=120000")
expect(line).to_contain("c_write_iops=80000")
expect(nvme_production_perf_serial_acceptance_reason(line)).to_equal("ready")
```

</details>

#### builds the canonical hardware-runner report line from measured counters

- builds the canonical hardware-runner report line from measured counters
   - Expected: nvme_production_perf_serial_acceptance_reason(line) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds the canonical hardware-runner report line from measured counters")
val line = nvme_production_perf_report_line_from_measurements(
    120000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    false
)

expect(line).to_contain("nvme_perf reason=ready")
expect(line).to_contain("queue_depth=64")
expect(line).to_contain("warm_runs=5")
expect(nvme_production_perf_serial_acceptance_reason(line)).to_equal("ready")
```

</details>

#### keeps measured-counter report lines fail-closed when Simple is not faster or allocates per I/O

- keeps measured-counter report lines fail-closed when Simple is not faster or allocates per I/O
   - Expected: nvme_production_perf_serial_acceptance_reason(slower) equals `nvme-perf-report-not-ready`
   - Expected: nvme_production_perf_serial_acceptance_reason(alloc) equals `nvme-perf-report-not-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps measured-counter report lines fail-closed when Simple is not faster or allocates per I/O")
val slower = nvme_production_perf_report_line_from_measurements(
    100000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    false
)
val alloc = nvme_production_perf_report_line_from_measurements(
    120000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    true
)

expect(slower).to_contain("reason=simple-read-iops-not-faster-than-c")
expect(alloc).to_contain("reason=simple-sample-not-ready:nvme-perf-allocation-per-io")
expect(nvme_production_perf_serial_acceptance_reason(slower)).to_equal("nvme-perf-report-not-ready")
expect(nvme_production_perf_serial_acceptance_reason(alloc)).to_equal("nvme-perf-report-not-ready")
```

</details>

#### rejects incomplete or non-ready serial benchmark reports

- rejects incomplete or non-ready serial benchmark reports
   - Expected: nvme_production_perf_serial_acceptance_reason("boot ok") equals `missing-nvme-perf-report`
   - Expected: nvme_production_perf_serial_acceptance_reason("nvme_perf reason=simple-read-iops-not-faster-than-c simple_read_iops=1") equals `nvme-perf-report-not-ready`
   - Expected: nvme_production_perf_serial_acceptance_reason("nvme_perf reason=ready simple_read_iops=1") equals `nvme-perf-provider-not-simple`
   - Expected: nvme_production_perf_serial_acceptance_reason("nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096 simple_read_iops=1") equals `nvme-perf-direct-io-path-not-shared-dma`
   - Expected: nvme_production_perf_serial_acceptance_reason("nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096 direct_io_path=nvme-lease-shared-dma-4k fs_consumers=fat32,nvfs,dbfs c_bridge_used=false") equals `nvme-perf-fat32-direct-io-missing`
   - Expected: nvme_production_perf_serial_acceptance_reason(missing_baseline) equals `nvme-perf-c-baseline-not-same-device`
   - Expected: nvme_production_perf_serial_acceptance_reason(loose_baseline) equals `nvme-perf-c-baseline-not-same-device`
   - Expected: nvme_production_perf_serial_acceptance_reason(loose_scope) equals `nvme-perf-c-baseline-not-in-guest`
   - Expected: nvme_production_perf_serial_acceptance_reason(loose_vfat) equals `nvme-perf-vfat-baseline-not-same-device`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(duplicate_qemu) equals `duplicate-nvme-perf-field:qemu=`
   - Expected: nvme_production_perf_serial_acceptance_reason(duplicate_vfat) equals `duplicate-nvme-perf-field:vfat_baseline_device=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects incomplete or non-ready serial benchmark reports")
expect(nvme_production_perf_serial_acceptance_reason("boot ok")).to_equal("missing-nvme-perf-report")
expect(nvme_production_perf_serial_acceptance_reason("nvme_perf reason=simple-read-iops-not-faster-than-c simple_read_iops=1")).to_equal("nvme-perf-report-not-ready")
expect(nvme_production_perf_serial_acceptance_reason("nvme_perf reason=ready simple_read_iops=1")).to_equal("nvme-perf-provider-not-simple")
expect(nvme_production_perf_serial_acceptance_reason("nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096 simple_read_iops=1")).to_equal("nvme-perf-direct-io-path-not-shared-dma")
expect(nvme_production_perf_serial_acceptance_reason("nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096 direct_io_path=nvme-lease-shared-dma-4k fs_consumers=fat32,nvfs,dbfs c_bridge_used=false")).to_equal("nvme-perf-fat32-direct-io-missing")
val missing_baseline = "nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096 direct_io_path=nvme-lease-shared-dma-4k fs_consumers=fat32,nvfs,dbfs fat32_direct_io=read-write-through nvfs_direct_io=read-write-through dbfs_direct_io=read-write-through fat32_extent_source=freestanding-fat32-extents nvfs_extent_source=freestanding-dbfs-arena dbfs_extent_source=freestanding-dbfs-arena c_bridge_used=false common_logic_shared=true allocation_per_io=false"
expect(nvme_production_perf_serial_acceptance_reason(missing_baseline)).to_equal("nvme-perf-c-baseline-not-same-device")
val loose_baseline = _serial_perf_prefix().replace("c_baseline_device=same-nvme", "c_baseline_device=same-nvme-spoof") + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
val loose_scope = _serial_perf_prefix().replace("c_baseline_scope=in-guest", "c_baseline_scope=in-guest-hosted") + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
val loose_vfat = _serial_perf_prefix().replace("vfat_baseline_device=same-nvme", "vfat_baseline_device=host-cache") + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
expect(nvme_production_perf_serial_acceptance_reason(loose_baseline)).to_equal("nvme-perf-c-baseline-not-same-device")
expect(nvme_production_perf_serial_acceptance_reason(loose_scope)).to_equal("nvme-perf-c-baseline-not-in-guest")
expect(nvme_production_perf_serial_acceptance_reason(loose_vfat)).to_equal("nvme-perf-vfat-baseline-not-same-device")
val duplicate_qemu = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768 hardware_target=real-nvme qemu=false qemu=true device_model=Samsung_PM9A3 device_serial=SN123 namespace_nsid=1 physical_runs=5 measured_on=real-device"
val duplicate_vfat = _serial_perf_prefix() + "vfat_baseline_device=host-cache simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
expect(nvme_real_hardware_perf_serial_acceptance_reason(duplicate_qemu)).to_equal("duplicate-nvme-perf-field:qemu=")
expect(nvme_production_perf_serial_acceptance_reason(duplicate_vfat)).to_equal("duplicate-nvme-perf-field:vfat_baseline_device=")
```

</details>

#### revalidates serial benchmark numbers instead of trusting reason=ready

- revalidates serial benchmark numbers instead of trusting reason=ready
   - Expected: nvme_production_perf_serial_acceptance_reason(slow_iops) equals `simple-read-iops-not-faster-than-c`
   - Expected: nvme_production_perf_serial_acceptance_reason(slow_p99) equals `simple-read-p99-not-faster-than-c`
   - Expected: nvme_production_perf_serial_acceptance_reason(equal_p99) equals `simple-read-p99-not-faster-than-c`
   - Expected: nvme_production_perf_serial_acceptance_reason(cold) equals `nvme-perf-not-warm`
   - Expected: nvme_production_perf_serial_acceptance_reason(invalid) equals `invalid-simple-read-iops`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("revalidates serial benchmark numbers instead of trusting reason=ready")
val slow_iops = _serial_perf_prefix() + "simple_read_iops=100000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
val slow_p99 = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=950 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
val equal_p99 = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=900 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
val cold = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=1 max_rss_kib=32768"
val invalid = _serial_perf_prefix() + "simple_read_iops=fast simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"

expect(nvme_production_perf_serial_acceptance_reason(slow_iops)).to_equal("simple-read-iops-not-faster-than-c")
expect(nvme_production_perf_serial_acceptance_reason(slow_p99)).to_equal("simple-read-p99-not-faster-than-c")
expect(nvme_production_perf_serial_acceptance_reason(equal_p99)).to_equal("simple-read-p99-not-faster-than-c")
expect(nvme_production_perf_serial_acceptance_reason(cold)).to_equal("nvme-perf-not-warm")
expect(nvme_production_perf_serial_acceptance_reason(invalid)).to_equal("invalid-simple-read-iops")
```

</details>

#### parses perf fields from full serial output with later lines

- parses perf fields from full serial output with later lines
   - Expected: nvme_production_perf_serial_acceptance_reason(serial) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses perf fields from full serial output with later lines")
val serial = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768\nTEST PASSED\n"
expect(nvme_production_perf_serial_acceptance_reason(serial)).to_equal("ready")
```

</details>

#### rejects serial logs with multiple NVMe performance reports

- rejects serial logs with multiple NVMe performance reports
   - Expected: nvme_production_perf_serial_acceptance_reason(ready + "\n" + stale + "\nTEST PASSED\n") equals `multiple-nvme-perf-reports`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(ready + " hardware_target=real-nvme qemu=false device_model=Samsung_PM9A3 device_serial=SN123 namespace_nsid=1 physical_runs=5 measured_on=real-device\n" + stale) equals `multiple-nvme-perf-reports`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects serial logs with multiple NVMe performance reports")
val ready = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
val stale = "nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096"
expect(nvme_production_perf_serial_acceptance_reason(ready + "\n" + stale + "\nTEST PASSED\n")).to_equal("multiple-nvme-perf-reports")
expect(nvme_real_hardware_perf_serial_acceptance_reason(ready + " hardware_target=real-nvme qemu=false device_model=Samsung_PM9A3 device_serial=SN123 namespace_nsid=1 physical_runs=5 measured_on=real-device\n" + stale)).to_equal("multiple-nvme-perf-reports")
```

</details>

#### requires physical NVMe identity before accepting real-hardware throughput evidence

- requires physical NVMe identity before accepting real-hardware throughput evidence
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(perf) equals `nvme-real-hardware-target-missing`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(q35) equals `nvme-real-hardware-target-missing`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(spoofed) equals `nvme-real-hardware-emulator-report`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(missing_nsid) equals `nvme-real-hardware-namespace-missing`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(loose_target) equals `nvme-real-hardware-target-missing`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(loose_qemu) equals `nvme-real-hardware-emulator-report`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(loose_measured) equals `nvme-real-hardware-measurement-source-invalid`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(unknown_model) equals `nvme-real-hardware-device-model-invalid`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(missing_runs) equals `nvme-real-hardware-physical-runs-missing`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(low_runs) equals `nvme-real-hardware-physical-runs-too-low`
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(real) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires physical NVMe identity before accepting real-hardware throughput evidence")
val perf = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
val real = perf + " hardware_target=real-nvme qemu=false device_model=Samsung-MZQL2960HCJR device_serial=SIMPLE123 namespace_nsid=1 physical_runs=5 measured_on=real-device"
val q35 = perf + " hardware_target=q35 qemu=true device_model=qemu-nvme device_serial=pure-simple-perf namespace_nsid=1 measured_on=emulator"
val spoofed = perf + " hardware_target=real-nvme qemu=true device_model=qemu-nvme device_serial=pure-simple-perf namespace_nsid=1 measured_on=emulator"
val missing_nsid = perf + " hardware_target=real-nvme qemu=false device_model=Samsung-MZQL2960HCJR device_serial=SIMPLE123 measured_on=real-device"
val loose_target = perf + " hardware_target=real-nvme-emulated qemu=false device_model=Samsung-MZQL2960HCJR device_serial=SIMPLE123 namespace_nsid=1 measured_on=real-device"
val loose_qemu = perf + " hardware_target=real-nvme qemu=false-positive device_model=Samsung-MZQL2960HCJR device_serial=SIMPLE123 namespace_nsid=1 measured_on=real-device"
val loose_measured = perf + " hardware_target=real-nvme qemu=false device_model=Samsung-MZQL2960HCJR device_serial=SIMPLE123 namespace_nsid=1 physical_runs=5 measured_on=real-device-spoof"
val unknown_model = perf + " hardware_target=real-nvme qemu=false device_model=unknown device_serial=SIMPLE123 namespace_nsid=1 physical_runs=5 measured_on=real-device"
val missing_runs = perf + " hardware_target=real-nvme qemu=false device_model=Samsung-MZQL2960HCJR device_serial=SIMPLE123 namespace_nsid=1 measured_on=real-device"
val low_runs = perf + " hardware_target=real-nvme qemu=false device_model=Samsung-MZQL2960HCJR device_serial=SIMPLE123 namespace_nsid=1 physical_runs=1 measured_on=real-device"

expect(nvme_real_hardware_perf_serial_acceptance_reason(perf)).to_equal("nvme-real-hardware-target-missing")
expect(nvme_real_hardware_perf_serial_acceptance_reason(q35)).to_equal("nvme-real-hardware-target-missing")
expect(nvme_real_hardware_perf_serial_acceptance_reason(spoofed)).to_equal("nvme-real-hardware-emulator-report")
expect(nvme_real_hardware_perf_serial_acceptance_reason(missing_nsid)).to_equal("nvme-real-hardware-namespace-missing")
expect(nvme_real_hardware_perf_serial_acceptance_reason(loose_target)).to_equal("nvme-real-hardware-target-missing")
expect(nvme_real_hardware_perf_serial_acceptance_reason(loose_qemu)).to_equal("nvme-real-hardware-emulator-report")
expect(nvme_real_hardware_perf_serial_acceptance_reason(loose_measured)).to_equal("nvme-real-hardware-measurement-source-invalid")
expect(nvme_real_hardware_perf_serial_acceptance_reason(unknown_model)).to_equal("nvme-real-hardware-device-model-invalid")
expect(nvme_real_hardware_perf_serial_acceptance_reason(missing_runs)).to_equal("nvme-real-hardware-physical-runs-missing")
expect(nvme_real_hardware_perf_serial_acceptance_reason(low_runs)).to_equal("nvme-real-hardware-physical-runs-too-low")
expect(nvme_real_hardware_perf_serial_acceptance_reason(real)).to_equal("ready")
```

</details>

#### builds accepted real-hardware report lines with sanitized physical identity

- builds accepted real-hardware report lines with sanitized physical identity
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(line) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds accepted real-hardware report lines with sanitized physical identity")
val line = nvme_real_hardware_perf_report_line_from_measurements(
    120000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    false,
    "Samsung PM9A3",
    "SN 123\t456",
    1u32
)

expect(line).to_contain("hardware_target=real-nvme")
expect(line).to_contain("qemu=false")
expect(line).to_contain("device_model=Samsung_PM9A3")
expect(line).to_contain("device_serial=SN_123_456")
expect(line).to_contain("namespace_nsid=1")
expect(line).to_contain("physical_runs=5")
expect(line).to_contain("measured_on=real-device")
expect(nvme_real_hardware_perf_serial_acceptance_reason(line)).to_equal("ready")
```

</details>

#### keeps real-hardware report builder fail-closed when measured counters are not ready

- keeps real-hardware report builder fail-closed when measured counters are not ready
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(line) equals `nvme-perf-report-not-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps real-hardware report builder fail-closed when measured counters are not ready")
val line = nvme_real_hardware_perf_report_line_from_measurements(
    100000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    false,
    "Samsung PM9A3",
    "SN123456",
    1u32
)

expect(line).to_contain("reason=simple-read-iops-not-faster-than-c")
expect(nvme_real_hardware_perf_serial_acceptance_reason(line)).to_equal("nvme-perf-report-not-ready")
```

</details>

#### rejects real-hardware report builder output with missing physical identity

- rejects real-hardware report builder output with missing physical identity
   - Expected: nvme_real_hardware_perf_serial_acceptance_reason(line) equals `nvme-real-hardware-device-model-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects real-hardware report builder output with missing physical identity")
val line = nvme_real_hardware_perf_report_line_from_measurements(
    120000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    false,
    "",
    "SN123456",
    1u32
)

expect(line).to_contain("device_model=unknown")
expect(nvme_real_hardware_perf_serial_acceptance_reason(line)).to_equal("nvme-real-hardware-device-model-invalid")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NVMe production performance contract.
- NVMe production performance contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c8feeae4e8de17615fce84df0f76d6910bad7dd8a97869c1c2ff1c156d5410fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c8feeae4e8de17615fce84df0f76d6910bad7dd8a97869c1c2ff1c156d5410fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c8feeae4e8de17615fce84df0f76d6910bad7dd8a97869c1c2ff1c156d5410fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl
mirror: doc/06_spec/unit/os/drivers/nvme/nvme_performance_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/nvme/nvme_performance_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/nvme/nvme_performance_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts warmed pure Simple 4K random I/O samples without C bridge or per-I/O allocation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects samples that are not measuring the production 4K random NVMe path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires pure Simple random read and write to beat the C FAT baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
