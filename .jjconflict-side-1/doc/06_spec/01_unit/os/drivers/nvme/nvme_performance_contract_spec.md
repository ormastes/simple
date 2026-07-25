# Nvme Performance Contract Specification

> <details>

<!-- sdn-diagram:id=nvme_performance_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_performance_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_performance_contract_spec -> std
nvme_performance_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_performance_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Performance Contract Specification

## Scenarios

### NVMe production performance contract

#### accepts warmed pure Simple 4K random I/O samples without C bridge or per-I/O allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = _simple_sample(120000u64, 80000u64, 900u64, 1300u64)
expect(nvme_random_io_perf_sample_reason(sample)).to_equal("ready")
expect(nvme_random_io_perf_sample_ready(sample)).to_equal(true)
```

</details>

#### rejects samples that are not measuring the production 4K random NVMe path

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  simple sample
2.  c sample
3.  simple sample
4.  c sample
5.  simple sample
6.  c sample
7.  simple sample
8.  c sample
9.  simple sample
10.  c sample
   - Expected: nvme_c_parity_perf_ready(ready) is true
   - Expected: nvme_c_parity_perf_reason(slow_read) equals `simple-read-iops-not-faster-than-c`
   - Expected: nvme_c_parity_perf_reason(slow_write_p99) equals `simple-write-p99-not-faster-than-c`
   - Expected: nvme_c_parity_perf_reason(equal_read_p99) equals `simple-read-p99-not-faster-than-c`
   - Expected: nvme_c_parity_perf_reason(equal_write_p99) equals `simple-write-p99-not-faster-than-c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  simple sample
2.  c sample
   - Expected: nvme_production_perf_report_ready(report) is true
   - Expected: nvme_production_perf_serial_acceptance_reason(line) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768\nTEST PASSED\n"
expect(nvme_production_perf_serial_acceptance_reason(serial)).to_equal("ready")
```

</details>

#### rejects serial logs with multiple NVMe performance reports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = _serial_perf_prefix() + "simple_read_iops=120000 simple_write_iops=90000 simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 queue_depth=64 warm_runs=5 max_rss_kib=32768"
val stale = "nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096"
expect(nvme_production_perf_serial_acceptance_reason(ready + "\n" + stale + "\nTEST PASSED\n")).to_equal("multiple-nvme-perf-reports")
expect(nvme_real_hardware_perf_serial_acceptance_reason(ready + " hardware_target=real-nvme qemu=false device_model=Samsung_PM9A3 device_serial=SN123 namespace_nsid=1 physical_runs=5 measured_on=real-device\n" + stale)).to_equal("multiple-nvme-perf-reports")
```

</details>

#### requires physical NVMe identity before accepting real-hardware throughput evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/drivers/nvme/nvme_performance_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
