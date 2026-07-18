# NVMe FW RV64 direct build terminates before ELF output

Status: OPEN
Date: 2026-07-07

## Repro

```bash
NVME_RV64_BUILD_TIMEOUT_SECS=120 sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs
```

## Observed

The script creates a tiny generated entry and invokes:

```bash
bin/simple native-build --backend llvm \
  --source build/os/generated \
  --source examples/09_embedded/simpleos_nvme_fw/fw_rv32 \
  --entry build/os/generated/nvme_fw_rv64_direct_entry.spl \
  --entry-closure \
  --target riscv64-unknown-none \
  --emit-object -o build/test-artifacts/nvme_fw_rv64.o
```

The compiler is terminated before `build/nvme_fw_rv64.elf` is produced. Last
observed phase:

```text
phase2:parse:file:start examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_ecc.spl
Terminated
```

## Expected

The build completes and produces `build/nvme_fw_rv64.elf`, allowing
`examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs` to satisfy the RV64
real-boot SSpec.

## Notes

The first implementation generated one large concatenated source file; that was
fixed by importing the existing split `fw_rv32` logic modules directly. The
remaining failure is native-build throughput or external termination, not a fake
boot pass.

## Update — ECC split moves the parse choke point

`logic_ecc.spl` was split into a tiny public self-test wrapper plus
`logic_ecc_core.spl`, preserving `rv32_ecc_selftest()` and the host logic gate:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

The same helper split was applied to `logic_journal.spl`. A 120s RV64 direct
build retry still exits 143 before producing `build/nvme_fw_rv64.elf`, but the
last phase now reaches the smaller journal wrapper:

```text
[BOOTSTRAP-PHASE] ... logic_ecc.spl chars=1153
[BOOTSTRAP-PHASE] ... logic_ecc.spl
[BOOTSTRAP-PHASE] ... logic_journal.spl chars=1773
Terminated
```

So the current blocker is still parse/native-build throughput or external
termination; the fake-QEMU boot wrapper remains fail-closed and must not be
relaxed.

## Update — journal/map/band wrappers now parse quickly

`logic_journal.spl`, `logic_map.spl`, and `logic_band.spl` were split into
small public wrappers plus core/case files. The scalar host logic gate remains
green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through the previously blocking
journal/map/band wrappers and stops at scheduler parsing:

```text
[BOOTSTRAP-PHASE] ... logic_journal.spl chars=240
[BOOTSTRAP-PHASE] ... logic_journal.spl
[BOOTSTRAP-PHASE] ... logic_map.spl chars=84
[BOOTSTRAP-PHASE] ... logic_map.spl
[BOOTSTRAP-PHASE] ... logic_band.spl chars=229
[BOOTSTRAP-PHASE] ... logic_band.spl
[BOOTSTRAP-PHASE] ... logic_sched.spl chars=1342
Terminated
```

The RV64 real-boot proof is still incomplete until the ELF is produced and
`fw_rv64/boot.shs` passes against real QEMU media.

## Update — scheduler wrapper now parses quickly

`logic_sched.spl` was split into a tiny public wrapper plus core/case files. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through scheduler and stops at power
/ thermal parsing:

```text
[BOOTSTRAP-PHASE] ... logic_sched.spl chars=90
[BOOTSTRAP-PHASE] ... logic_sched.spl
[BOOTSTRAP-PHASE] ... logic_power_thermal.spl chars=2069
Terminated
```

The next source-shape choke point is `logic_power_thermal.spl`.

## Update — power/thermal wrapper now parses quickly

`logic_power_thermal.spl` was split into a tiny public wrapper plus core/case
files. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through power/thermal and stops at
HIL parsing:

```text
[BOOTSTRAP-PHASE] ... logic_power_thermal.spl chars=92
[BOOTSTRAP-PHASE] ... logic_power_thermal.spl
[BOOTSTRAP-PHASE] ... logic_hil.spl chars=957
Terminated
```

The next source-shape choke point is `logic_hil.spl`.

## Update — HIL wrapper now parses quickly

`logic_hil.spl` was split into a tiny public wrapper plus core/case files. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through HIL and stops at admin
parsing:

```text
[BOOTSTRAP-PHASE] ... logic_hil.spl chars=84
[BOOTSTRAP-PHASE] ... logic_hil.spl
[BOOTSTRAP-PHASE] ... logic_admin.spl chars=2157
Terminated
```

The next source-shape choke point is `logic_admin.spl`.

## Update — early logic and IO wrappers now parse quickly

`logic.spl`, `logic_rain.spl`, `logic_queue_phase.spl`,
`logic_io_command.spl`, `logic_flush.spl`, and `logic_reactor.spl` were split
into small public wrappers plus section/core/case files. The scalar host logic
gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through reactor and stops at DRAM /
durability parsing:

```text
[BOOTSTRAP-PHASE] ... logic_io_command.spl chars=105
[BOOTSTRAP-PHASE] ... logic_flush.spl chars=90
[BOOTSTRAP-PHASE] ... logic_admin.spl chars=90
[BOOTSTRAP-PHASE] ... logic_reactor.spl chars=96
[BOOTSTRAP-PHASE] ... logic_policy_target.spl chars=3166
[BOOTSTRAP-PHASE] ... logic_dram_durability.spl chars=3594
Terminated
```

The next source-shape choke point is `logic_dram_durability.spl`; the preceding
`logic_policy_target.spl` also remains a large parse-cost file.

## Update — policy and DRAM wrappers now parse quickly

`logic_policy_target.spl` and `logic_dram_durability.spl` were split into tiny
public wrappers plus core/case files. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through policy and DRAM durability
and stops at wear/scrub parsing:

```text
[BOOTSTRAP-PHASE] ... logic_policy_target.spl chars=114
[BOOTSTRAP-PHASE] ... logic_policy_target.spl
[BOOTSTRAP-PHASE] ... logic_dram_durability.spl chars=120
[BOOTSTRAP-PHASE] ... logic_dram_durability.spl
[BOOTSTRAP-PHASE] ... logic_wear_scrub.spl chars=1830
Terminated
```

The next source-shape choke point is `logic_wear_scrub.spl`.

## Update — late public wrappers now parse quickly

`logic_wear_scrub.spl`, `logic_media_retire.spl`, `logic_power_cycle.spl`,
`logic_backpressure_abort.spl`, `logic_feature_guard.spl`,
`logic_namespace_guard.spl`, and `logic_target.spl` were split into tiny public
wrappers plus core/case files. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through every public `logic_*.spl`
wrapper and stops in split case files:

```text
[BOOTSTRAP-PHASE] ... logic_backpressure_abort.spl chars=129
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl chars=114
[BOOTSTRAP-PHASE] ... logic_namespace_guard.spl chars=120
[BOOTSTRAP-PHASE] ... logic_target.spl chars=105
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl chars=1181
Terminated
```

The next source-shape choke point is the split case/core set, starting at
`logic_rain_cases.spl`.

## Update — rain cases and ECC facade now parse quickly

`logic_rain_cases.spl` was split into recovery/address case files, and
`logic_ecc_core.spl` was reduced to a facade over bit, compute, check, and
correction helpers. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through rain cases and ECC core, then
stops at journal count cases:

```text
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl chars=264
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl
[BOOTSTRAP-PHASE] ... logic_ecc_core.spl chars=532
[BOOTSTRAP-PHASE] ... logic_ecc_core.spl
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=682
Terminated
```

The next source-shape choke point is `logic_journal_count_cases.spl`.

## Update — journal count support now parses quickly

`logic_journal_core.spl` was reduced to a public facade, with count helpers and
record/checkpoint helpers split into dedicated support modules. The scalar host
logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through journal count cases and stops
at journal record cases:

```text
[BOOTSTRAP-PHASE] ... logic_ecc_core.spl chars=532
[BOOTSTRAP-PHASE] ... logic_ecc_core.spl
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=682
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=958
Terminated
```

The next source-shape choke point is `logic_journal_record_cases.spl`.

## Update — journal record cases split, probe not yet past ECC

`logic_journal_record_cases.spl` was reduced to a small case facade, with LBA,
sequence, and checkpoint/truncate assertions moved into separate case modules.
The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run did not reach the newly split journal record
case files; the last emitted parse line was back at `logic_ecc_core.spl`:

```text
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl chars=264
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl
[BOOTSTRAP-PHASE] ... logic_ecc_core.spl chars=532
Terminated
```

Keep `logic_journal_record_cases.spl` split, but do not count this probe as
forward RV64 evidence. The next measured blocker remains the RV64 direct build
timeout around the ECC/journal parse boundary.

## Update — ECC self-test and journal count cases now parse quickly

`logic_ecc.spl` was reduced to a small self-test facade, with compute and
check/correct assertions moved into separate case modules. Journal count cases
were also split into effective-count and append/full case modules. The scalar
host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through the ECC case files, journal
count cases, and journal record cases before stopping at map cases:

```text
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl chars=824
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=431
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=1103
Terminated
```

The next source-shape choke point is `logic_map_cases.spl`.

## Update — map cases now parse quickly

`logic_map_cases.spl` was reduced to a small case facade, with validation,
update, and flush/crash assertions moved into separate case modules. The scalar
host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through map cases and band geometry
cases before stopping at band allocation cases:

```text
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
[BOOTSTRAP-PHASE] ... logic_map_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=650
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl chars=1093
Terminated
```

The next source-shape choke point is `logic_band_alloc_cases.spl`.

## Update — band allocation cases now parse quickly

`logic_band_alloc_cases.spl` was reduced to a small case facade, with allocation,
host open/writable, and state/count assertions moved into separate case modules.
The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but it now gets through band allocation cases before
stopping at scheduler cases:

```text
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=650
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl chars=335
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl chars=897
Terminated
```

The next source-shape choke point is `logic_sched_cases.spl`.

## Update — scheduler cases split, probe not past journal

`logic_sched_cases.spl` was reduced to a small case facade, with channel/depth,
step-count, and completion assertions moved into separate case modules. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run did not reach the newly split scheduler case
files; the last emitted parse line was back at journal count cases:

```text
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl chars=824
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=431
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
Terminated
```

Keep `logic_sched_cases.spl` split, but do not count this probe as forward RV64
evidence. The next measured blocker remains around the journal/scheduler parse
timeout boundary.

## Update — DRAM durability cases split, probe still near journal

`logic_dram_durability_cases.spl` was reduced to a small case facade, with DRAM
allocation, stage/usage, and recovery/journal assertions moved into separate
case modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run did not reach the newly split DRAM case
files; it stopped around journal record cases:

```text
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
Terminated
```

Keep the DRAM durability split as total parse-load reduction, but do not count
this probe as forward RV64 evidence.

## Update — policy/target cases split, probe still near ECC/journal

`logic_policy_target_cases.spl` was reduced to a small case facade, with policy
hook/clamp, policy GC, and target geometry assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run did not reach the newly split policy/target
case files; it stopped at ECC check cases:

```text
[BOOTSTRAP-PHASE] ... logic_target.spl
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl chars=264
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl chars=824
Terminated
```

Keep the policy/target split as total parse-load reduction, but do not count
this probe as forward RV64 evidence.

## Update — admin cases split, probe still near ECC

`logic_admin_cases.spl` was reduced to a small case facade, with SMART, log and
feature id, and firmware commit assertions moved into separate case modules.
The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run did not reach the newly split admin case
files; it stopped near ECC compute cases:

```text
[BOOTSTRAP-PHASE] ... logic_admin.spl chars=90
[BOOTSTRAP-PHASE] ... logic_admin.spl
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl chars=824
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=431
Terminated
```

Keep the admin split as total parse-load reduction, but do not count this probe
as forward RV64 evidence.

## Update — reactor cases split, probe reaches map again

`logic_reactor_cases.spl` was reduced to a small case facade, with lock/owner,
foreground/service, and background/power assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through ECC and journal cases again
before stopping at map cases:

```text
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
Terminated
```

The current measured timeout remains around the map/band parse boundary.

## Update — queue phase cases split, probe reaches band geometry

`logic_queue_phase_cases.spl` was reduced to a small case facade, with queue
length, submit validation, and fetch/next assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through map cases and stopped at
band geometry cases:

```text
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
[BOOTSTRAP-PHASE] ... logic_map_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=650
Terminated
```

The current measured timeout is now around `logic_band_geometry_cases.spl`.

## Update — band geometry core split, probe reaches band alloc cases

`logic_band_core.spl` was reduced by moving band geometry helper bodies into
`logic_band_geometry_core.spl`, while preserving the existing `_rv32_band_*`
entrypoint names as wrappers. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through band geometry cases before
stopping at band allocation cases:

```text
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=334
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl chars=335
Terminated
```

The current measured timeout is now around `logic_band_alloc_cases.spl`.

## Update — band geometry cases split, probe back near map

`logic_band_geometry_cases.spl` was reduced to a small case facade, with band
validity, PPN/block address, and count/state assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run stopped at map cases before reaching the
newly split band geometry case files:

```text
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
Terminated
```

Keep the band geometry split as total parse-load reduction, but do not count
this probe as forward RV64 evidence.

## Update — I/O command cases split, probe reaches band allocation

`logic_io_command_cases.spl` was reduced to a small case facade, with valid and
invalid command vectors moved into separate case modules. The scalar host logic
gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through band geometry cases and
stopped at band allocation cases:

```text
[BOOTSTRAP-PHASE] ... logic_map_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=334
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl chars=335
Terminated
```

The current measured timeout is now around `logic_band_alloc_cases.spl`.

## Update — media retire cases split, probe reaches scheduler

`logic_media_retire_cases.spl` was reduced to a small case facade, with
block/spare validation and retire/program result assertions moved into separate
case modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through band allocation cases and
stopped at scheduler cases:

```text
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl chars=335
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl chars=328
Terminated
```

The current measured timeout is now around `logic_sched_cases.spl`.

## Update — scheduler step cases split

`logic_sched_step_cases.spl` was reduced to a small case facade, with balanced
and same-channel scheduling assertions moved into separate case modules. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run stopped earlier in total parse order at
journal count cases:

```text
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl chars=264
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl chars=362
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=276
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update - target logic RV64 probe boots

The full RV64 direct build remains blocked, but `fw_rv64/build.shs` now has a
`target_logic` section that avoids imported-module duplicate `__simple_main`
emission and boots a target profile/aperture probe through OpenSBI.

```text
NVME_RV64_BUILD_SECTION=target_logic NVME_RV64_BUILD_TIMEOUT_SECS=120 \
  sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs
build/nvme_fw_rv64_target_logic.elf: ELF 64-bit LSB executable, UCB RISC-V

NVME_RV64_BOOT_LOG=build/nvme_fw_rv64_target_logic_serial.log \
  sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs \
  build/nvme_fw_rv64_target_logic.elf
RV64 ENTRY
SimpleOS RV64
[BOOT] boot complete
ALL RV64 NVME FW CHECKS PASS
RESULT: PASS
```

The rejected `target` section exposed the compiler-side root cause for imported
case wrappers: every imported module contributes duplicate
`rt_rv64_boot_optional_nvme_fw_selftest` / `__simple_main` symbols during the
RV64 emit-object path. Keep `target_logic` import-free until that backend issue
is fixed.

## Update - compiler source guards non-entry main symbols

The MIR-to-LLVM translator now only maps `main` to `__simple_main` for the
requested native-build entry module (`SIMPLE_NATIVE_BUILD_ENTRY`). Other modules
that happen to define `main` get a module-scoped `__simple_main_<module>` symbol,
removing the duplicate `__simple_main` root cause seen by imported RV64 firmware
closures. Runtime proof against `NVME_RV64_BUILD_SECTION=target` still requires
the self-hosted compiler/bootstrap lane to deploy this source change into
`bin/simple`.

## Update — detached full build still stops without ELF

After the RV64 target-core boot pass, a fresh foreground full build still exited
early:

```text
NVME_RV64_BUILD_FAILED code=143 reason=external-termination-before-timeout timeout=120s elapsed=80s
```

Running the full build through `--background` escaped the foreground command
lifetime and reached `NVME_RV64_BUILD_HEARTBEAT elapsed=60s timeout=300s`, with
native-build reporting `Entry closure files: 177`, but the process still exited
without `build/nvme_fw_rv64.elf` or `build/test-artifacts/nvme_fw_rv64.o`.
`fw_rv64/build.shs --status` now reports this as `NVME_RV64_BUILD_STATUS
stopped` and points at the foreground/background logs instead of flattening it
to a plain missing-media state.

## Update — stopped status now carries last phase

`fw_rv64/build.shs --status` now includes `last_phase=` for stopped background
builds, populated from the latest `[native-build]`, `[BOOTSTRAP-PHASE]`, or
`NVME_RV64_BUILD_FAILED` log line. This makes the next full-closure blocker
visible from the status command without requiring manual log tailing.

## Update — running status also carries last phase

`fw_rv64/build.shs --status` now includes the same `last_phase=` field while a
background build is still running, so long full-closure probes can be monitored
without tailing logs or waiting for a stopped/missing-media state.

Live status evidence from a fresh full-closure background probe:

```text
NVME_RV64_BUILD_STATUS running ... last_phase=[BOOTSTRAP-PHASE] ... logic_queue_phase.spl chars=108
NVME_RV64_BUILD_STATUS stopped ... last_phase=[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=276
```

`--status` also reports `last_heartbeat=` from the detached wrapper log. A
later retry stopped without an ELF at:

```text
last_heartbeat=NVME_RV64_BUILD_HEARTBEAT elapsed=40s timeout=300s
last_phase=[BOOTSTRAP-PHASE] ... logic_power_thermal_cases.spl chars=342
```

`--status` now also includes `last_done=`, so a stopped build can report both
the last fully completed phase and the current/failed phase start. This avoids
guessing whether the final `phase2:parse:file:start` line completed before the
process exited.

The foreground failure summary now scans both `nvme_fw_rv64_build.out` and
`nvme_fw_rv64_build.err` for native-build phase lines. The phase profiler writes
to stderr in current runs, so this keeps direct foreground failures aligned with
the background `--status` telemetry.

## Update — closure diagnostics and fail-closed stub fallback

The RV64 direct build wrapper now runs `native-build` with `--verbose`, records
`closure=compiler-verbose`, and sets `SIMPLE_NO_STUB_FALLBACK=1` with
`stub_fallback=disabled`. Production firmware must not silently accept codegen
stub fallback. The failure path also prints the compiler closure count,
driver-start line, and latest parse phase lines directly before the generic
log tails.

A 60s bounded full-build probe still failed before producing
`build/nvme_fw_rv64.elf`, but reached the compiler closure evidence:

```text
[native-build] Entry closure files: 177
[native-build] Driver start: inputs=177 backend=llvm mode=dynload
[BOOTSTRAP-PHASE] +2759ms phase2:parse:file:start .../logic_sections_primary.spl chars=1441
NVME_RV64_BUILD_FAILED code=124 reason=native-build-timeout timeout=60s elapsed=60s ...
stub_fallback=disabled
```

This narrows the remaining blocker: the direct RV64 firmware build is no longer
an unknown source-root problem; it is compiling a 177-file entry closure and
timing out while parsing that closure with the current self-hosted compiler.

## Update — primary section closure probe

The RV64 direct build wrapper now supports
`NVME_RV64_BUILD_SECTION=all|primary|secondary`. The default remains `all` for
the production firmware path; the section selector is a diagnostic/probe knob
for isolating closure size and future chunked-build work. Invalid section names
fail closed:

```text
NVME_RV64_BUILD_FAILED invalid-section section=nope expected=all,primary,secondary
```

A 60s primary-section probe reduced the entry closure from 177 files to 117
files, but still timed out while parsing:

```text
entry=build/os/generated/nvme_fw_rv64_direct_entry.spl target=riscv64-unknown-none mode=direct_firmware section=primary
stub_fallback=disabled
[BOOTSTRAP-PHASE] +9ms phase1:load_sources:done n_sources=117
[BOOTSTRAP-PHASE] +17647ms phase2:parse:file:start .../logic_journal_count_cases.spl chars=260
NVME_RV64_BUILD_FAILED code=124 reason=native-build-timeout timeout=60s elapsed=60s ...
```

This confirms primary/secondary chunking can reduce closure size, but primary
alone is still too large for the current 60s self-hosted parse budget.

## Update — secondary section closure and probe output isolation

Section probes now write section-specific artifacts such as
`build/nvme_fw_rv64_primary.elf` and `build/nvme_fw_rv64_secondary.elf`.
Only the default `NVME_RV64_BUILD_SECTION=all` path writes
`build/nvme_fw_rv64.elf`, so a partial diagnostic probe cannot accidentally
masquerade as the full production firmware image.

A 90s secondary-section probe reduced the entry closure to 61 files, but the
host still terminated the build before the wrapper timeout:

```text
entry=build/os/generated/nvme_fw_rv64_direct_entry.spl target=riscv64-unknown-none mode=direct_firmware section=secondary
[native-build] Entry closure files: 61
[native-build] Driver start: inputs=61 backend=llvm mode=dynload
[BOOTSTRAP-PHASE] +3ms phase1:load_sources:done n_sources=61
NVME_RV64_BUILD_FAILED code=143 reason=external-termination-before-timeout timeout=90s elapsed=70s ...
```

This confirms that secondary-only is much smaller than the full 177-file
closure, but the current host/compiler path still cannot produce even that
section within the observed 70-second process lifetime.

## Update — target subsystem reaches duplicate-main failure

The RV64 direct build wrapper now supports `NVME_RV64_BUILD_SECTION=target`.
This is a smallest useful secondary subsystem probe: it imports the target
profile self-test and writes `build/nvme_fw_rv64_target.elf` instead of the full
firmware path.

A 90s target-subsystem probe reduced the entry closure to 6 files and got past
parse/lowering/backend driver work, then failed during emit-object relocatable
link:

```text
[native-build] Entry closure files: 6
[native-build] Driver start: inputs=6 backend=llvm mode=dynload
[BOOTSTRAP-PHASE] +1ms phase1:load_sources:done n_sources=6
NVME_RV64_BUILD_FAILED code=1 reason=native-build-duplicate-symbol timeout=90s elapsed=50s ...
error: emit-object relocatable link failed: ld.lld: error: duplicate symbol: rt_rv64_boot_optional_nvme_fw_selftest
```

This is now the smallest known RV64 firmware native-build reproducer. The
remaining production blocker is no longer only parse budget; even a 6-file
firmware closure hits duplicate generated symbols before an ELF can be linked.

## Update — isolated cache and one-binary mode still duplicate main

RV64 direct firmware builds now use a section-specific native cache directory
such as `build/native_cache/nvme_fw_rv64_target`. This prevents stale shared
`build/native_cache` objects from contaminating section probes.

The isolated-cache target probe still fails, but now consistently classifies the
fresh duplicate-main failure:

```text
cache-dir=build/native_cache/nvme_fw_rv64_target
[native-build] Entry closure files: 6
NVME_RV64_BUILD_FAILED code=1 reason=native-build-duplicate-main timeout=90s elapsed=50s ...
error: emit-object relocatable link failed: ld.lld: error: duplicate symbol: __simple_main
```

A direct `--mode one-binary` check against the same 6-file target closure also
failed with duplicate `__simple_main`, so this is not only a dynload-mode issue:

```text
[native-build] Driver start: inputs=6 backend=llvm mode=one-binary
error: emit-object relocatable link failed: ld.lld: error: duplicate symbol: __simple_main
```

## Update — target-core 2-file probe builds but boots silent

The wrapper now supports `NVME_RV64_BUILD_SECTION=target_core`, a 2-file
diagnostic probe that imports only `logic_target_core` and directly checks the
target profile/aperture validators from the generated entry. This bypasses the
duplicate `__simple_main` failure seen in the 6-file `target` closure:

```text
[native-build] Entry closure files: 2
[native-build] Build successful: build/test-artifacts/nvme_fw_rv64_target_core.o
NVME_RV64_NATIVE_BUILD_DONE elapsed=40s
build/nvme_fw_rv64_target_core.elf: ELF 64-bit LSB executable, UCB RISC-V ...
```

The resulting ELF is structurally plausible:

```text
Entry point address: 0x80200000
0000000080200000 T _start
000000008020058e T rt_rv64_boot_optional_nvme_fw_selftest
0000000080211000 B _stack_top
```

Booting it with the old `-bios none` wrapper failed with an empty serial log
because the ELF is linked at `0x80200000` as an OpenSBI S-mode payload:

```text
--- serial ---
--- end ---
RESULT: FAIL (serial empty)
```

The RV64 wrapper now uses QEMU's default OpenSBI firmware. Rebuilding the
`target_core` probe after adding an early `_start` UART marker showed that
OpenSBI reaches the firmware entry. The first generated probe still looped
because the imported helper calls lowered to `jalr a0` without loading the
callee address. The target-core probe now keeps the two constant target checks
inside the exported entry so this boot slice exercises the RV64 firmware
startup path without that imported-call lowering bug.

```text
$ NVME_RV64_BUILD_SECTION=target_core NVME_RV64_BUILD_TIMEOUT_SECS=90 \
  sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs
build/nvme_fw_rv64_target_core.elf: ELF 64-bit LSB executable, UCB RISC-V ...

$ NVME_RV64_BOOT_LOG=build/nvme_fw_rv64_target_core_serial.log \
  sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs build/nvme_fw_rv64_target_core.elf
--- serial ---
RV64 ENTRY
SimpleOS RV64
[BOOT] boot complete
ALL RV64 NVME FW CHECKS PASS
--- end ---
RESULT: PASS
```

So the direct RV64 path can now build and boot a real 1-file target-core
firmware probe. It is still not full production firmware completion because
the full `all` closure image is not built and booted yet.

The wrapper still classifies truly empty serial logs as `serial empty`; after
the OpenSBI fix, the remaining RV64 blocker is the full firmware closure, not
the target-core boot path.

## Update — elapsed evidence shows external termination before 120s cap

`fw_rv64/build.shs` now reports native-build elapsed seconds. A fresh
`NVME_RV64_BUILD_TIMEOUT_SECS=120` probe exited with code 143 after 70 seconds,
before the configured wrapper timeout:

```text
NVME_RV64_BUILD_FAILED code=143 timeout=120s elapsed=70s
[BOOTSTRAP-PHASE] ... logic_sections_primary.spl chars=1441
[BOOTSTRAP-PHASE] ... logic_sections_secondary.spl chars=1464
[BOOTSTRAP-PHASE] ... logic_media_retire.spl chars=111
Terminated
```

Treat this host result as `external-termination-before-timeout`, not proof that
the native build consumed the full 120-second budget. The RV64 ELF is still not
produced; the next production fix should address the external kill or run the
direct build in an environment with a larger process lifetime before resuming
source-shape reductions.

## Update — heartbeat proves host lifetime cap survives visible output

`fw_rv64/build.shs` now emits `NVME_RV64_BUILD_HEARTBEAT` while native-build is
running, so silent-child idle termination is ruled out. A fresh 120-second probe
printed heartbeats through 60 seconds, then still exited 143 at 70 seconds:

```text
NVME_RV64_BUILD_HEARTBEAT elapsed=40s timeout=120s
NVME_RV64_BUILD_HEARTBEAT elapsed=50s timeout=120s
NVME_RV64_BUILD_HEARTBEAT elapsed=60s timeout=120s
NVME_RV64_BUILD_FAILED code=143 reason=external-termination-before-timeout timeout=120s elapsed=70s
```

This host appears to impose a hard process lifetime below the wrapper timeout.
The wrapper now provides live progress and a precise failure reason, but the
RV64 direct ELF still requires running the build outside that 70-second cap or
reducing native-build work enough to complete before it.

## Update — background mode escapes interactive command lifetime

`fw_rv64/build.shs` now supports detached operation for hosts that kill
interactive commands before the configured native-build timeout:

```text
NVME_RV64_BUILD_TIMEOUT_SECS=900 sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs --background
NVME_RV64_BUILD_BACKGROUND pid=152834 out=build/test-artifacts/nvme_fw_rv64_background.out err=build/test-artifacts/nvme_fw_rv64_background.err

sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs --status
NVME_RV64_BUILD_STATUS running pid=152834 out=build/test-artifacts/nvme_fw_rv64_background.out err=build/test-artifacts/nvme_fw_rv64_background.err
```

The detached build emitted heartbeats after the foreground command returned:

```text
NVME_RV64_BUILD_HEARTBEAT elapsed=0s timeout=900s
NVME_RV64_BUILD_HEARTBEAT elapsed=10s timeout=900s
NVME_RV64_BUILD_HEARTBEAT elapsed=20s timeout=900s
```

This is now the canonical path for producing `build/nvme_fw_rv64.elf` on hosts
with a short interactive process lifetime.

## Update — band allocation core split, probe reaches reactor cases

`logic_band_core.spl` was reduced by moving band allocation, host-open, writable
page, and block-state helper bodies into `logic_band_alloc_core.spl`. Geometry
case files now import the narrow geometry/allocation core files directly so
geometry-only checks do not pull the broader band facade.

The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through band geometry, band
allocation, scheduler, power/thermal, HIL, queue phase, I/O command, flush, and
admin cases before stopping at reactor cases:

```text
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl
[BOOTSTRAP-PHASE] ... logic_power_thermal_cases.spl
[BOOTSTRAP-PHASE] ... logic_hil_cases.spl
[BOOTSTRAP-PHASE] ... logic_queue_phase_cases.spl
[BOOTSTRAP-PHASE] ... logic_io_command_cases.spl
[BOOTSTRAP-PHASE] ... logic_flush_cases.spl
[BOOTSTRAP-PHASE] ... logic_admin_cases.spl
[BOOTSTRAP-PHASE] ... logic_reactor_cases.spl chars=328
Terminated
```

The current measured timeout is now around `logic_reactor_cases.spl`.

## Update — reactor core split, probe reaches policy target cases

`logic_reactor_core.spl` was reduced by moving lock, foreground, and background
helper bodies into narrow core files. Reactor case files now import only the
core slice they exercise, while `logic_reactor_core.spl` remains a compatibility
facade for callers that need the original helper names.

The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through reactor cases before
stopping at policy target cases:

```text
[BOOTSTRAP-PHASE] ... logic_reactor_cases.spl chars=328
[BOOTSTRAP-PHASE] ... logic_reactor_cases.spl
[BOOTSTRAP-PHASE] ... logic_policy_target_cases.spl chars=340
Terminated
```

The current measured timeout is now around `logic_policy_target_cases.spl`.

## Update — map flush cases split, probe reaches band geometry

`logic_map_flush_cases.spl` was reduced to a small case facade, with flush L2P
assertions and crash-recovery assertions moved into separate case modules. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through map cases before stopping at
band geometry:

```text
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
[BOOTSTRAP-PHASE] ... logic_map_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=334
Terminated
```

The current measured timeout is now around `logic_band_geometry_cases.spl`.

## Update — journal append cases split, probe reaches map cases

`logic_journal_append_cases.spl` was reduced to a small case facade, with
append-count assertions and full-state assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through journal count and journal
record cases before stopping at map cases:

```text
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
Terminated
```

The current measured timeout is now around `logic_map_cases.spl`.

## Update — map valid cases split

`logic_map_valid_cases.spl` was reduced to a small case facade, with LBA
validation assertions and PPN/sanitize assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run still stopped at map cases:

```text
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update — feature guard value cases split, probe reaches queue phase cases

`logic_feature_guard_value_cases.spl` was reduced to a small case facade, with
queue-depth, temperature, and power-state value assertions moved into separate
case modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through feature guard, namespace,
target, RAIN, ECC, journal, map, band, scheduler, power, and HIL cases before
stopping at queue-phase cases:

```text
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl chars=114
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=276
[BOOTSTRAP-PHASE] ... logic_hil_cases.spl chars=228
[BOOTSTRAP-PHASE] ... logic_queue_phase_cases.spl chars=332
Terminated
```

The current measured timeout is now around `logic_queue_phase_cases.spl`.

## Update — queue fetch cases split

`logic_queue_fetch_cases.spl` was reduced to a small case facade, with fetch
validity checks and next-index wrap checks moved into separate case modules. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run stopped earlier in total parse order at
journal count:

```text
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl chars=114
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=276
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update — flush dirty cases split, probe reaches namespace guard

`logic_flush_dirty_cases.spl` was reduced to a small case facade, with valid
flush dirty-state assertions and dirty clamp assertions moved into separate
case modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through flush, admin, reactor, and
later small logic facades before stopping at namespace guard:

```text
[BOOTSTRAP-PHASE] ... logic_flush.spl chars=90
[BOOTSTRAP-PHASE] ... logic_flush.spl
[BOOTSTRAP-PHASE] ... logic_admin.spl chars=90
[BOOTSTRAP-PHASE] ... logic_reactor.spl chars=96
[BOOTSTRAP-PHASE] ... logic_namespace_guard.spl chars=120
Terminated
```

The current measured timeout is now around `logic_namespace_guard.spl`.

## Update — namespace invalid cases split, probe reaches ECC compute

`logic_namespace_guard_invalid_cases.spl` was reduced to a small case facade,
with namespace/header failures and range/end failures moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through namespace guard, target, and
RAIN cases before stopping at ECC compute cases:

```text
[BOOTSTRAP-PHASE] ... logic_namespace_guard.spl chars=120
[BOOTSTRAP-PHASE] ... logic_namespace_guard.spl
[BOOTSTRAP-PHASE] ... logic_target.spl chars=105
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl chars=264
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=276
Terminated
```

The current measured timeout is now around `logic_ecc_compute_cases.spl`.

## Update — ECC compute payload split, probe reaches I/O command cases

`logic_ecc_compute.spl` was reduced to the compute entrypoint, with Hamming
payload construction moved into `logic_ecc_compute_payload.spl`. The scalar
host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through ECC compute, journal, map,
band, scheduler, power, HIL, and queue-phase cases before stopping at I/O
command cases:

```text
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=276
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_queue_phase_cases.spl chars=332
[BOOTSTRAP-PHASE] ... logic_io_command_cases.spl chars=263
Terminated
```

The current measured timeout is now around `logic_io_command_cases.spl`.

## Update — I/O invalid address cases split

`logic_io_command_invalid_addr_cases.spl` was reduced to a small case facade,
with address/count bounds and invalid payload assertions moved into separate
case modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run stopped earlier in total parse order at
feature guard:

```text
[BOOTSTRAP-PHASE] ... logic_io_command.spl chars=105
[BOOTSTRAP-PHASE] ... logic_io_command.spl
[BOOTSTRAP-PHASE] ... logic_flush.spl chars=90
[BOOTSTRAP-PHASE] ... logic_backpressure_abort.spl chars=129
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl chars=114
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update — namespace guard cases split

`logic_namespace_guard_cases.spl` was reduced to a small case facade, with
valid and invalid namespace command assertions moved into separate case modules.
The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run stopped earlier in total parse order at
flush:

```text
[BOOTSTRAP-PHASE] ... logic_io_command.spl chars=105
[BOOTSTRAP-PHASE] ... logic_io_command.spl
[BOOTSTRAP-PHASE] ... logic_flush.spl chars=90
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update — journal checkpoint cases split, probe reaches namespace guard

`logic_journal_checkpoint_cases.spl` was reduced to a small case facade, with
checkpoint pointer/valid assertions and truncate-count assertions moved into
separate case modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run advanced past the previous journal-count
timeout area and stopped later in total parse order at namespace guard:

```text
[BOOTSTRAP-PHASE] ... logic_journal.spl chars=240
[BOOTSTRAP-PHASE] ... logic_journal.spl
[BOOTSTRAP-PHASE] ... logic_power_cycle.spl chars=108
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl chars=114
[BOOTSTRAP-PHASE] ... logic_namespace_guard.spl chars=120
Terminated
```

The current measured timeout is now around `logic_namespace_guard.spl`.

## Update — target cases split, probe reaches power/thermal

`logic_target_cases.spl` was reduced to a small case facade, with target profile
and target aperture assertions moved into separate case modules. The scalar host
logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through scheduler cases and stopped
at power/thermal cases:

```text
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl chars=328
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl
[BOOTSTRAP-PHASE] ... logic_power_thermal_cases.spl chars=951
Terminated
```

The current measured timeout is now around `logic_power_thermal_cases.spl`.

## Update — power/thermal cases split, probe gets through wrapper

`logic_power_thermal_cases.spl` was reduced to a small case facade, with power
state, temperature, and warning assertions moved into separate case modules. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run got through the small power/thermal wrapper
and later stopped while parsing journal count cases:

```text
[BOOTSTRAP-PHASE] ... logic_power_thermal.spl chars=92
[BOOTSTRAP-PHASE] ... logic_power_thermal.spl
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=431
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
Terminated
```

Keep the power/thermal split as total parse-load reduction and wrapper progress,
but do not count this probe as completion evidence for the RV64 direct ELF.

## Update — backpressure/abort cases split, probe reaches map

`logic_backpressure_abort_cases.spl` was reduced to a small case facade, with
abort record, invalid-status, and accessor assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through journal count and journal
record cases before stopping at map cases:

```text
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl chars=260
[BOOTSTRAP-PHASE] ... logic_journal_count_cases.spl
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
Terminated
```

The current measured timeout is now around `logic_map_cases.spl`.

## Update — feature guard cases split

`logic_feature_guard_cases.spl` was reduced to a small case facade, with feature
ID, value, and default assertions moved into separate case modules. The scalar
host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run got through the small feature guard wrapper
but stopped earlier in the total parse order, at ECC compute cases:

```text
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl chars=114
[BOOTSTRAP-PHASE] ... logic_feature_guard.spl
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl chars=824
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=431
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update — ECC check cases split, probe reaches scheduler

`logic_ecc_check_cases.spl` was reduced to a small case facade, with valid,
injected-error, and correction assertions moved into separate case modules. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through ECC check, ECC compute, map,
and band allocation before stopping at scheduler cases:

```text
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl chars=362
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=276
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=334
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl chars=335
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl chars=328
Terminated
```

The current measured timeout is now around `logic_sched_cases.spl`.

## Update — band state cases split

`logic_band_state_cases.spl` was reduced to a small case facade, with mark,
free, and rebuild-state assertions moved into separate case modules. The scalar
host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run got through band geometry, band allocation,
and scheduler cases before stopping at HIL cases:

```text
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=334
[BOOTSTRAP-PHASE] ... logic_band_alloc_cases.spl chars=335
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl chars=328
[BOOTSTRAP-PHASE] ... logic_power_thermal_cases.spl chars=342
[BOOTSTRAP-PHASE] ... logic_hil_cases.spl chars=228
Terminated
```

Keep this split as total parse-load reduction; the RV64 direct ELF is still not
produced under the 120s cap.

## Update — HIL invalid cases split

`logic_hil_invalid_cases.spl` was reduced to a small case facade, with CID/op
and address/data invalid validation assertions moved into separate case modules.
The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run stopped earlier in total parse order at ECC
check cases:

```text
[BOOTSTRAP-PHASE] ... logic_target.spl chars=105
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl chars=264
[BOOTSTRAP-PHASE] ... logic_rain_cases.spl
[BOOTSTRAP-PHASE] ... logic_ecc_check_cases.spl chars=824
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update — band validation cases split

`logic_band_valid_cases.spl` was reduced to a small case facade, with block and
PPN validation assertions moved into separate case modules. The scalar host
logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run still stopped at the band geometry facade:

```text
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
[BOOTSTRAP-PHASE] ... logic_map_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=334
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update — I/O command invalid cases split

`logic_io_command_invalid_cases.spl` was reduced to a small case facade, with
CID/opcode and address/data invalid command assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run stopped earlier in total parse order at band
geometry cases:

```text
[BOOTSTRAP-PHASE] ... logic_journal_record_cases.spl chars=351
[BOOTSTRAP-PHASE] ... logic_map_cases.spl chars=316
[BOOTSTRAP-PHASE] ... logic_map_cases.spl
[BOOTSTRAP-PHASE] ... logic_band_geometry_cases.spl chars=334
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.

## Update — ECC compute cases split, probe reaches queue phase

`logic_ecc_compute_cases.spl` was reduced to a small case facade, with
determinism/range and input-sensitivity assertions moved into separate case
modules. The scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through ECC compute, map, band, and
scheduler cases before stopping at queue phase cases:

```text
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl chars=276
[BOOTSTRAP-PHASE] ... logic_ecc_compute_cases.spl
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl chars=328
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl
[BOOTSTRAP-PHASE] ... logic_queue_phase_cases.spl chars=332
Terminated
```

The current measured timeout is now around `logic_queue_phase_cases.spl`.

## Update — queue submit cases split

`logic_queue_submit_cases.spl` was reduced to a small case facade, with valid
and invalid submit assertions moved into separate case modules. The scalar host
logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run got through the queue phase path in the
previously targeted area, but stopped earlier in total parse order at HIL cases:

```text
[BOOTSTRAP-PHASE] ... logic_sched_cases.spl chars=328
[BOOTSTRAP-PHASE] ... logic_power_thermal_cases.spl chars=342
[BOOTSTRAP-PHASE] ... logic_power_thermal_cases.spl
[BOOTSTRAP-PHASE] ... logic_hil_cases.spl chars=643
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build completion evidence.

## Update — HIL cases split, probe reaches flush

`logic_hil_cases.spl` was reduced to a small case facade, with valid and invalid
host-interface validation assertions moved into separate case modules. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`, but this run got through HIL, queue phase, and I/O
command cases before stopping at flush cases:

```text
[BOOTSTRAP-PHASE] ... logic_hil_cases.spl chars=228
[BOOTSTRAP-PHASE] ... logic_hil_cases.spl
[BOOTSTRAP-PHASE] ... logic_queue_phase_cases.spl chars=332
[BOOTSTRAP-PHASE] ... logic_io_command_cases.spl chars=263
[BOOTSTRAP-PHASE] ... logic_flush_cases.spl chars=758
Terminated
```

The current measured timeout is now around `logic_flush_cases.spl`.

## Update — flush cases split

`logic_flush_cases.spl` was reduced to a small case facade, with flush command
validation and dirty-state assertions moved into separate case modules. The
scalar host logic gate remains green:

```text
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl --mode=interpreter
All checks passed (1 file(s))

bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
RV32 NVME FW LOGIC OK
```

A 120s RV64 direct build retry still exits 143 before producing
`build/nvme_fw_rv64.elf`. This run stopped earlier in total parse order at I/O
command cases:

```text
[BOOTSTRAP-PHASE] ... logic_hil_cases.spl chars=228
[BOOTSTRAP-PHASE] ... logic_queue_phase_cases.spl chars=332
[BOOTSTRAP-PHASE] ... logic_queue_phase_cases.spl
[BOOTSTRAP-PHASE] ... logic_io_command_cases.spl chars=263
Terminated
```

Keep this split as total parse-load reduction, but do not count this probe as
forward RV64 direct-build evidence.
