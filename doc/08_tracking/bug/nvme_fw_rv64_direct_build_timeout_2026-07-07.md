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
