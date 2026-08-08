# CH32V307 Direct Hardware Readiness and Workload Probe

> <details>

<!-- sdn-diagram:id=ch32v307_composite_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ch32v307_composite_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ch32v307_composite_runner_spec -> std
ch32v307_composite_runner_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ch32v307_composite_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CH32V307 Direct Hardware Readiness and Workload Probe

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/ch32v307_composite_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#
#

## Scenarios

### CH32V307 Baremetal Direct Hardware

<details>
<summary>Advanced: shares the same baremetal workload fixture as host and stm32h7</summary>

#### shares the same baremetal workload fixture as host and stm32h7 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_workload_available()).to_equal(true)
expect(workload_elf_available()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects CH32V307 through wlink</summary>

#### detects CH32V307 through wlink _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
expect(ch32v307_detected()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: writes and reads back RAM on real CH32V307 hardware</summary>

#### writes and reads back RAM on real CH32V307 hardware _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
expect(ram_write_readback_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: reads registers on real CH32V307 hardware</summary>

#### reads registers on real CH32V307 hardware _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
expect(register_dump_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: attempts the shared collections workload through flashed RV32 ELF</summary>

#### attempts the shared collections workload through flashed RV32 ELF _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
if not workload_elf_available():
    print "[skip] workload ELF unavailable"
    return
val output = workload_flash_output()
if output.contains("Permission denied"):
    print "[skip] WCH-Link serial permission denied for SDI workload output"
else:
    expect(output).to_contain("PASS: FixedArray push/pop order correct")
    expect(output).to_contain("PASS: FixedMap hash/put/get correct")
    expect(output).to_contain("PASS: RingBuffer enqueue/dequeue with wrap-around correct")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
