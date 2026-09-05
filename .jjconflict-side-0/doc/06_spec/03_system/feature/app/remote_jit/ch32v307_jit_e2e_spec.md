# CH32V307 Direct Hardware E2E

> <details>

<!-- sdn-diagram:id=ch32v307_jit_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ch32v307_jit_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ch32v307_jit_e2e_spec -> std
ch32v307_jit_e2e_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ch32v307_jit_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CH32V307 Direct Hardware E2E

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/remote_jit/ch32v307_jit_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#
#
#

## Scenarios

### CH32V307 Direct Hardware E2E

<details>
<summary>Advanced: discovers WCH-Link tools</summary>

#### discovers WCH-Link tools _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink not installed"
else:
    val version = shell("wlink --version 2>&1")
    expect(version.exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: reuses the shared baremetal workload fixture</summary>

#### reuses the shared baremetal workload fixture _(slow)_

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
<summary>Advanced: detects CH32V307 through WCH-Link</summary>

#### detects CH32V307 through WCH-Link _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink not installed"
else if not ch32v307_detected():
    print "[skip] WCH-Link probe not detected through wlink status"
else:
    expect(ch32v307_detected()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: writes and reads back RAM through WCH-Link</summary>

#### writes and reads back RAM through WCH-Link _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink not installed"
else if not ch32v307_detected():
    print "[skip] WCH-Link probe not detected through wlink status"
else:
    expect(ram_write_readback_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: reads registers through WCH-Link</summary>

#### reads registers through WCH-Link _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink not installed"
else if not ch32v307_detected():
    print "[skip] WCH-Link probe not detected through wlink status"
else:
    expect(register_dump_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: attempts the shared collections workload through flashed RV32 ELF</summary>

#### attempts the shared collections workload through flashed RV32 ELF _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink not installed"
else if not ch32v307_detected():
    print "[skip] WCH-Link probe not detected through wlink status"
else if not workload_elf_available():
    print "[skip] workload ELF unavailable"
else:
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
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
