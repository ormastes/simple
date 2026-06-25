# Compressed Logging E2E

> Tests the full compressed logging pipeline from QEMU semihost output to decoded text. Verifies the SYS_WRITEC-based binary protocol (v3) for bandwidth-efficient logging on resource-constrained bare-metal targets.

<!-- sdn-diagram:id=compressed_logging_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compressed_logging_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compressed_logging_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compressed_logging_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compressed Logging E2E

Tests the full compressed logging pipeline from QEMU semihost output to decoded text. Verifies the SYS_WRITEC-based binary protocol (v3) for bandwidth-efficient logging on resource-constrained bare-metal targets.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/compressed_logging_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the full compressed logging pipeline from QEMU semihost output to decoded
text. Verifies the SYS_WRITEC-based binary protocol (v3) for bandwidth-efficient
logging on resource-constrained bare-metal targets.

## Scenarios

### Compressed Logging v3 (SYS_WRITEC)

<details>
<summary>Advanced: QEMU produces binary protocol output</summary>

#### QEMU produces binary protocol output _(slow)_

1. run qemu to file
   - Expected: file_exists(OUTPUT_FILE) is true
   - Expected: bytes[0] as i64 equals `171`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    expect(file_exists(OUTPUT_FILE)).to_equal(true)
    val bytes = read_file_bytes(OUTPUT_FILE)
    expect(bytes[0] as i64).to_equal(171)
    expect(bytes.len()).to_be_greater_than(20)
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: binary output contains valid frame structure</summary>

#### binary output contains valid frame structure _(slow)_

1. run qemu to file
   - Expected: bytes[0] as i64 equals `171`
   - Expected: bytes.len() equals `28`
   - Expected: bytes[1] as i64 equals `1`
   - Expected: bytes[14] as i64 equals `171`
   - Expected: bytes[15] as i64 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    val bytes = read_file_bytes(OUTPUT_FILE)
    expect(bytes[0] as i64).to_equal(171)
    expect(bytes.len()).to_equal(28)
    expect(bytes[1] as i64).to_equal(1)
    expect(bytes[14] as i64).to_equal(171)
    expect(bytes[15] as i64).to_equal(1)
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: decoder resolves handles to Hello message</summary>

#### decoder resolves handles to Hello message _(slow)_

1. run qemu to file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    val decoded = decode_binary_output(OUTPUT_FILE, SMT_FILE)
    expect(decoded).to_contain("Hello, RISC-V 32!")
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: decoder resolves all messages</summary>

#### decoder resolves all messages _(slow)_

1. run qemu to file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    val decoded = decode_binary_output(OUTPUT_FILE, SMT_FILE)
    expect(decoded).to_contain("Hello, RISC-V 32!")
    expect(decoded).to_contain("SEMIHOST TEST")
    expect(decoded).to_contain("Success")
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: compressed binary data is smaller than text strings</summary>

#### compressed binary data is smaller than text strings _(slow)_

1. run qemu to file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    val bytes = read_file_bytes(OUTPUT_FILE)
    expect(bytes.len()).to_be_less_than(50)
else:
    print "SKIP: QEMU or V3 ELF not available"
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
