# Rv64 Http Storage Probe Specification

> 1. print rt file read text

<!-- sdn-diagram:id=rv64_http_storage_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_http_storage_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_http_storage_probe_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_http_storage_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Http Storage Probe Specification

## Scenarios

### RV64 HTTP storage probe

#### prints process output

1. print rt file read text
   - Expected: exit_code equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, exit_code) = rt_process_run_timeout(
    "sh",
    ["scripts/qemu/qemu_rv64_http_test.shs", "--expect-http-only", "--with-storage"],
    90000,
)
print "EXIT={exit_code}"
print "STDOUT_START"
print stdout
print "STDOUT_END"
print "STDERR_START"
print stderr
print "STDERR_END"
print "SERIAL_START"
print rt_file_read_text("build/qemu-rv64-serial.log")
print "SERIAL_END"
expect(exit_code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `target/rv64_http_storage_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV64 HTTP storage probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
