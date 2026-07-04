# Os Tls Specification

> <details>

<!-- sdn-diagram:id=os_tls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_tls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_tls_spec -> std
os_tls_spec -> os
os_tls_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_tls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Tls Specification

## Scenarios

### TLS 1.3 Unit Tests

#### builds tls_unit_entry.spl into a baremetal kernel

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _tls_unit_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots guest and all TLS 1.3 unit tests pass

1. passed = output contains
2. failed = output contains
3. output len = output len
   - Expected: passed is true
   - Expected: failed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _tls_unit_target()
if not file_exists(target.output):
    expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

var passed = true
var failed = false
var output_len: u64 = 0
val live_enabled = _live_tls_qemu_enabled()

if live_enabled:
    # Host may not have qemu-system-x86_64 — skip the live run but
    # leave the build assertion as the hard gate.
    if not can_run_target(target):
        print "[os_tls_spec] qemu-system-x86_64 not available, skipping live run"
    else:
        # Synchronous run — captures serial output directly.  60 s host wall
        # clock, 30 s guest timeout (passed through shell timeout wrapper).
        val result = run_os_qemu_with_target_via_timeout(target, "30", 60000)
        val output = result[0] + result[1]

        passed = output.contains("[ALL TESTS PASSED]")
        failed = output.contains("[TEST FAIL")
        output_len = output.len()

        if not passed:
            print "[os_tls_spec] [ALL TESTS PASSED] marker not found in serial output"
        if failed:
            print "[os_tls_spec] [TEST FAIL] marker found in serial output"
else:
    print "[os_tls_spec] SIMPLEOS_QEMU_TLS_LIVE not set, skipping live TLS QEMU boot"

if live_enabled:
    print "[os_tls_spec] serial output length: {output_len}"

expect(passed).to_equal(true)
expect(failed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_tls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS 1.3 Unit Tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
