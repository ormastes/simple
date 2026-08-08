# test_classification_system_routing_spec

> @cover src/lib/nogc_sync_mut/test_runner/test_classification.spl 80%

<!-- sdn-diagram:id=test_classification_system_routing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_classification_system_routing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_classification_system_routing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_classification_system_routing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_classification_system_routing_spec

@cover src/lib/nogc_sync_mut/test_runner/test_classification.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/test_classification_system_routing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_sync_mut/test_runner/test_classification.spl 80%

Test Classification — System Path Routing Specification

Verifies that separate_qemu_tests() correctly routes test/system/*qemu*
and test/system/*baremetal* paths into the QEMU bucket, not just paths
containing /qemu/ or /baremetal/ directory segments.

Also verifies classify_test() parses @session: and @arch: markers from
system spec files.

## Scenarios

### separate_qemu_tests

### existing /qemu/ and /baremetal/ path routing

#### AC-3: routes test/system/qemu/ paths to qemu bucket

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "test/system/qemu/os/boot_test.spl",
    "test/unit/lib/math_spec.spl"
]
val result = separate_qemu_tests(files)
val normal = result[0]
val qemu = result[1]
expect(qemu.len()).to_equal(1)
expect(qemu).to_contain("test/system/qemu/os/boot_test.spl")
expect(normal.len()).to_equal(1)
expect(normal).to_contain("test/unit/lib/math_spec.spl")
```

</details>

#### AC-3: routes test/baremetal/ paths to qemu bucket

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "test/baremetal/rv32_test.spl",
    "test/unit/lib/text_spec.spl"
]
val result = separate_qemu_tests(files)
val qemu = result[1]
expect(qemu.len()).to_equal(1)
expect(qemu).to_contain("test/baremetal/rv32_test.spl")
```

</details>

### system path routing (new — must fail until fix applied)

#### AC-3: routes test/system/*_in_qemu_spec.spl to qemu bucket

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "test/system/browser_in_qemu_spec.spl",
    "test/system/engine2d_in_qemu_spec.spl",
    "test/unit/lib/json_spec.spl"
]
val result = separate_qemu_tests(files)
val normal = result[0]
val qemu = result[1]
expect(qemu.len()).to_equal(2)
expect(qemu).to_contain("test/system/browser_in_qemu_spec.spl")
expect(qemu).to_contain("test/system/engine2d_in_qemu_spec.spl")
expect(normal.len()).to_equal(1)
```

</details>

#### AC-3: routes test/system/*baremetal* to qemu bucket

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "test/system/baremetal_test_runner_spec.spl",
    "test/system/replay_baremetal_core_spec.spl",
    "test/system/remote_baremetal_lane_status_spec.spl"
]
val result = separate_qemu_tests(files)
val qemu = result[1]
expect(qemu.len()).to_equal(3)
expect(qemu).to_contain("test/system/baremetal_test_runner_spec.spl")
expect(qemu).to_contain("test/system/replay_baremetal_core_spec.spl")
expect(qemu).to_contain("test/system/remote_baremetal_lane_status_spec.spl")
```

</details>

#### AC-3: routes test/system/replay_qemu* to qemu bucket

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "test/system/replay_qemu_arch_spec.spl",
    "test/system/replay_qemu_e2e_spec.spl",
    "test/unit/lib/crypto_spec.spl"
]
val result = separate_qemu_tests(files)
val qemu = result[1]
expect(qemu.len()).to_equal(2)
expect(qemu).to_contain("test/system/replay_qemu_arch_spec.spl")
expect(qemu).to_contain("test/system/replay_qemu_e2e_spec.spl")
```

</details>

#### AC-3: does not route non-qemu system specs to qemu bucket

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "test/system/some_normal_system_spec.spl",
    "test/unit/lib/text_spec.spl"
]
val result = separate_qemu_tests(files)
val normal = result[0]
val qemu = result[1]
expect(qemu.len()).to_equal(0)
expect(normal.len()).to_equal(2)
```

</details>

#### AC-3: mixed bucket — normal, /qemu/, and test/system/*qemu* all routed

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "test/unit/lib/math_spec.spl",
    "test/system/qemu/os/boot_test.spl",
    "test/system/browser_in_qemu_spec.spl",
    "test/system/ssh_live_login_in_qemu_spec.spl",
    "test/system/simpleos_tls_baremetal_gate_spec.spl"
]
val result = separate_qemu_tests(files)
val normal = result[0]
val qemu = result[1]
expect(normal.len()).to_equal(1)
expect(qemu.len()).to_equal(4)
expect(qemu).to_contain("test/system/qemu/os/boot_test.spl")
expect(qemu).to_contain("test/system/browser_in_qemu_spec.spl")
expect(qemu).to_contain("test/system/ssh_live_login_in_qemu_spec.spl")
expect(qemu).to_contain("test/system/simpleos_tls_baremetal_gate_spec.spl")
```

</details>

### classify_test marker parsing

### session and arch markers

#### AC-3: classifies /qemu/ path as needs_qemu with default mutating mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = classify_test("test/system/qemu/os/boot_test.spl")
expect(tc.needs_qemu).to_equal(true)
expect(tc.session_mode).to_equal(SESSION_MUTATING)
```

</details>

#### AC-3: classifies non-qemu path as not needing qemu

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tc = classify_test("test/unit/lib/math_spec.spl")
expect(tc.needs_qemu).to_equal(false)
expect(tc.session_mode).to_equal(SESSION_NOT_QEMU)
expect(tc.arch).to_equal("host")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
