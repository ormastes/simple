# simpleos_platform_catalog_spec

> Regression spec for P1 bug: interp_simpleos_lane_contract_crash_2026-06-13.

<!-- sdn-diagram:id=simpleos_platform_catalog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_platform_catalog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_platform_catalog_spec -> std
simpleos_platform_catalog_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_platform_catalog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_platform_catalog_spec

Regression spec for P1 bug: interp_simpleos_lane_contract_crash_2026-06-13.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/simpleos_platform_catalog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Regression spec for P1 bug: interp_simpleos_lane_contract_crash_2026-06-13.

Verifies that catalog accessors work in interpreter mode without
'on Option' error or SIGSEGV after the index-based workaround.

## Scenarios

### simpleos platform catalog — target_by_name

#### returns non-nil for riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = simpleos_platform_target_names()
var found = false
for n in names:
    if n == "riscv64gc-simpleos":
        found = true
expect(found).to_equal(true)
```

</details>

#### target_names has 6 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = simpleos_platform_target_names()
expect(names.len()).to_equal(6)
```

</details>

### simpleos platform catalog — qemu_smoke_lane (P1 regression)

#### riscv64 smoke lane name is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = simpleos_platform_qemu_smoke_lane("riscv64")
expect(lane.name != "").to_equal(true)
```

</details>

#### riscv64 smoke lane name is riscv64-smoke

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = simpleos_platform_qemu_smoke_lane("riscv64")
expect(lane.name).to_equal("riscv64-smoke")
```

</details>

#### x86_64 smoke lane name is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = simpleos_platform_qemu_smoke_lane("x86_64")
expect(lane.name != "").to_equal(true)
```

</details>

### simpleos platform catalog — qemu_acceptance_lane

#### riscv64 acceptance lane name is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = simpleos_platform_qemu_acceptance_lane("riscv64")
expect(lane.name != "").to_equal(true)
```

</details>

#### arm64 acceptance lane name is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = simpleos_platform_qemu_acceptance_lane("arm64")
expect(lane.name != "").to_equal(true)
```

</details>

### simpleos platform catalog — qemu_lane named lookup

#### riscv64-virtio-fat32-smf lane found for riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = simpleos_platform_has_qemu_lane("riscv64", "riscv64-virtio-fat32-smf")
expect(found).to_equal(true)
```

</details>

#### unknown-lane not found for riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = simpleos_platform_has_qemu_lane("riscv64", "no-such-lane")
expect(found).to_equal(false)
```

</details>

#### riscv64-hosted lane found for riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = simpleos_platform_has_qemu_lane("riscv64", "riscv64-hosted")
expect(found).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
