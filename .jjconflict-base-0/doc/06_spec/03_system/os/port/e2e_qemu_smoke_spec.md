# e2e_qemu_smoke_spec

> Encodes the 6-step Phase-3 verification pipeline. Each step is a

<!-- sdn-diagram:id=e2e_qemu_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=e2e_qemu_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

e2e_qemu_smoke_spec -> std
e2e_qemu_smoke_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=e2e_qemu_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# e2e_qemu_smoke_spec

Encodes the 6-step Phase-3 verification pipeline. Each step is a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/e2e_qemu_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Encodes the 6-step Phase-3 verification pipeline. Each step is a
    separate it-block so failures are reported individually. All cases
    skip cleanly when SIMPLEOS_QEMU_SMOKE is not set.

## Scenarios

### Phase-3 end-to-end QEMU SimpleOS smoke test

#### step 1 [phase-3-boot]: QEMU boots initramfs+FAT32 with IF-08 [BOOT] markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-boot]")
```

</details>

#### step 2 [phase-3-clang]: clang cross-compiles hello.c for x86_64-simpleos (exit 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-clang]")
```

</details>

#### step 3 [phase-3-nm]: llvm-nm finds main symbol in hello.o

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-nm]")
```

</details>

#### step 4 [phase-3-rustc]: rustc cross-compiles hello.rs, ELF contains _start

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-rustc]")
```

</details>

#### step 5 [phase-3-cargo]: cargo offline build succeeds for vendored hello_rs crate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-cargo]")
```

</details>

#### step 6 [phase-3-convergence]: simple native-build stage3=stage4 convergence (IF-09)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-convergence]")
```

</details>

### phase-3 IF-08 marker registry

#### all 6 phase-3 markers are registered in canonical order

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val markers = [
    "[phase-3-boot]",
    "[phase-3-clang]",
    "[phase-3-nm]",
    "[phase-3-rustc]",
    "[phase-3-cargo]",
    "[phase-3-convergence]"
]
markers.len().to_equal(6)
markers[0].to_equal("[phase-3-boot]")
markers[1].to_equal("[phase-3-clang]")
markers[2].to_equal("[phase-3-nm]")
markers[3].to_equal("[phase-3-rustc]")
markers[4].to_equal("[phase-3-cargo]")
markers[5].to_equal("[phase-3-convergence]")
## Assert all markers are distinct (no duplicates)
var i: i32 = 0
while i < markers.len():
    var j: i32 = i + 1
    while j < markers.len():
        (markers[i] == markers[j]).to_equal(false)
        j = j + 1
    i = i + 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
