# fs_exec_fallback_contract_spec

> FS-Exec Fallback Contract — per-arch rejection specs.

<!-- sdn-diagram:id=fs_exec_fallback_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fs_exec_fallback_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fs_exec_fallback_contract_spec -> std
fs_exec_fallback_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fs_exec_fallback_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_exec_fallback_contract_spec

FS-Exec Fallback Contract — per-arch rejection specs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FS-EXEC-MULTIARCH-AC2 |
| Category | OS serial acceptance |
| Status | Active |
| Source | `test/01_unit/os/fs_exec_fallback_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FS-Exec Fallback Contract — per-arch rejection specs.
Verifies that the shared fs_exec_fallback_contract correctly detects
resident-manifest fallback patterns, and that all five architecture lanes
(x86_64, riscv64, riscv32, arm64, arm32) would reject serial output
containing those patterns as completion evidence.

No QEMU needed — pure contract functions on text input.

## Scenarios

### fs_exec_fallback_contract — detection

#### clean serial has no fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_serial_has_fallback(_clean_serial())).to_equal(false)
```

</details>

#### clean serial passes rejects_fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_serial_rejects_fallback(_clean_serial())).to_equal(true)
```

</details>

#### detects resident-fallback:active pattern alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_serial_has_fallback(_fallback_serial_resident_active_only())).to_equal(true)
```

</details>

#### detects launcher fallback=resident-manifest pattern alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_serial_has_fallback(_fallback_serial_launcher_only())).to_equal(true)
```

</details>

#### detects both patterns together

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_serial_has_fallback(_fallback_serial_both_patterns())).to_equal(true)
```

</details>

#### rejects_fallback is false when fallback detected (both patterns)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_serial_rejects_fallback(_fallback_serial_both_patterns())).to_equal(false)
```

</details>

#### rejects_fallback is false for resident-active-only serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_serial_rejects_fallback(_fallback_serial_resident_active_only())).to_equal(false)
```

</details>

#### rejects_fallback is false for launcher-only serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_exec_serial_rejects_fallback(_fallback_serial_launcher_only())).to_equal(false)
```

</details>

#### pattern constants match expected strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FS_EXEC_FALLBACK_PATTERN_RESIDENT_ACTIVE).to_equal("[desktop-e2e] resident-fallback:active")
expect(FS_EXEC_FALLBACK_PATTERN_LAUNCHER).to_equal("[launcher] fallback=resident-manifest")
```

</details>

### fs_exec fallback rejection — x86_64 lane

#### x86_64: resident-fallback:active pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### x86_64: launcher fallback=resident-manifest pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### x86_64: clean serial is accepted (not a fallback)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

### fs_exec fallback rejection — riscv64 lane

#### riscv64: resident-fallback:active pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### riscv64: launcher fallback=resident-manifest pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### riscv64: clean serial is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

### fs_exec fallback rejection — riscv32 lane

#### riscv32: resident-fallback:active pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### riscv32: launcher fallback=resident-manifest pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### riscv32: clean serial is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

### fs_exec fallback rejection — arm64 lane

#### arm64: resident-fallback:active pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### arm64: launcher fallback=resident-manifest pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### arm64: clean serial is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

### fs_exec fallback rejection — arm32 lane

#### arm32: resident-fallback:active pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### arm32: launcher fallback=resident-manifest pattern is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### arm32: clean serial is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
