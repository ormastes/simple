# @manual: primary

> Purpose: Prove that log level constants ordering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that log level constants ordering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/logging/log_device_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that log level constants ordering.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-KERNEL-001
doc/01_research/local/REQ-OS-KERNEL-001.md
doc/03_plan/sys_test/REQ-OS-KERNEL-001.md
doc/04_architecture/REQ-OS-KERNEL-001.md
doc/05_design/REQ-OS-KERNEL-001.md

## Scenarios

### log level constants ordering

#### orders TRACE through OFF

- Verify: orders TRACE through OFF
   - Expected: LOG_TRACE equals `0`
   - Expected: LOG_DEBUG equals `1`
   - Expected: LOG_INFO equals `2`
   - Expected: LOG_WARN equals `3`
   - Expected: LOG_ERROR equals `4`
   - Expected: LOG_FATAL equals `5`
   - Expected: LOG_OFF equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: orders TRACE through OFF")
expect(LOG_TRACE).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(LOG_DEBUG).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(LOG_INFO).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(LOG_WARN).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(LOG_ERROR).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(LOG_FATAL).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(LOG_OFF).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### names each level via log_level_name

- Verify: names each level via log_level_name
   - Expected: log_level_name(LOG_TRACE) equals `TRACE`
   - Expected: log_level_name(LOG_DEBUG) equals `DEBUG`
   - Expected: log_level_name(LOG_INFO) equals `INFO`
   - Expected: log_level_name(LOG_WARN) equals `WARN`
   - Expected: log_level_name(LOG_ERROR) equals `ERROR`
   - Expected: log_level_name(LOG_FATAL) equals `FATAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: names each level via log_level_name")
expect(log_level_name(LOG_TRACE)).to_equal("TRACE")
expect(log_level_name(LOG_DEBUG)).to_equal("DEBUG")
expect(log_level_name(LOG_INFO)).to_equal("INFO")
expect(log_level_name(LOG_WARN)).to_equal("WARN")
expect(log_level_name(LOG_ERROR)).to_equal("ERROR")
expect(log_level_name(LOG_FATAL)).to_equal("FATAL")
```

</details>

### log target bit constants

#### assigns DEVICE=1, SEMIHOST=2, HOST_FILE=4

- Verify: assigns DEVICE=1, SEMIHOST=2, HOST_FILE=4
   - Expected: TARGET_DEVICE equals `1`
   - Expected: TARGET_SEMIHOST equals `2`
   - Expected: TARGET_HOST_FILE equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: assigns DEVICE=1, SEMIHOST=2, HOST_FILE=4")
expect(TARGET_DEVICE).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(TARGET_SEMIHOST).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(TARGET_HOST_FILE).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

### log_kind_from_text translates profile serial-kind to runtime code

#### com1 → LOG_DEV_KIND_COM1 (1)

- Verify: com1 → LOG_DEV_KIND_COM1 (1)
   - Expected: log_kind_from_text("com1") equals `LOG_DEV_KIND_COM1`
   - Expected: log_kind_from_text("com1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: com1 → LOG_DEV_KIND_COM1 (1)")
expect(log_kind_from_text("com1")).to_equal(LOG_DEV_KIND_COM1)
expect(log_kind_from_text("com1")).to_equal(1)
```

</details>

#### pl011 → LOG_DEV_KIND_PL011 (2)

- Verify: pl011 → LOG_DEV_KIND_PL011 (2)
   - Expected: log_kind_from_text("pl011") equals `LOG_DEV_KIND_PL011`
   - Expected: log_kind_from_text("pl011") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: pl011 → LOG_DEV_KIND_PL011 (2)")
expect(log_kind_from_text("pl011")).to_equal(LOG_DEV_KIND_PL011)
expect(log_kind_from_text("pl011")).to_equal(2)
```

</details>

#### ns16550 → LOG_DEV_KIND_NS16550 (3)

- Verify: ns16550 → LOG_DEV_KIND_NS16550 (3)
   - Expected: log_kind_from_text("ns16550") equals `LOG_DEV_KIND_NS16550`
   - Expected: log_kind_from_text("ns16550") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: ns16550 → LOG_DEV_KIND_NS16550 (3)")
expect(log_kind_from_text("ns16550")).to_equal(LOG_DEV_KIND_NS16550)
expect(log_kind_from_text("ns16550")).to_equal(3)
```

</details>

#### unknown text → 0 (sentinel: no device dispatch)

- Verify: unknown text → 0 (sentinel: no device dispatch)
   - Expected: log_kind_from_text("nonsense") equals `0`
   - Expected: log_kind_from_text("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: unknown text → 0 (sentinel: no device dispatch)")
expect(log_kind_from_text("nonsense")).to_equal(0)
expect(log_kind_from_text("")).to_equal(0)
```

</details>

### log_parse_level: SIMPLE_LOG-style level token parsing

#### parses canonical lowercase tokens

- Verify: parses canonical lowercase tokens
   - Expected: log_parse_level("trace") equals `LOG_TRACE`
   - Expected: log_parse_level("debug") equals `LOG_DEBUG`
   - Expected: log_parse_level("info") equals `LOG_INFO`
   - Expected: log_parse_level("warn") equals `LOG_WARN`
   - Expected: log_parse_level("error") equals `LOG_ERROR`
   - Expected: log_parse_level("fatal") equals `LOG_FATAL`
   - Expected: log_parse_level("off") equals `LOG_OFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: parses canonical lowercase tokens")
expect(log_parse_level("trace")).to_equal(LOG_TRACE)
expect(log_parse_level("debug")).to_equal(LOG_DEBUG)
expect(log_parse_level("info")).to_equal(LOG_INFO)
expect(log_parse_level("warn")).to_equal(LOG_WARN)
expect(log_parse_level("error")).to_equal(LOG_ERROR)
expect(log_parse_level("fatal")).to_equal(LOG_FATAL)
expect(log_parse_level("off")).to_equal(LOG_OFF)
```

</details>

#### unknown tokens default to LOG_INFO

- Verify: unknown tokens default to LOG_INFO
   - Expected: log_parse_level("verbose") equals `LOG_INFO`
   - Expected: log_parse_level("") equals `LOG_INFO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: unknown tokens default to LOG_INFO")
expect(log_parse_level("verbose")).to_equal(LOG_INFO)
expect(log_parse_level("")).to_equal(LOG_INFO)
```

</details>

### log_parse_targets: comma-separated target list to bitmask

#### parses single targets

- Verify: parses single targets
   - Expected: log_parse_targets("serial") equals `1`
   - Expected: log_parse_targets("device") equals `1`
   - Expected: log_parse_targets("semihost") equals `2`
   - Expected: log_parse_targets("file") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: parses single targets")
expect(log_parse_targets("serial")).to_equal(1)
expect(log_parse_targets("device")).to_equal(1)
expect(log_parse_targets("semihost")).to_equal(2)
expect(log_parse_targets("file")).to_equal(4)
```

</details>

#### ORs multiple targets

- Verify: ORs multiple targets
   - Expected: log_parse_targets("serial,semihost") equals `3`
   - Expected: log_parse_targets("serial,semihost,file") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: ORs multiple targets")
expect(log_parse_targets("serial,semihost")).to_equal(3)
expect(log_parse_targets("serial,semihost,file")).to_equal(7)
```

</details>

#### empty string → 0 (no targets)

- Verify: empty string → 0 (no targets)
   - Expected: log_parse_targets("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: empty string → 0 (no targets)")
expect(log_parse_targets("")).to_equal(0)
```

</details>

### platform target exposes serial config per arch

#### x86_64 platform → com1 @ 0x3F8

- Verify: x86_64 platform → com1 @ 0x3F8
   - Expected: platform.qemu_serial_kind equals `com1`
   - Expected: platform.qemu_serial_base equals `0x3F8u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: x86_64 platform → com1 @ 0x3F8")
if val platform = simpleos_platform_target_by_name("x86_64"):
    expect(platform.qemu_serial_kind).to_equal("com1")
    expect(platform.qemu_serial_base).to_equal(0x3F8u64)
```

</details>

#### arm64 platform → pl011 @ 0x09000000

- Verify: arm64 platform → pl011 @ 0x09000000
   - Expected: platform.qemu_serial_kind equals `pl011`
   - Expected: platform.qemu_serial_base equals `0x09000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: arm64 platform → pl011 @ 0x09000000")
if val platform = simpleos_platform_target_by_name("arm64"):
    expect(platform.qemu_serial_kind).to_equal("pl011")
    expect(platform.qemu_serial_base).to_equal(0x09000000u64)
```

</details>

#### riscv64 platform → ns16550 @ 0x10000000

- Verify: riscv64 platform → ns16550 @ 0x10000000
   - Expected: platform.qemu_serial_kind equals `ns16550`
   - Expected: platform.qemu_serial_base equals `0x10000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: riscv64 platform → ns16550 @ 0x10000000")
if val platform = simpleos_platform_target_by_name("riscv64"):
    expect(platform.qemu_serial_kind).to_equal("ns16550")
    expect(platform.qemu_serial_base).to_equal(0x10000000u64)
```

</details>

### MachineProfile mirrors the platform's serial config

#### riscv64 MachineProfile carries ns16550 @ 0x10000000

- Verify: riscv64 MachineProfile carries ns16550 @ 0x10000000
   - Expected: profile.qemu_serial_kind equals `ns16550`
   - Expected: profile.qemu_serial_base equals `0x10000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: riscv64 MachineProfile carries ns16550 @ 0x10000000")
val profile = riscv64_machine_profile()
expect(profile.qemu_serial_kind).to_equal("ns16550")
expect(profile.qemu_serial_base).to_equal(0x10000000u64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-KERNEL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `018d84d1490fc606a3f21fc1a1b6df3957b850179181bbfd0c2b84830ef611dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `018d84d1490fc606a3f21fc1a1b6df3957b850179181bbfd0c2b84830ef611dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `018d84d1490fc606a3f21fc1a1b6df3957b850179181bbfd0c2b84830ef611dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/kernel/logging/log_device_target_spec.spl
mirror: doc/06_spec/unit/os/kernel/logging/log_device_target_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/os/kernel/logging/log_device_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/logging/log_device_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/logging/log_device_target_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/logging/log_device_target_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/os/kernel/logging/log_device_target_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders TRACE through OFF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/logging/log_device_target_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names each level via log_level_name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/logging/log_device_target_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns DEVICE=1, SEMIHOST=2, HOST_FILE=4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
