# T32 Gdb Adapter Specification

> Tests covering T32GdbAdapter config factories, T32GdbAdapter capabilities, T32GdbAdapter name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Gdb Adapter Specification

## Scenarios

### T32GdbAdapter config factories

#### t32-gdb config for T32 target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- t32-gdb config for T32 target
   - Expected: cfg.adapter_type equals `t32-gdb`
   - Expected: cfg.port equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32-gdb config for T32 target")
val cfg = AdapterConfig.for_t32_target("test.elf")
expect(cfg.adapter_type).to_equal("t32-gdb")
expect(cfg.port).to_equal(20000)
```

</details>

#### t32-gdb bridge config

- t32-gdb bridge config
   - Expected: cfg.adapter_type equals `t32-gdb`
   - Expected: cfg.port equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32-gdb bridge config")
val cfg = AdapterConfig.t32_gdb_bridge("localhost", 20000, 2331, "test.elf")
expect(cfg.adapter_type).to_equal("t32-gdb")
expect(cfg.port).to_equal(20000)
```

</details>

#### t32-gdb config has arm architecture

- t32-gdb config has arm architecture
   - Expected: cfg.architecture equals `arm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32-gdb config has arm architecture")
val cfg = AdapterConfig.for_t32_target("test.elf")
expect(cfg.architecture).to_equal("arm")
```

</details>

#### t32-gdb config has correct host

- t32-gdb config has correct host
   - Expected: cfg.host equals `myhost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32-gdb config has correct host")
val cfg = AdapterConfig.t32_gdb_bridge("myhost", 20000, 2331, "test.elf")
expect(cfg.host).to_equal("myhost")
```

</details>

### T32GdbAdapter capabilities

#### has reset capability

- has reset capability
   - Expected: caps.can_reset is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has reset capability")
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.can_reset).to_equal(true)
```

</details>

#### has memory capability

- has memory capability
   - Expected: caps.supports_memory is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has memory capability")
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.supports_memory).to_equal(true)
```

</details>

#### has registers capability

- has registers capability
   - Expected: caps.supports_registers is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has registers capability")
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.supports_registers).to_equal(true)
```

</details>

### T32GdbAdapter name

#### adapter name is t32-gdb

- adapter name is t32-gdb
   - Expected: name equals `t32-gdb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adapter name is t32-gdb")
val name = "t32-gdb"
expect(name).to_equal("t32-gdb")
```

</details>

#### adapter supports trace capture

- adapter supports trace capture
   - Expected: supported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adapter supports trace capture")
val supported = true
expect(supported).to_equal(true)
```

</details>

#### adapter supports coverage collect

- adapter supports coverage collect
   - Expected: supported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adapter supports coverage collect")
val supported = true
expect(supported).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/t32_gdb_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32GdbAdapter config factories, T32GdbAdapter capabilities, T32GdbAdapter name.
- T32GdbAdapter config factories
- T32GdbAdapter capabilities
- T32GdbAdapter name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7eaa2fe287305f98bf16b884397c2ce8452265223df0848ee968203369ee0bac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7eaa2fe287305f98bf16b884397c2ce8452265223df0848ee968203369ee0bac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7eaa2fe287305f98bf16b884397c2ce8452265223df0848ee968203369ee0bac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/debug/remote/t32_gdb_adapter_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/t32_gdb_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/t32_gdb_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/t32_gdb_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/t32_gdb_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/t32_gdb_adapter_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 't32-gdb config for T32 target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/t32_gdb_adapter_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 't32-gdb bridge config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/t32_gdb_adapter_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 't32-gdb config has arm architecture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
