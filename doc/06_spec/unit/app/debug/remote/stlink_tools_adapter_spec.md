# Stlink Tools Adapter Specification

> Tests covering StLinkToolsAdapter config factories, StLinkToolsAdapter capabilities, StLinkToolsAdapter name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stlink Tools Adapter Specification

## Scenarios

### StLinkToolsAdapter config factories

#### stlink-tools config for STM32H7

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stlink-tools config for STM32H7
   - Expected: cfg.adapter_type equals `stlink-tools`
   - Expected: cfg.architecture equals `002600213137510833333639`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stlink-tools config for STM32H7")
val cfg = AdapterConfig.stlink_tools("002600213137510833333639", "test.bin")
expect(cfg.adapter_type).to_equal("stlink-tools")
expect(cfg.architecture).to_equal("002600213137510833333639")
```

</details>

#### stlink-tools config for STM32WB

- stlink-tools config for STM32WB
   - Expected: cfg.architecture equals `0671FF555755846687041216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stlink-tools config for STM32WB")
val cfg = AdapterConfig.stlink_tools("0671FF555755846687041216", "test.bin")
expect(cfg.architecture).to_equal("0671FF555755846687041216")
```

</details>

#### stlink-tools config has no host

- stlink-tools config has no host
   - Expected: cfg.host equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stlink-tools config has no host")
val cfg = AdapterConfig.stlink_tools("serial", "test.bin")
expect(cfg.host).to_equal("")
```

</details>

#### stlink-tools config has port 0

- stlink-tools config has port 0
   - Expected: cfg.port equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stlink-tools config has port 0")
val cfg = AdapterConfig.stlink_tools("serial", "test.bin")
expect(cfg.port).to_equal(0)
```

</details>

### StLinkToolsAdapter capabilities

#### has reset capability

- has reset capability
   - Expected: adapter.can_reset() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has reset capability")
val adapter = MockStLinkAdapter.create()
expect(adapter.can_reset()).to_equal(true)
```

</details>

#### has memory capability

- has memory capability
   - Expected: adapter.can_read_memory() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has memory capability")
val adapter = MockStLinkAdapter.create()
expect(adapter.can_read_memory()).to_equal(true)
```

</details>

#### does NOT have halt capability

- does NOT have halt capability
   - Expected: adapter.can_halt() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT have halt capability")
val adapter = MockStLinkAdapter.create()
expect(adapter.can_halt()).to_equal(false)
```

</details>

#### does NOT have step capability

- does NOT have step capability
   - Expected: adapter.can_step() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT have step capability")
val adapter = MockStLinkAdapter.create()
expect(adapter.can_step()).to_equal(false)
```

</details>

#### does NOT have breakpoint capability

- does NOT have breakpoint capability
   - Expected: adapter.can_set_breakpoint() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT have breakpoint capability")
val adapter = MockStLinkAdapter.create()
expect(adapter.can_set_breakpoint()).to_equal(false)
```

</details>

#### does NOT have register capability

- does NOT have register capability
   - Expected: adapter.can_read_registers() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT have register capability")
val adapter = MockStLinkAdapter.create()
expect(adapter.can_read_registers()).to_equal(false)
```

</details>

### StLinkToolsAdapter name

#### adapter name is stlink-tools

- adapter name is stlink-tools
   - Expected: adapter.name() equals `stlink-tools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adapter name is stlink-tools")
val adapter = MockStLinkAdapter.create()
expect(adapter.name()).to_equal("stlink-tools")
```

</details>

#### adapter is attached after creation

- adapter is attached after creation
   - Expected: adapter.is_attached() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adapter is attached after creation")
val adapter = MockStLinkAdapter.create()
expect(adapter.is_attached()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/stlink_tools_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StLinkToolsAdapter config factories, StLinkToolsAdapter capabilities, StLinkToolsAdapter name.
- StLinkToolsAdapter config factories
- StLinkToolsAdapter capabilities
- StLinkToolsAdapter name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `3569d16e3a0251619d201487a513f047cd4fb99367e479dbfb288641b99e5c7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3569d16e3a0251619d201487a513f047cd4fb99367e479dbfb288641b99e5c7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3569d16e3a0251619d201487a513f047cd4fb99367e479dbfb288641b99e5c7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/debug/remote/stlink_tools_adapter_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/stlink_tools_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/stlink_tools_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/stlink_tools_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/stlink_tools_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/stlink_tools_adapter_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stlink-tools config for STM32H7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/stlink_tools_adapter_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stlink-tools config for STM32WB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/stlink_tools_adapter_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stlink-tools config has no host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
