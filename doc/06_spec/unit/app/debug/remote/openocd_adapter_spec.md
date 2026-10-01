# Openocd Adapter Specification

> Tests covering OpenocdAdapter config factories, OpenocdAdapter capabilities, OpenocdAdapter name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openocd Adapter Specification

## Scenarios

### OpenocdAdapter config factories

#### openocd config for STM32H7

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- openocd config for STM32H7
   - Expected: cfg.adapter_type equals `openocd`
   - Expected: cfg.port equals `3333`
   - Expected: cfg.architecture equals `board/stm32h7x3i_eval.cfg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("openocd config for STM32H7")
val cfg = AdapterConfig.openocd("board/stm32h7x3i_eval.cfg", 3333, "test.elf")
expect(cfg.adapter_type).to_equal("openocd")
expect(cfg.port).to_equal(3333)
expect(cfg.architecture).to_equal("board/stm32h7x3i_eval.cfg")
```

</details>

#### openocd config for STM32WB

- openocd config for STM32WB
   - Expected: cfg.port equals `3334`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("openocd config for STM32WB")
val cfg = AdapterConfig.openocd("board/stm32wb5x_nucleo.cfg", 3334, "test.elf")
expect(cfg.port).to_equal(3334)
expect(cfg.architecture).to_contain("stm32wb")
```

</details>

#### openocd config has localhost host

- openocd config has localhost host
   - Expected: cfg.host equals `localhost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("openocd config has localhost host")
val cfg = AdapterConfig.openocd("board/stm32h7x3i_eval.cfg", 3333, "test.elf")
expect(cfg.host).to_equal("localhost")
```

</details>

#### openocd config has correct program

- openocd config has correct program
   - Expected: cfg.program equals `my_app.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("openocd config has correct program")
val cfg = AdapterConfig.openocd("board/stm32h7x3i_eval.cfg", 3333, "my_app.elf")
expect(cfg.program).to_equal("my_app.elf")
```

</details>

### OpenocdAdapter capabilities

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

### OpenocdAdapter name

#### adapter name is openocd

- adapter name is openocd
   - Expected: name equals `openocd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adapter name is openocd")
val name = "openocd"
expect(name).to_equal("openocd")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/openocd_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OpenocdAdapter config factories, OpenocdAdapter capabilities, OpenocdAdapter name.
- OpenocdAdapter config factories
- OpenocdAdapter capabilities
- OpenocdAdapter name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `dc46ad7a0c9ae51d5b629bdd559358b9428086cb56ff772c965e78032cfa302b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc46ad7a0c9ae51d5b629bdd559358b9428086cb56ff772c965e78032cfa302b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc46ad7a0c9ae51d5b629bdd559358b9428086cb56ff772c965e78032cfa302b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/debug/remote/openocd_adapter_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/openocd_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/openocd_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/openocd_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/openocd_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/openocd_adapter_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'openocd config for STM32H7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/openocd_adapter_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'openocd config for STM32WB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/openocd_adapter_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'openocd config has localhost host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
