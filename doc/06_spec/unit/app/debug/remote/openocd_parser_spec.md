# Openocd Parser Specification

> Tests covering OpenOCD hex formatting, OpenOCD mdw output parsing, OpenOCD process config.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openocd Parser Specification

## Scenarios

### OpenOCD hex formatting

#### formats 0 as 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats 0 as 0
   - Expected: rt_hex(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats 0 as 0")
expect(rt_hex(0)).to_equal("0")
```

</details>

#### formats 255 as ff

- formats 255 as ff
   - Expected: rt_hex(255) equals `ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats 255 as ff")
expect(rt_hex(255)).to_equal("ff")
```

</details>

#### formats 256 as 100

- formats 256 as 100
   - Expected: rt_hex(256) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats 256 as 100")
expect(rt_hex(256)).to_equal("100")
```

</details>

#### formats 0x1000 as 1000

- formats 0x1000 as 1000
   - Expected: rt_hex(4096) equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats 0x1000 as 1000")
expect(rt_hex(4096)).to_equal("1000")
```

</details>

#### formats address with 0x prefix

- formats address with 0x prefix
   - Expected: format_address(4096) equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats address with 0x prefix")
expect(format_address(4096)).to_equal("0x1000")
```

</details>

### OpenOCD mdw output parsing

#### parses single word

- parses single word


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single word")
val result = parse_mdw_output("0x08000000: 0xDEADBEEF")
expect(result.len()).to_be_greater_than(0)
```

</details>

#### parses hex values from output

- parses hex values from output


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hex values from output")
val result = parse_mdw_output("0x20000000: 0x0 0x0 0x0 0x0")
expect(result.len()).to_be_greater_than(0)
```

</details>

### OpenOCD process config

#### OpenOCD config path for STM32H7

- OpenOCD config path for STM32H7


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OpenOCD config path for STM32H7")
val cfg = "board/stm32h7x3i_eval.cfg"
expect(cfg).to_contain("stm32h7")
```

</details>

#### OpenOCD config path for STM32WB

- OpenOCD config path for STM32WB


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OpenOCD config path for STM32WB")
val cfg = "board/stm32wb5x_nucleo.cfg"
expect(cfg).to_contain("stm32wb")
```

</details>

#### GDB port defaults for STM32H7

- GDB port defaults for STM32H7
   - Expected: port equals `3333`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GDB port defaults for STM32H7")
val port = 3333
expect(port).to_equal(3333)
```

</details>

#### telnet port is GDB port + 1000

- telnet port is GDB port + 1000
   - Expected: telnet_port equals `4333`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("telnet port is GDB port + 1000")
val gdb_port = 3333
val telnet_port = gdb_port + 1000
expect(telnet_port).to_equal(4333)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/openocd_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OpenOCD hex formatting, OpenOCD mdw output parsing, OpenOCD process config.
- OpenOCD hex formatting
- OpenOCD mdw output parsing
- OpenOCD process config

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `ffaec3c5a2e1d54912dd48739106a9606281ecfcc411335df810f273af6cd5ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ffaec3c5a2e1d54912dd48739106a9606281ecfcc411335df810f273af6cd5ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ffaec3c5a2e1d54912dd48739106a9606281ecfcc411335df810f273af6cd5ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/debug/remote/openocd_parser_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/openocd_parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/openocd_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/openocd_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/openocd_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/openocd_parser_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats 0 as 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/openocd_parser_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats 255 as ff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/openocd_parser_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats 256 as 100' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
