# RV64 Hello World SoC Integration Tests

> Full SoC pipeline: bus decode, UART output, timer, SRAM.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Hello World SoC Integration Tests

Full SoC pipeline: bus decode, UART output, timer, SRAM.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-HELLO-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/integration/hardware/rv64gc/rv64_hello_world_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Full SoC pipeline: bus decode, UART output, timer, SRAM.

## Scenarios

### Bus Address Decode

#### CLINT region: 0x02000000-0x0200FFFF

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- CLINT region: 0x02000000-0x0200FFFF
   - Expected: in_clint is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("CLINT region: 0x02000000-0x0200FFFF")
val addr = CLINT_BASE + 0x4000
val in_clint = addr >= CLINT_BASE and addr < CLINT_BASE + 0x10000
expect(in_clint).to_equal(true)
```

</details>

#### PLIC region: 0x0C000000-0x0FFFFFFF

- PLIC region: 0x0C000000-0x0FFFFFFF
   - Expected: in_plic is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PLIC region: 0x0C000000-0x0FFFFFFF")
val addr = PLIC_BASE + 0x200004
val in_plic = addr >= PLIC_BASE and addr < PLIC_BASE + 0x4000000
expect(in_plic).to_equal(true)
```

</details>

#### UART region: 0x10000000-0x10000FFF

- UART region: 0x10000000-0x10000FFF
   - Expected: in_uart is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("UART region: 0x10000000-0x10000FFF")
val addr = UART_BASE + 5
val in_uart = addr >= UART_BASE and addr < UART_BASE + 0x1000
expect(in_uart).to_equal(true)
```

</details>

#### DRAM region: 0x80000000+

- DRAM region: 0x80000000+
   - Expected: in_dram is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DRAM region: 0x80000000+")
val addr = DRAM_BASE + 0x1000
val in_dram = addr >= DRAM_BASE
expect(in_dram).to_equal(true)
```

</details>

### UART Model

#### TX register is ready when empty

- TX register is ready when empty
   - Expected: (lsr and 0x20) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("TX register is ready when empty")
# LSR bit 5 = THR empty
val lsr: i64 = 0x60  # Both THR empty and transmitter idle
expect((lsr and 0x20) != 0).to_equal(true)
```

</details>

#### write byte to THR

- write byte to THR
   - Expected: tx_byte equals `0x48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write byte to THR")
var tx_byte: i64 = 0
tx_byte = 0x48  # 'H'
expect(tx_byte).to_equal(0x48)
```

</details>

#### multiple bytes form string

- multiple bytes form string
   - Expected: hello.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("multiple bytes form string")
val hello = [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # "Hello"
expect(hello.len()).to_equal(5)
```

</details>

### Timer Model

#### mtime increments

- mtime increments
   - Expected: mtime equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mtime increments")
var mtime: i64 = 0
mtime = mtime + 1
expect(mtime).to_equal(1)
```

</details>

#### timer compare triggers interrupt

- timer compare triggers interrupt
   - Expected: mtime >= mtimecmp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("timer compare triggers interrupt")
val mtime: i64 = 100
val mtimecmp: i64 = 50
expect(mtime >= mtimecmp).to_equal(true)
```

</details>

#### timer compare not triggered before threshold

- timer compare not triggered before threshold
   - Expected: mtime >= mtimecmp is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("timer compare not triggered before threshold")
val mtime: i64 = 10
val mtimecmp: i64 = 50
expect(mtime >= mtimecmp).to_equal(false)
```

</details>

### SRAM Model (64-bit)

#### write and read 64-bit value

- write and read 64-bit value
   - Expected: mem[0] equals `0xDEADBEEFCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write and read 64-bit value")
var mem: [i64] = [0, 0, 0, 0]
mem[0] = 0xDEADBEEFCAFEBABE
expect(mem[0]).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### byte-addressable access

- byte-addressable access
   - Expected: byte_val and 0xFF equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("byte-addressable access")
var byte_val: i64 = 0xFF
expect(byte_val and 0xFF).to_equal(0xFF)
```

</details>

#### word-aligned access

- word-aligned access
   - Expected: aligned equals `0x80000008`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("word-aligned access")
val addr: i64 = 0x80000008
val aligned = addr and 0xFFFFFFFFFFFFFFF8
expect(aligned).to_equal(0x80000008)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5964b014713b86be80d58d858346e0f19da8fc157cf2b65cf19380e3fd21db5f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5964b014713b86be80d58d858346e0f19da8fc157cf2b65cf19380e3fd21db5f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5964b014713b86be80d58d858346e0f19da8fc157cf2b65cf19380e3fd21db5f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/hardware/rv64gc/rv64_hello_world_spec.spl
mirror: doc/06_spec/integration/hardware/rv64gc/rv64_hello_world_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/hardware/rv64gc/rv64_hello_world_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/hardware/rv64gc/rv64_hello_world_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/hardware/rv64gc/rv64_hello_world_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/hardware/rv64gc/rv64_hello_world_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CLINT region: 0x02000000-0x0200FFFF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/hardware/rv64gc/rv64_hello_world_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PLIC region: 0x0C000000-0x0FFFFFFF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/hardware/rv64gc/rv64_hello_world_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UART region: 0x10000000-0x10000FFF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
