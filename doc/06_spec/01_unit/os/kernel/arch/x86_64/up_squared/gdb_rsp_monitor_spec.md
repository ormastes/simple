# Gdb Rsp Monitor Specification

> Tests covering UP2 target-side GDB RSP framing, UP2 target-side GDB RSP query planning, UP2 target-side GDB RSP bounded memory planning.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gdb Rsp Monitor Specification

## Scenarios

### UP2 target-side GDB RSP framing

#### round trips a checksummed query packet

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round trips a checksummed query packet
   - Expected: frame.starts_with("$qSupported:multiprocess+#") is true
   - Expected: decoded.is_ok() is true
   - Expected: decoded.unwrap() equals `qSupported:multiprocess+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round trips a checksummed query packet")
val frame = up2_rsp_frame("qSupported:multiprocess+")
expect(frame.starts_with("$qSupported:multiprocess+#")).to_equal(true)
val decoded = up2_rsp_decode_frame(frame)
expect(decoded.is_ok()).to_equal(true)
expect(decoded.unwrap()).to_equal("qSupported:multiprocess+")
```

</details>

#### rejects malformed, oversized, and mismatched checksums

- rejects malformed, oversized, and mismatched checksums
   - Expected: up2_rsp_decode_frame("qSupported#00").unwrap_err() equals `rsp-frame`
   - Expected: up2_rsp_decode_frame("$qSupported#zz").unwrap_err() equals `rsp-checksum-format`
   - Expected: up2_rsp_decode_frame("$qSupported#00").unwrap_err() equals `rsp-checksum`
   - Expected: up2_rsp_decode_frame("$" + ("a" * 4094) + "#00").unwrap_err() equals `rsp-frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects malformed, oversized, and mismatched checksums")
expect(up2_rsp_decode_frame("qSupported#00").unwrap_err()).to_equal("rsp-frame")
expect(up2_rsp_decode_frame("$qSupported#zz").unwrap_err()).to_equal("rsp-checksum-format")
expect(up2_rsp_decode_frame("$qSupported#00").unwrap_err()).to_equal("rsp-checksum")
expect(up2_rsp_decode_frame("$" + ("a" * 4094) + "#00").unwrap_err()).to_equal("rsp-frame")
```

</details>

#### uses the byte-sum modulo 256 checksum

- uses the byte-sum modulo 256 checksum
   - Expected: up2_rsp_checksum("m0,1") equals `0xfau8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses the byte-sum modulo 256 checksum")
expect(up2_rsp_checksum("m0,1")).to_equal(0xfau8)
```

</details>

### UP2 target-side GDB RSP query planning

#### advertises only packet size and reports one attached thread

- advertises only packet size and reports one attached thread
   - Expected: up2_rsp_plan("qSupported:xmlRegisters=i386").response equals `PacketSize=1000`
   - Expected: up2_rsp_plan("qAttached").response equals `1`
   - Expected: up2_rsp_plan("qC").response equals `QC1`
   - Expected: up2_rsp_plan("qfThreadInfo").response equals `m1`
   - Expected: up2_rsp_plan("qsThreadInfo").response equals `l`
   - Expected: up2_rsp_plan("Hg0").response equals `OK`
   - Expected: up2_rsp_plan("?").response equals `S00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("advertises only packet size and reports one attached thread")
expect(up2_rsp_plan("qSupported:xmlRegisters=i386").response).to_equal("PacketSize=1000")
expect(up2_rsp_plan("qAttached").response).to_equal("1")
expect(up2_rsp_plan("qC").response).to_equal("QC1")
expect(up2_rsp_plan("qfThreadInfo").response).to_equal("m1")
expect(up2_rsp_plan("qsThreadInfo").response).to_equal("l")
expect(up2_rsp_plan("Hg0").response).to_equal("OK")
expect(up2_rsp_plan("?").response).to_equal("S00")
```

</details>

#### fails closed for register, breakpoint, continue, and step packets

- fails closed for register, breakpoint, continue, and step packets
   - Expected: up2_rsp_plan("g").response equals ``
   - Expected: up2_rsp_plan("p0").response equals ``
   - Expected: up2_rsp_plan("Z0,a000000,1").response equals ``
   - Expected: up2_rsp_plan("c").response equals ``
   - Expected: up2_rsp_plan("s").response equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed for register, breakpoint, continue, and step packets")
expect(up2_rsp_plan("g").response).to_equal("")
expect(up2_rsp_plan("p0").response).to_equal("")
expect(up2_rsp_plan("Z0,a000000,1").response).to_equal("")
expect(up2_rsp_plan("c").response).to_equal("")
expect(up2_rsp_plan("s").response).to_equal("")
```

</details>

#### plans detach without treating it as target reset

- plans detach without treating it as target reset
   - Expected: plan.operation equals `Up2RspOperation.Detach`
   - Expected: plan.response equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("plans detach without treating it as target reset")
val plan = up2_rsp_plan("D")
expect(plan.operation).to_equal(Up2RspOperation.Detach)
expect(plan.response).to_equal("OK")
```

</details>

### UP2 target-side GDB RSP bounded memory planning

#### admits reads at both staging boundaries

- admits reads at both staging boundaries
   - Expected: first.operation equals `Up2RspOperation.ReadMemory`
   - Expected: first.address equals `UP2_RSP_STAGING_START`
   - Expected: first.length equals `1`
   - Expected: last.operation equals `Up2RspOperation.ReadMemory`
   - Expected: last.address equals `UP2_RSP_STAGING_START + UP2_RSP_STAGING_SIZE - 1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits reads at both staging boundaries")
val first = up2_rsp_plan("m0a000000,1")
expect(first.operation).to_equal(Up2RspOperation.ReadMemory)
expect(first.address).to_equal(UP2_RSP_STAGING_START)
expect(first.length).to_equal(1)
val last = up2_rsp_plan("m0affffff,1")
expect(last.operation).to_equal(Up2RspOperation.ReadMemory)
expect(last.address).to_equal(UP2_RSP_STAGING_START + UP2_RSP_STAGING_SIZE - 1u64)
```

</details>

#### admits an exact write and decodes its bytes

- admits an exact write and decodes its bytes
   - Expected: plan.operation equals `Up2RspOperation.WriteMemory`
   - Expected: plan.length equals `4`
   - Expected: plan.data equals `[0x00u8, 0xa5u8, 0x5au8, 0xffu8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits an exact write and decodes its bytes")
val plan = up2_rsp_plan("M0a000010,4:00a55aff")
expect(plan.operation).to_equal(Up2RspOperation.WriteMemory)
expect(plan.length).to_equal(4)
expect(plan.data).to_equal([0x00u8, 0xa5u8, 0x5au8, 0xffu8])
```

</details>

#### rejects zero, oversized, overflowed, and out-of-range reads

- rejects zero, oversized, overflowed, and out-of-range reads
   - Expected: up2_rsp_plan("m0a000000,0").response equals `E02`
   - Expected: up2_rsp_plan("m0a000000,401").response equals `E02`
   - Expected: UP2_RSP_MAX_TRANSFER equals `1024`
   - Expected: up2_rsp_plan("m09ffffff,1").response equals `E02`
   - Expected: up2_rsp_plan("m0b000000,1").response equals `E02`
   - Expected: up2_rsp_plan("mffffffffffffffff,2").response equals `E02`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects zero, oversized, overflowed, and out-of-range reads")
expect(up2_rsp_plan("m0a000000,0").response).to_equal("E02")
expect(up2_rsp_plan("m0a000000,401").response).to_equal("E02")
expect(UP2_RSP_MAX_TRANSFER).to_equal(1024)
expect(up2_rsp_plan("m09ffffff,1").response).to_equal("E02")
expect(up2_rsp_plan("m0b000000,1").response).to_equal("E02")
expect(up2_rsp_plan("mffffffffffffffff,2").response).to_equal("E02")
```

</details>

#### rejects malformed and length-mismatched writes

- rejects malformed and length-mismatched writes
   - Expected: up2_rsp_plan("M0a000000,2:00").response equals `E01`
   - Expected: up2_rsp_plan("M0a000000,1:zz").response equals `E01`
   - Expected: up2_rsp_plan("M0a000000:00").response equals `E01`
   - Expected: up2_rsp_plan("M0a000000,1").response equals `E01`
   - Expected: up2_rsp_plan("mxyz,1").response equals `E01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects malformed and length-mismatched writes")
expect(up2_rsp_plan("M0a000000,2:00").response).to_equal("E01")
expect(up2_rsp_plan("M0a000000,1:zz").response).to_equal("E01")
expect(up2_rsp_plan("M0a000000:00").response).to_equal("E01")
expect(up2_rsp_plan("M0a000000,1").response).to_equal("E01")
expect(up2_rsp_plan("mxyz,1").response).to_equal("E01")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UP2 target-side GDB RSP framing, UP2 target-side GDB RSP query planning, UP2 target-side GDB RSP bounded memory planning.
- UP2 target-side GDB RSP framing
- UP2 target-side GDB RSP query planning
- UP2 target-side GDB RSP bounded memory planning

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `24ecc65b6de500bc961999dde2e20e03c01e63772352b78adccf844e83469a12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24ecc65b6de500bc961999dde2e20e03c01e63772352b78adccf844e83469a12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24ecc65b6de500bc961999dde2e20e03c01e63772352b78adccf844e83469a12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round trips a checksummed query packet' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed, oversized, and mismatched checksums' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/x86_64/up_squared/gdb_rsp_monitor_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the byte-sum modulo 256 checksum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
