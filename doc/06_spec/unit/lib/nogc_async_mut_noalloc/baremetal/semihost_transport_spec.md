# Semihost Transport Specification

> Tests covering Transport Constants, Capability Flags, Config Defaults, Ring Buffer Power-of-2.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semihost Transport Specification

## Scenarios

### Transport Constants

#### WRITEC is 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- WRITEC is 1
   - Expected: TRANSPORT_WRITEC equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WRITEC is 1")
val TRANSPORT_WRITEC = 1
expect(TRANSPORT_WRITEC).to_equal(1)
```

</details>

#### WRITE0 is 2

- WRITE0 is 2
   - Expected: TRANSPORT_WRITE0 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WRITE0 is 2")
val TRANSPORT_WRITE0 = 2
expect(TRANSPORT_WRITE0).to_equal(2)
```

</details>

#### WRITE is 3

- WRITE is 3
   - Expected: TRANSPORT_WRITE equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WRITE is 3")
val TRANSPORT_WRITE = 3
expect(TRANSPORT_WRITE).to_equal(3)
```

</details>

#### BATCH_N is 4

- BATCH_N is 4
   - Expected: TRANSPORT_BATCH_N equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BATCH_N is 4")
val TRANSPORT_BATCH_N = 4
expect(TRANSPORT_BATCH_N).to_equal(4)
```

</details>

#### BUFFERED is 5

- BUFFERED is 5
   - Expected: TRANSPORT_BUFFERED equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BUFFERED is 5")
val TRANSPORT_BUFFERED = 5
expect(TRANSPORT_BUFFERED).to_equal(5)
```

</details>

#### UART is 6

- UART is 6
   - Expected: TRANSPORT_UART equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UART is 6")
val TRANSPORT_UART = 6
expect(TRANSPORT_UART).to_equal(6)
```

</details>

#### RAW_BINARY is 7

- RAW_BINARY is 7
   - Expected: TRANSPORT_RAW_BINARY equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RAW_BINARY is 7")
val TRANSPORT_RAW_BINARY = 7
expect(TRANSPORT_RAW_BINARY).to_equal(7)
```

</details>

#### INTERNED is 8

- INTERNED is 8
   - Expected: TRANSPORT_INTERNED equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("INTERNED is 8")
val TRANSPORT_INTERNED = 8
expect(TRANSPORT_INTERNED).to_equal(8)
```

</details>

#### all transport constants are unique

- all transport constants are unique
   - Expected: values.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all transport constants are unique")
val values = [1, 2, 3, 4, 5, 6, 7, 8]
expect(values.len()).to_equal(8)
```

</details>

### Capability Flags

#### CAP_WRITEC is 1

- CAP_WRITEC is 1
   - Expected: CAP_WRITEC equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CAP_WRITEC is 1")
val CAP_WRITEC = 1
expect(CAP_WRITEC).to_equal(1)
```

</details>

#### CAP_WRITE0 is 2

- CAP_WRITE0 is 2
   - Expected: CAP_WRITE0 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CAP_WRITE0 is 2")
val CAP_WRITE0 = 2
expect(CAP_WRITE0).to_equal(2)
```

</details>

#### CAP_WRITE is 4

- CAP_WRITE is 4
   - Expected: CAP_WRITE equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CAP_WRITE is 4")
val CAP_WRITE = 4
expect(CAP_WRITE).to_equal(4)
```

</details>

#### CAP_UART is 8

- CAP_UART is 8
   - Expected: CAP_UART equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CAP_UART is 8")
val CAP_UART = 8
expect(CAP_UART).to_equal(8)
```

</details>

#### CAP_INTERNED is 16

- CAP_INTERNED is 16
   - Expected: CAP_INTERNED equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CAP_INTERNED is 16")
val CAP_INTERNED = 16
expect(CAP_INTERNED).to_equal(16)
```

</details>

#### capability flags are disjoint powers of 2

- capability flags are disjoint powers of 2
   - Expected: all_disjoint is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capability flags are disjoint powers of 2")
val caps = [1, 2, 4, 8, 16]
# Each pair OR'd must differ from each individual
var i = 0
var all_disjoint = true
while i < 5:
    var j = i + 1
    while j < 5:
        val combined = caps[i] | caps[j]
        if combined == caps[i]:
            all_disjoint = false
        if combined == caps[j]:
            all_disjoint = false
        j = j + 1
    i = i + 1
expect(all_disjoint).to_equal(true)
```

</details>

#### full capability mask combines all flags

- full capability mask combines all flags
   - Expected: all_caps equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full capability mask combines all flags")
val all_caps = 1 | 2 | 4 | 8 | 16
expect(all_caps).to_equal(31)
```

</details>

### Config Defaults

#### default batch_size is 3

- default batch_size is 3
   - Expected: default_batch equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default batch_size is 3")
val default_batch = 3
expect(default_batch).to_equal(3)
```

</details>

#### default UART base is 0x10000000

- default UART base is 0x10000000
   - Expected: default_uart equals `268435456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default UART base is 0x10000000")
val default_uart = 0x10000000
expect(default_uart).to_equal(268435456)
```

</details>

#### RAW_BINARY_MAGIC is 0x53 (ASCII S)

- RAW_BINARY_MAGIC is 0x53 (ASCII S)
   - Expected: magic equals `83`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RAW_BINARY_MAGIC is 0x53 (ASCII S)")
val magic = 0x53
expect(magic).to_equal(83)
```

</details>

### Ring Buffer Power-of-2

#### next_power_of_2 for 1 is 1

- next_power_of_2 for 1 is 1
   - Expected: v + 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("next_power_of_2 for 1 is 1")
var v = 0
v = v | (v >> 1)
v = v | (v >> 2)
v = v | (v >> 4)
v = v | (v >> 8)
v = v | (v >> 16)
# n=1 => v = 1-1 = 0, result = 0+1 = 1
expect(v + 1).to_equal(1)
```

</details>

#### next_power_of_2 for 5 is 8

- next_power_of_2 for 5 is 8
   - Expected: v + 1 equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("next_power_of_2 for 5 is 8")
var v = 5 - 1  # 4
v = v | (v >> 1)   # 4|2 = 6
v = v | (v >> 2)   # 6|1 = 7
v = v | (v >> 4)   # 7|0 = 7
v = v | (v >> 8)   # 7
v = v | (v >> 16)  # 7
expect(v + 1).to_equal(8)
```

</details>

#### next_power_of_2 for 16 is 16

- next_power_of_2 for 16 is 16
   - Expected: v + 1 equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("next_power_of_2 for 16 is 16")
var v = 16 - 1  # 15
v = v | (v >> 1)   # 15
v = v | (v >> 2)   # 15
v = v | (v >> 4)   # 15
v = v | (v >> 8)   # 15
v = v | (v >> 16)  # 15
expect(v + 1).to_equal(16)
```

</details>

#### bitmask wrapping works for capacity 4

- bitmask wrapping works for capacity 4
   - Expected: idx equals `1`
   - Expected: idx equals `2`
   - Expected: idx equals `3`
   - Expected: idx equals `0)  # wraps around`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bitmask wrapping works for capacity 4")
val mask = 3  # capacity 4 - 1
var idx = 0
idx = (idx + 1) & mask
expect(idx).to_equal(1)
idx = (idx + 1) & mask
expect(idx).to_equal(2)
idx = (idx + 1) & mask
expect(idx).to_equal(3)
idx = (idx + 1) & mask
expect(idx).to_equal(0)  # wraps around
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Transport Constants, Capability Flags, Config Defaults, Ring Buffer Power-of-2.
- Transport Constants
- Capability Flags
- Config Defaults
- Ring Buffer Power-of-2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `7acb5a062c1ad10d140c596816624d2da591960dc02de06210fd8fc59e04669f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7acb5a062c1ad10d140c596816624d2da591960dc02de06210fd8fc59e04669f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7acb5a062c1ad10d140c596816624d2da591960dc02de06210fd8fc59e04669f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 24 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WRITEC is 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WRITE0 is 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WRITE is 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
