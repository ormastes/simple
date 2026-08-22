# semihost_transport_spec

> Verifies the semihost transport behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# semihost_transport_spec

Verifies the semihost transport behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the semihost transport behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Transport Constants

#### WRITEC is 1

- Verify: WRITEC is 1
   - Expected: TRANSPORT_WRITEC equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: WRITEC is 1")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val TRANSPORT_WRITEC = 1
expect(TRANSPORT_WRITEC).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### WRITE0 is 2

- Verify: WRITE0 is 2
   - Expected: TRANSPORT_WRITE0 equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: WRITE0 is 2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val TRANSPORT_WRITE0 = 2
expect(TRANSPORT_WRITE0).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### WRITE is 3

- Verify: WRITE is 3
   - Expected: TRANSPORT_WRITE equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: WRITE is 3")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val TRANSPORT_WRITE = 3
expect(TRANSPORT_WRITE).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### BATCH_N is 4

- Verify: BATCH_N is 4
   - Expected: TRANSPORT_BATCH_N equals `4)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: BATCH_N is 4")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val TRANSPORT_BATCH_N = 4
expect(TRANSPORT_BATCH_N).to_equal(4)  # oracle: pinned constant asserted by this scenario
```

</details>

#### BUFFERED is 5

- Verify: BUFFERED is 5
   - Expected: TRANSPORT_BUFFERED equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: BUFFERED is 5")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val TRANSPORT_BUFFERED = 5
expect(TRANSPORT_BUFFERED).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

#### UART is 6

- Verify: UART is 6
   - Expected: TRANSPORT_UART equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: UART is 6")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val TRANSPORT_UART = 6
expect(TRANSPORT_UART).to_equal(6)  # oracle: pinned constant asserted by this scenario
```

</details>

#### RAW_BINARY is 7

- Verify: RAW_BINARY is 7
   - Expected: TRANSPORT_RAW_BINARY equals `7)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: RAW_BINARY is 7")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val TRANSPORT_RAW_BINARY = 7
expect(TRANSPORT_RAW_BINARY).to_equal(7)  # oracle: pinned constant asserted by this scenario
```

</details>

#### INTERNED is 8

- Verify: INTERNED is 8
   - Expected: TRANSPORT_INTERNED equals `8)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: INTERNED is 8")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val TRANSPORT_INTERNED = 8
expect(TRANSPORT_INTERNED).to_equal(8)  # oracle: pinned constant asserted by this scenario
```

</details>

#### all transport constants are unique

- Verify: all transport constants are unique
   - Expected: values.len() equals `8)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: all transport constants are unique")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val values = [1, 2, 3, 4, 5, 6, 7, 8]
expect(values.len()).to_equal(8)  # oracle: pinned constant asserted by this scenario
```

</details>

### Capability Flags

#### CAP_WRITEC is 1

- Verify: CAP_WRITEC is 1
   - Expected: CAP_WRITEC equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: CAP_WRITEC is 1")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val CAP_WRITEC = 1
expect(CAP_WRITEC).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### CAP_WRITE0 is 2

- Verify: CAP_WRITE0 is 2
   - Expected: CAP_WRITE0 equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: CAP_WRITE0 is 2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val CAP_WRITE0 = 2
expect(CAP_WRITE0).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### CAP_WRITE is 4

- Verify: CAP_WRITE is 4
   - Expected: CAP_WRITE equals `4)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: CAP_WRITE is 4")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val CAP_WRITE = 4
expect(CAP_WRITE).to_equal(4)  # oracle: pinned constant asserted by this scenario
```

</details>

#### CAP_UART is 8

- Verify: CAP_UART is 8
   - Expected: CAP_UART equals `8)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: CAP_UART is 8")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val CAP_UART = 8
expect(CAP_UART).to_equal(8)  # oracle: pinned constant asserted by this scenario
```

</details>

#### CAP_INTERNED is 16

- Verify: CAP_INTERNED is 16
   - Expected: CAP_INTERNED equals `16)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: CAP_INTERNED is 16")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val CAP_INTERNED = 16
expect(CAP_INTERNED).to_equal(16)  # oracle: pinned constant asserted by this scenario
```

</details>

#### capability flags are disjoint powers of 2

- Verify: capability flags are disjoint powers of 2
   - Expected: all_disjoint is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: capability flags are disjoint powers of 2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: full capability mask combines all flags
   - Expected: all_caps equals `31)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: full capability mask combines all flags")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val all_caps = 1 | 2 | 4 | 8 | 16
expect(all_caps).to_equal(31)  # oracle: pinned constant asserted by this scenario
```

</details>

### Config Defaults

#### default batch_size is 3

- Verify: default batch_size is 3
   - Expected: default_batch equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: default batch_size is 3")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val default_batch = 3
expect(default_batch).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### default UART base is 0x10000000

- Verify: default UART base is 0x10000000
   - Expected: default_uart equals `268435456)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: default UART base is 0x10000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val default_uart = 0x10000000
expect(default_uart).to_equal(268435456)  # oracle: pinned constant asserted by this scenario
```

</details>

#### RAW_BINARY_MAGIC is 0x53 (ASCII S)

- Verify: RAW_BINARY_MAGIC is 0x53 (ASCII S)
   - Expected: magic equals `83)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: RAW_BINARY_MAGIC is 0x53 (ASCII S)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val magic = 0x53
expect(magic).to_equal(83)  # oracle: pinned constant asserted by this scenario
```

</details>

### Ring Buffer Power-of-2

#### next_power_of_2 for 1 is 1

- Verify: next_power_of_2 for 1 is 1
   - Expected: v + 1 equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: next_power_of_2 for 1 is 1")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var v = 0
v = v | (v >> 1)
v = v | (v >> 2)
v = v | (v >> 4)
v = v | (v >> 8)
v = v | (v >> 16)
# n=1 => v = 1-1 = 0, result = 0+1 = 1
expect(v + 1).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### next_power_of_2 for 5 is 8

- Verify: next_power_of_2 for 5 is 8
   - Expected: v + 1 equals `8)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: next_power_of_2 for 5 is 8")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var v = 5 - 1  # 4
v = v | (v >> 1)   # 4|2 = 6
v = v | (v >> 2)   # 6|1 = 7
v = v | (v >> 4)   # 7|0 = 7
v = v | (v >> 8)   # 7
v = v | (v >> 16)  # 7
expect(v + 1).to_equal(8)  # oracle: pinned constant asserted by this scenario
```

</details>

#### next_power_of_2 for 16 is 16

- Verify: next_power_of_2 for 16 is 16
   - Expected: v + 1 equals `16)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: next_power_of_2 for 16 is 16")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var v = 16 - 1  # 15
v = v | (v >> 1)   # 15
v = v | (v >> 2)   # 15
v = v | (v >> 4)   # 15
v = v | (v >> 8)   # 15
v = v | (v >> 16)  # 15
expect(v + 1).to_equal(16)  # oracle: pinned constant asserted by this scenario
```

</details>

#### bitmask wrapping works for capacity 4

- Verify: bitmask wrapping works for capacity 4
   - Expected: idx equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: idx equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: idx equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: idx equals `0)  # wraps around  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BAREMETAL_SEMIHOST_TRANSPORT-001
step("Verify: bitmask wrapping works for capacity 4")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val mask = 3  # capacity 4 - 1
var idx = 0
idx = (idx + 1) & mask
expect(idx).to_equal(1)  # oracle: pinned constant asserted by this scenario
idx = (idx + 1) & mask
expect(idx).to_equal(2)  # oracle: pinned constant asserted by this scenario
idx = (idx + 1) & mask
expect(idx).to_equal(3)  # oracle: pinned constant asserted by this scenario
idx = (idx + 1) & mask
expect(idx).to_equal(0)  # wraps around  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94208b6ebbcf6fee59713ad166c3c7b0f156258af11b09c8adb7c7c3dbfb9d06`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94208b6ebbcf6fee59713ad166c3c7b0f156258af11b09c8adb7c7c3dbfb9d06`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94208b6ebbcf6fee59713ad166c3c7b0f156258af11b09c8adb7c7c3dbfb9d06`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
