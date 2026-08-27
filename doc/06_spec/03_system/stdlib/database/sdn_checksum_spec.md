# Sdn Checksum Specification

> Tests covering CRC32 Runtime, SDN Checksum Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdn Checksum Specification

## Scenarios

### CRC32 Runtime

#### returns consistent hash for same input

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns consistent hash for same input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns consistent hash for same input")
val crc1 = rt_crc32_text("hello")
val crc2 = rt_crc32_text("hello")
expect crc1 == crc2
```

</details>

#### returns different hash for different input

- returns different hash for different input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns different hash for different input")
val crc1 = rt_crc32_text("hello")
val crc2 = rt_crc32_text("world")
expect crc1 != crc2
```

</details>

#### handles empty string

- handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty string")
val crc = rt_crc32_text("")
expect crc == 0
```

</details>

#### matches known CRC32 test vector

- matches known CRC32 test vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches known CRC32 test vector")
val crc = rt_crc32_text("123456789")
expect crc == 3421780262
```

</details>

### SDN Checksum Integration

#### computes and verifies checksum header

- computes and verifies checksum header


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes and verifies checksum header")
val body = "test data here\n"
val crc = rt_crc32_text(body)
val content = "#sdn-crc32:{crc}\n" + body
expect content.starts_with("#sdn-crc32:")
```

</details>

#### detects corruption in body

- detects corruption in body


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects corruption in body")
val body = "original data\n"
val crc = rt_crc32_text(body)
val corrupted = "corrupted data\n"
val crc2 = rt_crc32_text(corrupted)
expect crc != crc2
```

</details>

#### parses checksum header correctly

- parses checksum header correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses checksum header correctly")
val body = "table_data|col1,col2|\n1\tAlice\n"
val crc = rt_crc32_text(body)
val content = "#sdn-crc32:{crc}\n" + body
val lines = content.split("\n")
val header_line = lines[0]
expect header_line.starts_with("#sdn-crc32:")
val stored_str = header_line.slice(11, header_line.len())
val stored_crc = stored_str.to_int() ?? -1
expect stored_crc == crc
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/database/sdn_checksum_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CRC32 Runtime, SDN Checksum Integration.
- CRC32 Runtime
- SDN Checksum Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `902c35e06605b79daf2c61b3f3eb00eaa37f42637a21fc06fdffc7a3446da15f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `902c35e06605b79daf2c61b3f3eb00eaa37f42637a21fc06fdffc7a3446da15f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `902c35e06605b79daf2c61b3f3eb00eaa37f42637a21fc06fdffc7a3446da15f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/stdlib/database/sdn_checksum_spec.spl
mirror: doc/06_spec/03_system/stdlib/database/sdn_checksum_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/database/sdn_checksum_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/database/sdn_checksum_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/database/sdn_checksum_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns consistent hash for same input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/sdn_checksum_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns different hash for different input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/sdn_checksum_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
