# ELF64 parser

> Verifies magic validation and header parsing of the minimal ELF64 loader.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ELF64 parser

Verifies magic validation and header parsing of the minimal ELF64 loader.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10 |
| Category | Kernel loader |
| Status | Active |
| Source | `test/unit/os/kernel/loader/elf64_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies magic validation and header parsing of the minimal ELF64 loader.

## Scenarios

### elf64_parse_header

#### rejects a truncated buffer

- rejects a truncated buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated buffer")
"""Anything shorter than the full ELF64 header is not parseable."""
val h = elf64_parse_header(_truncated())
expect(h).to_be_nil()
```

</details>

#### rejects a buffer with non-ELF magic

- rejects a buffer with non-ELF magic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a buffer with non-ELF magic")
"""Magic bytes must be 0x7F 'E' 'L' 'F'."""
val h = elf64_parse_header(_bad_magic())
expect(h).to_be_nil()
```

</details>

#### exposes the ELF64 magic bytes as expected constants

- exposes the ELF64 magic bytes as expected constants
   - Expected: ELF64_MAGIC_0 equals `0x7Fu8`
   - Expected: ELF64_MAGIC_1 equals `0x45u8`
   - Expected: ELF64_MAGIC_2 equals `0x4Cu8`
   - Expected: ELF64_MAGIC_3 equals `0x46u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the ELF64 magic bytes as expected constants")
"""These constants are the canonical ELF magic sequence."""
expect(ELF64_MAGIC_0).to_equal(0x7Fu8)
expect(ELF64_MAGIC_1).to_equal(0x45u8)
expect(ELF64_MAGIC_2).to_equal(0x4Cu8)
expect(ELF64_MAGIC_3).to_equal(0x46u8)
```

</details>

#### EHDR size is the canonical 64 bytes

- EHDR size is the canonical 64 bytes
   - Expected: ELF64_EHDR_SIZE equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EHDR size is the canonical 64 bytes")
"""Misreading header size is a classic loader bug — pin it."""
expect(ELF64_EHDR_SIZE).to_equal(64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `abbb13a898068cb9531b19779777acd0812e4a015591f2c246d96425aa6f18ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abbb13a898068cb9531b19779777acd0812e4a015591f2c246d96425aa6f18ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abbb13a898068cb9531b19779777acd0812e4a015591f2c246d96425aa6f18ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/kernel/loader/elf64_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/elf64_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/elf64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/elf64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/elf64_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/loader/elf64_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a truncated buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/elf64_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a buffer with non-ELF magic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/elf64_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the ELF64 magic bytes as expected constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
