# Elf Symbols High Byte Sanitize Specification

> Tests covering ELF symbol C-string high-byte sanitization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Symbols High Byte Sanitize Specification

## Scenarios

### ELF symbol C-string high-byte sanitization

#### replaces every byte above 0x7E with a single placeholder

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- replaces every byte above 0x7E with a single placeholder
   - Expected: decoded equals `???`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("replaces every byte above 0x7E with a single placeholder")
val decoded = elf_symbol_cstring_to_text([128u8, 200u8, 255u8, 0u8], 0)
expect(decoded).to_equal("???")
```

</details>

#### never lengthens the decoded name beyond the source byte count

- never lengthens the decoded name beyond the source byte count
   - Expected: decoded equals `A?B?`
   - Expected: decoded.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never lengthens the decoded name beyond the source byte count")
# 4 name bytes in, at most 4 characters out — the latin-1 widening bug
# produced 8 bytes here.
val decoded = elf_symbol_cstring_to_text([65u8, 200u8, 66u8, 255u8, 0u8], 0)
expect(decoded).to_equal("A?B?")
expect(decoded.len()).to_equal(4)
```

</details>

#### leaves the printable ASCII range untouched

- leaves the printable ASCII range untouched
   - Expected: decoded equals `_Zz0~`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves the printable ASCII range untouched")
val decoded = elf_symbol_cstring_to_text([95u8, 90u8, 122u8, 48u8, 126u8, 0u8], 0)
expect(decoded).to_equal("_Zz0~")
```

</details>

#### still decodes the whitespace escapes and honours the offset

- still decodes the whitespace escapes and honours the offset
   - Expected: decoded equals `a\n\r\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still decodes the whitespace escapes and honours the offset")
val decoded = elf_symbol_cstring_to_text([0u8, 97u8, 10u8, 13u8, 9u8, 0u8], 1)
expect(decoded).to_equal("a\n\r\t")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ELF symbol C-string high-byte sanitization.
- ELF symbol C-string high-byte sanitization

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `889fabffc0b1a0c6571ec27f62316f4face514ffba86a0bc9a7a0637874ed470`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `889fabffc0b1a0c6571ec27f62316f4face514ffba86a0bc9a7a0637874ed470`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `889fabffc0b1a0c6571ec27f62316f4face514ffba86a0bc9a7a0637874ed470`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces every byte above 0x7E with a single placeholder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never lengthens the decoded name beyond the source byte count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/introspection/elf_symbols_high_byte_sanitize_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves the printable ASCII range untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
