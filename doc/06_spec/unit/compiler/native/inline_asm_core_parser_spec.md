# inline_asm_core_parser_spec

> Purpose: Prove that Core parser raw asm blocks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# inline_asm_core_parser_spec

Purpose: Prove that Core parser raw asm blocks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/native/inline_asm_core_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Core parser raw asm blocks.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Core parser raw asm blocks

#### preserves unquoted x86 instruction

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves unquoted x86 instruction
- Verify: preserves unquoted x86 instruction
   - Expected: parse_first_asm_text("fn test():\n    asm \{ cli \}\n") equals `cli`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves unquoted x86 instruction")
step("Verify: preserves unquoted x86 instruction")
# @req: REQ-COMPILER-NATIVE-001
expect(parse_first_asm_text("fn test():\n    asm \{ cli \}\n")).to_equal("cli")
```

</details>

#### preserves ARM immediate hash text

- preserves ARM immediate hash text
- Verify: preserves ARM immediate hash text
   - Expected: parse_first_asm_text("fn test():\n    asm volatile \{ bkpt #0 \}\n") equals `bkpt #0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves ARM immediate hash text")
step("Verify: preserves ARM immediate hash text")
expect(parse_first_asm_text("fn test():\n    asm volatile \{ bkpt #0 \}\n")).to_equal("bkpt #0")
```

</details>

#### preserves RISC-V comma operands

- preserves RISC-V comma operands
- Verify: preserves RISC-V comma operands
   - Expected: parse_first_asm_text("fn test():\n    asm { fence rw, rw }\n") equals `fence rw, rw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves RISC-V comma operands")
step("Verify: preserves RISC-V comma operands")
expect(parse_first_asm_text("fn test():\n    asm { fence rw, rw }\n")).to_equal("fence rw, rw")
```

</details>

#### normalizes multiple lines

- normalizes multiple lines
- Verify: normalizes multiple lines
   - Expected: text equals `cli\nhlt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes multiple lines")
step("Verify: normalizes multiple lines")
val text = parse_first_asm_text("fn test():\n    asm {\n        cli\n        hlt\n    }\n")
expect(text).to_equal("cli\nhlt")
```

</details>

#### keeps quoted braced lines compatible

- keeps quoted braced lines compatible
- Verify: keeps quoted braced lines compatible
   - Expected: parse_first_asm_text("fn test():\n    asm \{ \"nop\" \}\n") equals `nop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps quoted braced lines compatible")
step("Verify: keeps quoted braced lines compatible")
expect(parse_first_asm_text("fn test():\n    asm \{ \"nop\" \}\n")).to_equal("nop")
```

</details>

#### does not warn for canonical braced asm

- does not warn for canonical braced asm
- Verify: does not warn for canonical braced asm
   - Expected: parse_first_asm_warning_count("fn test():\n    asm \{ nop \}\n") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn for canonical braced asm")
step("Verify: does not warn for canonical braced asm")
expect(parse_first_asm_warning_count("fn test():\n    asm \{ nop \}\n")).to_equal(0)
```

</details>

#### warns for legacy parenthesized asm

- warns for legacy parenthesized asm
- Verify: warns for legacy parenthesized asm
   - Expected: parse_first_asm_warning_count("fn test():\n    asm(\"nop\")\n") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for legacy parenthesized asm")
step("Verify: warns for legacy parenthesized asm")
expect(parse_first_asm_warning_count("fn test():\n    asm(\"nop\")\n")).to_equal(1)
```

</details>

#### warns for legacy bare string asm

- warns for legacy bare string asm
- Verify: warns for legacy bare string asm
   - Expected: parse_first_asm_warning_count("fn test():\n    asm \"nop\"\n") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for legacy bare string asm")
step("Verify: warns for legacy bare string asm")
expect(parse_first_asm_warning_count("fn test():\n    asm \"nop\"\n")).to_equal(1)
```

</details>

#### warns for legacy colon string asm

- warns for legacy colon string asm
- Verify: warns for legacy colon string asm
   - Expected: parse_first_asm_warning_count("fn test():\n    asm: \"nop\"\n") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for legacy colon string asm")
step("Verify: warns for legacy colon string asm")
expect(parse_first_asm_warning_count("fn test():\n    asm: \"nop\"\n")).to_equal(1)
```

</details>

#### warns for legacy colon block asm

- warns for legacy colon block asm
- Verify: warns for legacy colon block asm
   - Expected: parse_first_asm_warning_count("fn test():\n    asm:\n        \"nop\"\n") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for legacy colon block asm")
step("Verify: warns for legacy colon block asm")
expect(parse_first_asm_warning_count("fn test():\n    asm:\n        \"nop\"\n")).to_equal(1)
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-NATIVE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `151139624601596b1035902659cf387567f08b856d0b3fadd8f47496f5f96281`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `151139624601596b1035902659cf387567f08b856d0b3fadd8f47496f5f96281`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `151139624601596b1035902659cf387567f08b856d0b3fadd8f47496f5f96281`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/native/inline_asm_core_parser_spec.spl
mirror: doc/06_spec/unit/compiler/native/inline_asm_core_parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/native/inline_asm_core_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/native/inline_asm_core_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/native/inline_asm_core_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/native/inline_asm_core_parser_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves unquoted x86 instruction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/native/inline_asm_core_parser_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves ARM immediate hash text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/native/inline_asm_core_parser_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves RISC-V comma operands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
