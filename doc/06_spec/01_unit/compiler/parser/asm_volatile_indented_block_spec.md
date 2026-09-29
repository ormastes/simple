# asm_volatile_indented_block_spec

> Regression coverage for compiled_checker_asm_volatile_indent_gap_2026_08_03.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# asm_volatile_indented_block_spec

Regression coverage for compiled_checker_asm_volatile_indent_gap_2026_08_03.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/asm_volatile_indented_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for compiled_checker_asm_volatile_indent_gap_2026_08_03.

## Scenarios

### asm volatile indented blocks

#### parses the exact RISC-V instruction and input constraint form

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the exact RISC-V instruction and input constraint form
   - Expected: asm_parses_clean("asm_volatile_riscv_exact.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the exact RISC-V instruction and input constraint form")
val source = "fn cbo_clean(addr: u64):\n" +
    "    unsafe:\n" +
    "        asm volatile:\n" +
    "            \"cbo.clean 0(\{addr\})\"\n" +
    "            in(reg) addr\n"
expect(asm_parses_clean("asm_volatile_riscv_exact.spl", source)).to_equal(true)
```

</details>

#### preserves adjacent named output inout and option directives

- preserves adjacent named output inout and option directives
   - Expected: asm_parses_clean("asm_volatile_adjacent_operands.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves adjacent named output inout and option directives")
val source = "fn update(src: u64):\n" +
    "    var dst = 0\n" +
    "    asm volatile:\n" +
    "        \"add \{dst\}, \{src\}, 1\"\n" +
    "        dst = out(reg) dst\n" +
    "        src = in(reg) src\n" +
    "        options(nostack, readonly)\n"
expect(asm_parses_clean("asm_volatile_adjacent_operands.spl", source)).to_equal(true)
```

</details>

#### rejects an unknown directive then recovers for a valid block

- rejects an unknown directive then recovers for a valid block
   - Expected: asm_parses_clean("asm_volatile_bad_directive.spl", malformed) is false
   - Expected: asm_parses_clean("asm_volatile_recovery.spl", valid) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown directive then recovers for a valid block")
val malformed = "fn bad(addr: u64):\n" +
    "    asm volatile:\n" +
    "        \"nop\"\n" +
    "        mystery(reg) addr\n"
expect(asm_parses_clean("asm_volatile_bad_directive.spl", malformed)).to_equal(false)
val valid = "fn good():\n" +
    "    asm volatile:\n" +
    "        \"fence.i\"\n"
expect(asm_parses_clean("asm_volatile_recovery.spl", valid)).to_equal(true)
```

</details>

#### keeps braced and parenthesized neighboring forms accepted

- keeps braced and parenthesized neighboring forms accepted
   - Expected: asm_parses_clean("asm_volatile_neighbors.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps braced and parenthesized neighboring forms accepted")
val source = "fn neighbors(value: u64):\n" +
    "    asm volatile \{ fence.i \}\n" +
    "    asm volatile(\"mv a0, \{value\}\", in(reg) value)\n"
expect(asm_parses_clean("asm_volatile_neighbors.spl", source)).to_equal(true)
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

- Canonical SPipe generation for source `0b29a819a1ca60468326726a2a66737d5a6f8db43de58554bc7df2490f608f45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b29a819a1ca60468326726a2a66737d5a6f8db43de58554bc7df2490f608f45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b29a819a1ca60468326726a2a66737d5a6f8db43de58554bc7df2490f608f45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/asm_volatile_indented_block_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/asm_volatile_indented_block_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/asm_volatile_indented_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/asm_volatile_indented_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/asm_volatile_indented_block_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the exact RISC-V instruction and input constraint form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/asm_volatile_indented_block_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves adjacent named output inout and option directives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/asm_volatile_indented_block_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown directive then recovers for a valid block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
