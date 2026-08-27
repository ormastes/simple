# Allow Suppressions Canary Spec

> Canary spec for AC-1 / AC-2: verifies that representative files touched by Teams A, B, and C now use properly named arguments instead of relying on file-level duplicate-typed-argument suppressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Allow Suppressions Canary Spec

Canary spec for AC-1 / AC-2: verifies that representative files touched by Teams A, B, and C now use properly named arguments instead of relying on file-level duplicate-typed-argument suppressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-allow-suppressions |
| Category | Testing |
| Difficulty | 1/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/allow_suppressions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Canary spec for AC-1 / AC-2: verifies that representative files touched by
Teams A, B, and C now use properly named arguments instead of relying on
file-level duplicate-typed-argument suppressions.

NOTE: These specs verify the *replacement API compiles correctly* with named
args and explicit imports. They cannot directly assert the absence of a
file-level suppression annotation — that is a grep gate executed at
phase 7-verify against the duplicate-typed-argument suppression marker.

These specs WILL FAIL until Team A/B/C land because the called functions
do not yet have named argument signatures (they still use positional arg forms
that previously required duplicate-typed-argument suppression).

## Scenarios

### AC-1/AC-2 Compiler suppression canary

#### AC-2: riscv_encode_i_type accepts named imm12 rs1 funct3 rd opcode args

- AC-2: riscv_encode_i_type accepts named imm12 rs1 funct3 rd opcode args
   - Expected: result equals `0x00100293`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: riscv_encode_i_type accepts named imm12 rs1 funct3 rd opcode args")
# After fix: function must have distinct named args — this call must
# compile without a file-level suppression in the caller or callee.
# Arrange: known I-type encoding for ADDI x5, x0, 1
val imm12  = 1
val rs1    = 0   # x0
val funct3 = 0
val rd     = 5   # x5
val opcode = 0x13  # ADDI opcode
# Act: call with explicit named args (not positional duplicate-typed)
val result = riscv_encode_i_type(imm12: imm12, rs1: rs1, funct3: funct3, rd: rd, opcode: opcode)
# Assert: ADDI x5, x0, 1  -> bits: imm[11:0]=1, rs1=0, funct3=0, rd=5, opcode=0x13
# Word = (1 << 20) | (0 << 15) | (0 << 12) | (5 << 7) | 0x13
#      = 0x00100293
expect(result).to_equal(0x00100293)
```

</details>

#### AC-2: riscv_encode_r_type accepts named funct7 rs2 rs1 funct3 rd opcode args

- AC-2: riscv_encode_r_type accepts named funct7 rs2 rs1 funct3 rd opcode args
   - Expected: result equals `0x003100B3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: riscv_encode_r_type accepts named funct7 rs2 rs1 funct3 rd opcode args")
# After fix: no duplicate-typed-argument suppression in encode_riscv32/64
# ADD x1, x2, x3: funct7=0, rs2=3, rs1=2, funct3=0, rd=1, opcode=0x33
val funct7 = 0
val rs2    = 3
val rs1    = 2
val funct3 = 0
val rd     = 1
val opcode = 0x33
val result = riscv_encode_r_type(funct7: funct7, rs2: rs2, rs1: rs1, funct3: funct3, rd: rd, opcode: opcode)
# ADD x1, x2, x3 = 0x003100B3
expect(result).to_equal(0x003100B3)
```

</details>

### AC-1/AC-2 Lib star_import suppression canary

#### AC-2: Set operations compile with explicit imports (no star_import suppression)

- AC-2: Set operations compile with explicit imports (no star_import suppression)
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: Set operations compile with explicit imports (no star_import suppression)")
# Arrange: create a set using the explicit-import path
var s = Set.new()
s.insert("a")
s.insert("b")
# Act
val found = s.has("a")
# Assert
expect(found).to_equal(true)
```

</details>

#### AC-2: Map operations compile with explicit imports (no star_import suppression)

- AC-2: Map operations compile with explicit imports (no star_import suppression)
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: Map operations compile with explicit imports (no star_import suppression)")
var m = Map.new()
m.insert("key", "value")
val found = m.has("key")
expect(found).to_equal(true)
```

</details>

### AC-1/AC-2 App suppression canary

#### AC-2: cli_dispatch_rust accepts named cmd args gc_log gc_off args

- AC-2: cli_dispatch_rust accepts named cmd args gc_log gc_off args


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: cli_dispatch_rust accepts named cmd args gc_log gc_off args")
# cli_dispatch_rust(cmd: text, args: [text], gc_log: bool, gc_off: bool)
# After fix: no suppression marker needed — args have distinct names
val cmd     = "version"
val args: [text] = []
val gc_log  = false
val gc_off  = false
val result  = cli_dispatch_rust(cmd: cmd, args: args, gc_log: gc_log, gc_off: gc_off)
# Returns exit code; 0 for success
expect(result).to_be_greater_than(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `df3be10986779ac9b32b7ba760e435862bfca8642ff8b94dc41b0ee684708e85`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df3be10986779ac9b32b7ba760e435862bfca8642ff8b94dc41b0ee684708e85`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df3be10986779ac9b32b7ba760e435862bfca8642ff8b94dc41b0ee684708e85`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/quality/code_quality/allow_suppressions_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/allow_suppressions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/allow_suppressions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/allow_suppressions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/allow_suppressions_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: riscv_encode_i_type accepts named imm12 rs1 funct3 rd opcode args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/allow_suppressions_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: riscv_encode_r_type accepts named funct7 rs2 rs1 funct3 rd opcode args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/allow_suppressions_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: Set operations compile with explicit imports (no star_import suppression)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
