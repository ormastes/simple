# Allow Suppressions Canary Spec

> Canary spec for AC-1 / AC-2: verifies that representative files touched by Teams A, B, and C now use properly named arguments instead of relying on file-level duplicate-typed-argument suppressions.

<!-- sdn-diagram:id=allow_suppressions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=allow_suppressions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

allow_suppressions_spec -> std
allow_suppressions_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=allow_suppressions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var s = Set new
2. s insert
3. s insert
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var m = Map new
2. m insert
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = Map.new()
m.insert("key", "value")
val found = m.has("key")
expect(found).to_equal(true)
```

</details>

### AC-1/AC-2 App suppression canary

#### AC-2: cli_dispatch_rust accepts named cmd args gc_log gc_off args

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
