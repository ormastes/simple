# Isel X86 64 Specification

> Tests covering Isel X86_64 rotate intrinsic lowering, Isel X86_64 bit_bswap intrinsic lowering, Isel X86_64 Abort terminator lowering, MirBuilder terminate_abort.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Isel X86 64 Specification

## Scenarios

### Isel X86_64 rotate intrinsic lowering

#### lowers bit_rotate_left into shift-or machine ops

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers bit_rotate_left into shift-or machine ops
   - Expected: rotate_window(block) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers bit_rotate_left into shift-or machine ops")
val mach = isel_module(build_rotate_module("rol_test", "bit_rotate_left"))
val block = entry_block(mach)

expect(rotate_window(block)).to_equal([
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_IMM,
    X86_OP_AND,
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_REG,
    X86_OP_SHL,
    X86_OP_MOV_REG_IMM,
    X86_OP_SUB,
    X86_OP_AND,
    X86_OP_MOV_REG_REG,
    X86_OP_SHR,
    X86_OP_OR
])
```

</details>

#### lowers bit_rotate_right into mirrored shift-or machine ops

- lowers bit_rotate_right into mirrored shift-or machine ops
   - Expected: rotate_window(block) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers bit_rotate_right into mirrored shift-or machine ops")
val mach = isel_module(build_rotate_module("ror_test", "bit_rotate_right"))
val block = entry_block(mach)

expect(rotate_window(block)).to_equal([
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_IMM,
    X86_OP_AND,
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_REG,
    X86_OP_SHR,
    X86_OP_MOV_REG_IMM,
    X86_OP_SUB,
    X86_OP_AND,
    X86_OP_MOV_REG_REG,
    X86_OP_SHL,
    X86_OP_OR
])
```

</details>

### Isel X86_64 bit_bswap intrinsic lowering

#### lowers bit_bswap into move plus bswap

- lowers bit_bswap into move plus bswap
   - Expected: bswap_idx >= 0 is true
   - Expected: opcode_at(block, bswap_idx - 1) equals `X86_OP_MOV_REG_REG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers bit_bswap into move plus bswap")
val mach = isel_module(build_bswap_module("bswap_test"))
val block = entry_block(mach)
val bswap_idx = find_opcode(block, X86_OP_BSWAP)
expect(bswap_idx >= 0).to_equal(true)
expect(opcode_at(block, bswap_idx - 1)).to_equal(X86_OP_MOV_REG_REG)
```

</details>

### Isel X86_64 Abort terminator lowering

#### traps on Abort instead of falling through into the next block

- traps on Abort instead of falling through into the next block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on Abort instead of falling through into the next block")
val mach = isel_module(build_abort_module("abort_test"))
val block = entry_block(mach)
# INT3 must be present: Abort HALTS.
assert_true(find_opcode(block, X86_OP_INT3) >= 0)
```

</details>

#### does not lower Abort to a bare NOP

- does not lower Abort to a bare NOP


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not lower Abort to a bare NOP")
# The regression this guards: Abort falling into the trailing `case _:`
# and emitting X86_OP_NOP, which deletes the terminator entirely and
# lets control run on into the block laid out next.
val mach = isel_module(build_abort_module("abort_nop_test"))
val block = entry_block(mach)
val int3_idx = find_opcode(block, X86_OP_INT3)
val nop_idx = find_opcode(block, X86_OP_NOP)
assert_true(int3_idx >= 0)
assert_true(nop_idx < 0 or nop_idx > int3_idx)
```

</details>

### MirBuilder terminate_abort

#### marks the current block as diverging with an Abort terminator

- marks the current block as diverging with an Abort terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks the current block as diverging with an Abort terminator")
# The producer side of the same contract: `panic(msg)` lowering
# (switch_operators_calls.spl `lower_bootstrap_panic_call`) calls this
# so the panicking block DIVERGES. Before it existed there were zero
# Abort construction sites in src/**, so no block was ever marked
# non-returning and a panic left control falling through.
var b = MirBuilder.new()
val sig = MirSignature(params: [], return_type: MirType(kind: MirTypeKind.Unit), is_variadic: false)
b.begin_function(SymbolId.new(0), "panics", sig, Span(start: 0, end: 0, line: 1, col: 1))
val blk = b.new_block(Some("panic_block"))
b.switch_to_block(blk)
b.terminate_abort("explicit panic() -- diverging, must not fall through")

var saw_abort = false
var saw_message = ""
for block in b.blocks:
    if block.id.id == blk.id:
        match block.terminator:
            case Abort(message):
                saw_abort = true
                saw_message = message
            case _:
                ()
assert_true(saw_abort)
assert_contains(saw_message, "must not fall through")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/isel_x86_64_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Isel X86_64 rotate intrinsic lowering, Isel X86_64 bit_bswap intrinsic lowering, Isel X86_64 Abort terminator lowering, MirBuilder terminate_abort.
- Isel X86_64 rotate intrinsic lowering
- Isel X86_64 bit_bswap intrinsic lowering
- Isel X86_64 Abort terminator lowering
- MirBuilder terminate_abort

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `f6496916efbbff42d3c44136c62ea6fa84c622ea29cf38415a1df9b6238beea8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6496916efbbff42d3c44136c62ea6fa84c622ea29cf38415a1df9b6238beea8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6496916efbbff42d3c44136c62ea6fa84c622ea29cf38415a1df9b6238beea8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/native/isel_x86_64_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/native/isel_x86_64_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/native/isel_x86_64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/native/isel_x86_64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/native/isel_x86_64_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers bit_rotate_left into shift-or machine ops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/isel_x86_64_spec.spl:207:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers bit_rotate_right into mirrored shift-or machine ops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/isel_x86_64_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers bit_bswap into move plus bswap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
