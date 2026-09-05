# Every previously-silent MIR->native backend fallback is now loud

> Lane C7 closed the silent fallbacks of `src/compiler/70.backend/**` — the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Every previously-silent MIR->native backend fallback is now loud

Lane C7 closed the silent fallbacks of `src/compiler/70.backend/**` — the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / completeness proofs |
| Status | Active |
| Plan | doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C7) |
| Design | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6 |
| Source | `test/unit/compiler/backend/backend_silent_fallback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

Lane C7 closed the silent fallbacks of `src/compiler/70.backend/**` — the
MIR -> native / LLVM / C emitters. Three instruction dispatches over
`MirInstKind` (126 variants) plus the operand and type boundaries around them
each turned "this backend cannot lower the construct" into silently wrong or
silently absent code.

As with lanes C6 and C8 this spec pins the SOURCE: for each site it asserts BOTH
that the named diagnostic is present AND that the silent shape it replaced is
gone. `bin/simple test` executes an already-deployed binary, so a behavioural
test alone would pass against reverted source.

## Sites covered

1. `MirToC.translate_instruction` — 36 `MirInstKind` variants had NO arm at all;
   each now raises a spanned `E-BACKEND-C-INST-<Variant>`, plus a terminal
   `E-BACKEND-C-INST-Unknown` carrying the observed discriminant.
2. `MirToLlvm.translate_instruction_at` — a terminal `case _: ()` SILENTLY
   DROPPED 32 variants from the emitted module; each now raises
   `E-BACKEND-LLVM-INST-<Variant>`.
3. `isel_inst_with_simd` (x86_64) — a terminal `case _:` emitted a NOP, deleting
   105 variants from the generated machine code; each now raises
   `E-BACKEND-X86ISEL-INST-<Variant>`.
4. `native/operand_utils.spl` — five accessors answered `0` for a mis-kinded
   operand. `0` is register RAX, offset 0, immediate 0 and block label 0, all
   valid values, so the miscompile was invisible. Now
   `E-BACKEND-OPERAND-<Accessor>`.
5. `CTypeMapper.map_type` — `case _: "int64_t"` silently gave vectors, scalable
   vectors, arbitrary-width Bits and Result a 64-bit integer representation.
   Real C types for the vector and Bits families; `E-BACKEND-C-TYPE-<Kind>`
   otherwise.
6. `llvm_lib_translate_expr.get_operand_value` — `case _: 0` returned a NULL
   LLVMValueRef that the C API then dereferenced. Now
   `E-BACKEND-LLVMLIB-OPERAND-NonLocal`.

## Scenarios

### C backend has no silent instruction fallback

#### raises a NAMED, spanned diagnostic through an explicit arm for unlowered MirInstKind variants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Before C7 these 36 variants had NO arm at all in translate_instruction
   - Expected: src contains `E-BACKEND-C-INST-" + "\{variant}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMP-C-BACKEND-HAS-NO-SILENT-INSTRUCTION-FALL-001
step("Before C7 these 36 variants had NO arm at all in translate_instruction")
val src = source_of(C_BACKEND)
expect(src).to_contain("me _unsupported_c_inst(variant: text, span: Span?):")
expect(src.contains("E-BACKEND-C-INST-" + "\{variant}")).to_equal(true)
expect(src).to_contain("case LoadGlobal(_, _):")
expect(src).to_contain("case StoreGlobal(_, _):")
expect(src).to_contain("case MirSimdSplat(_, _, _):")
expect(src).to_contain("case MirWarpBallot(_, _, _):")
expect(src).to_contain("self._unsupported_c_inst(\"MirWarpBallot\", inst.span)")
```

</details>

#### names the terminal wildcard with the observed discriminant

- names the terminal wildcard with the observed discriminant
- Verify: names the terminal wildcard with the observed discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the terminal wildcard with the observed discriminant")
step("Verify: names the terminal wildcard with the observed discriminant")
val src = source_of(C_BACKEND)
expect(src).to_contain("E-BACKEND-C-INST-Unknown")
expect(src).to_contain("rt_enum_discriminant(inst.kind)")
```

</details>

#### keeps Drop an EXPLICIT no-op rather than a wildcard casualty

- keeps Drop an EXPLICIT no-op rather than a wildcard casualty
- Drop is emitted by MIR lowering and legitimately has no C code effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Drop an EXPLICIT no-op rather than a wildcard casualty")
step("Drop is emitted by MIR lowering and legitimately has no C code effect")
val src = source_of(C_BACKEND)
expect(src).to_contain("case Drop(_):")
```

</details>

### LLVM text backend no longer drops instructions silently

#### replaced the terminal `case _: ()` that emitted nothing at all

- replaced the terminal `case _: ()` that emitted nothing at all
- Verify: replaced the terminal `case _: ()` that emitted nothing at all
   - Expected: count_of(src, "\n            case _: ()\n") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaced the terminal `case _: ()` that emitted nothing at all")
step("Verify: replaced the terminal `case _: ()` that emitted nothing at all")
val src = source_of(LLVM)
expect(count_of(src, "\n            case _: ()\n")).to_equal(0)
expect(src).to_contain("E-BACKEND-LLVM-INST-Unknown")
```

</details>

#### raises a NAMED, spanned diagnostic per unlowered variant

- raises a NAMED, spanned diagnostic per unlowered variant
- Verify: raises a NAMED, spanned diagnostic per unlowered variant
   - Expected: src contains `E-BACKEND-LLVM-INST-" + "\{variant}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raises a NAMED, spanned diagnostic per unlowered variant")
step("Verify: raises a NAMED, spanned diagnostic per unlowered variant")
val src = source_of(LLVM)
expect(src).to_contain("me _unsupported_llvm_inst(variant: text, span: Span?):")
expect(src.contains("E-BACKEND-LLVM-INST-" + "\{variant}")).to_equal(true)
expect(src).to_contain("self._unsupported_llvm_inst(\"MirSimdLoad\", inst.span)")
expect(src).to_contain("self._unsupported_llvm_inst(\"ScalableVecFence\", inst.span)")
```

</details>

### x86_64 instruction selection no longer deletes instructions

#### replaced the wildcard that lowered any unknown instruction to a NOP

- replaced the wildcard that lowered any unknown instruction to a NOP
- A NOP is not a refusal: the computation vanished and execution continued
   - Expected: count_of(src, "# Unsupported instruction - emit NOP") equals `0`
   - Expected: src contains `E-BACKEND-X86ISEL-INST-" + "\{variant}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaced the wildcard that lowered any unknown instruction to a NOP")
step("A NOP is not a refusal: the computation vanished and execution continued")
val src = source_of(ISEL)
expect(count_of(src, "# Unsupported instruction - emit NOP")).to_equal(0)
expect(src).to_contain("fn x86_unsupported_inst(ctx: ISelContext, variant: text, span: Span?) -> ISelInstResult:")
expect(src.contains("E-BACKEND-X86ISEL-INST-" + "\{variant}")).to_equal(true)
```

</details>

#### raises the named diagnostic for variants it cannot select

- raises the named diagnostic for variants it cannot select
- Verify: raises the named diagnostic for variants it cannot select


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raises the named diagnostic for variants it cannot select")
step("Verify: raises the named diagnostic for variants it cannot select")
val src = source_of(ISEL)
expect(src).to_contain("x86_unsupported_inst(ctx, \"Await\", inst.span)")
expect(src).to_contain("x86_unsupported_inst(ctx, \"InlineAsm\", inst.span)")
expect(src).to_contain("E-BACKEND-X86ISEL-INST-Unknown")
```

</details>

### native operand accessors refuse a mis-kinded operand

#### no accessor answers a bare 0 any more

- no accessor answers a bare 0 any more
- 0 is RAX / offset 0 / immediate 0 / label 0 — all valid, so the bug was invisible
   - Expected: count_of(src, "\n        case _: 0\n") equals `0`
   - Expected: count_of(src, "native_operand_mismatch(") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no accessor answers a bare 0 any more")
step("0 is RAX / offset 0 / immediate 0 / label 0 — all valid, so the bug was invisible")
val src = source_of(OPERANDS)
expect(count_of(src, "\n        case _: 0\n")).to_equal(0)
expect(count_of(src, "native_operand_mismatch(")).to_equal(6)
```

</details>

#### names the accessor and the expected kind

- names the accessor and the expected kind
- Verify: names the accessor and the expected kind
   - Expected: src contains `E-BACKEND-OPERAND-" + "\{accessor}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the accessor and the expected kind")
step("Verify: names the accessor and the expected kind")
val src = source_of(OPERANDS)
expect(src.contains("E-BACKEND-OPERAND-" + "\{accessor}")).to_equal(true)
expect(src).to_contain("native_operand_mismatch(\"get_phys_reg_id\", \"Reg\", op)")
expect(src).to_contain("native_operand_mismatch(\"get_imm_value\", \"Imm\", op)")
```

</details>

### C type mapper no longer answers int64_t for anything it cannot map

#### dropped the silent int64_t fallback

- dropped the silent int64_t fallback
- Verify: dropped the silent int64_t fallback
   - Expected: count_of(src, "\n            case _: \"int64_t\"\n") equals `0`
   - Expected: src contains `E-BACKEND-C-TYPE-" + "\{kind}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dropped the silent int64_t fallback")
step("Verify: dropped the silent int64_t fallback")
val src = source_of(TYPE_MAPPER)
expect(count_of(src, "\n            case _: \"int64_t\"\n")).to_equal(0)
expect(src).to_contain("fn c_backend_unsupported_type(kind: text) -> text:")
expect(src.contains("E-BACKEND-C-TYPE-" + "\{kind}")).to_equal(true)
```

</details>

#### gives the vector and Bits families a real C representation

- gives the vector and Bits families a real C representation
- Verify: gives the vector and Bits families a real C representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives the vector and Bits families a real C representation")
step("Verify: gives the vector and Bits families a real C representation")
val src = source_of(TYPE_MAPPER)
expect(src).to_contain("case Vec8f:")
expect(src).to_contain("case Vec4i:")
expect(src).to_contain("case Bits(width, signed):")
expect(src).to_contain("case Result(_, _):")
```

</details>

### llvm_lib operand lookup refuses a non-local operand

#### no longer returns a NULL LLVMValueRef as 0

- no longer returns a NULL LLVMValueRef as 0
- Verify: no longer returns a NULL LLVMValueRef as 0
   - Expected: count_of(src, "        case Move(local): get_value(value_map, local.id)\n        case _: 0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no longer returns a NULL LLVMValueRef as 0")
step("Verify: no longer returns a NULL LLVMValueRef as 0")
val src = source_of(LLVM_LIB)
expect(src).to_contain("E-BACKEND-LLVMLIB-OPERAND-NonLocal")
expect(count_of(src, "        case Move(local): get_value(value_map, local.id)\n        case _: 0")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C7)`
- **Design:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-C-BACKEND-HAS-NO-SILENT-INSTRUCTION-FALL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2e95e0d1cb722771da250166a5c04b62d01e8c15dd10b70630e6eb3ca2f79160`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2e95e0d1cb722771da250166a5c04b62d01e8c15dd10b70630e6eb3ca2f79160`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2e95e0d1cb722771da250166a5c04b62d01e8c15dd10b70630e6eb3ca2f79160`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/backend_silent_fallback_spec.spl
mirror: doc/06_spec/unit/compiler/backend/backend_silent_fallback_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/backend_silent_fallback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/backend_silent_fallback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/backend_silent_fallback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/backend_silent_fallback_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'raises a NAMED, spanned diagnostic through an explicit arm for unlowered MirInstKind variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/backend_silent_fallback_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the terminal wildcard with the observed discriminant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/backend_silent_fallback_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Drop an EXPLICIT no-op rather than a wildcard casualty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
