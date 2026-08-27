# Every previously-silent MIR-interpreter fallback is now loud

> Lane C8 closed the silent fallbacks of the tree-walk MIR interpreter

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Every previously-silent MIR-interpreter fallback is now loud

Lane C8 closed the silent fallbacks of the tree-walk MIR interpreter

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / completeness proofs |
| Status | Active |
| Plan | doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C8) |
| Design | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6 |
| Source | `test/01_unit/compiler/interp/mir_interp_silent_fallback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

Lane C8 closed the silent fallbacks of the tree-walk MIR interpreter
(`src/compiler/95.interp/`). The interpreter walks MIR, so its expression /
statement boundaries are `MirInstKind` (instructions) and `MirTerminator`
(control flow), plus the value-side enums `MirConstValue`, `MirBinOp`,
`MirUnaryOp` and `LocalKind`.

As with lane C6 this spec pins the SOURCE: for each site it asserts both that
the named diagnostic is present and that the silent shape it replaced is gone.
A `bin/simple test` run executes the already-deployed binary, so a behavioural
test alone would pass against reverted source.

## Sites covered

1. `execute_instruction`'s terminal `case _:` reported every one of 87 missing
   `MirInstKind` arms as the unnamed "unknown instruction". Each variant now has
   an explicit arm raising `E-INTERP-INST-<Variant>` with the instruction span;
   the wildcard that remains raises `E-INTERP-INST-Unknown` with the observed
   discriminant. Five pre-existing arms with unnamed messages (transfer/freeze/
   snapshot/commit) now go through the same helper.
2. `get_operand` returned 0 for aggregate/string constants ("stub for complex
   constants") -- now materialises them via `_eval_const`, like `execute_const`.
3. `_eval_const`'s `case _: 0` -> `E-INTERP-CONST-Unknown`.
4. `execute_binop`'s "unknown binop" -> `E-INTERP-BINOP-Unknown` (all 23 ops
   have arms; the wildcard is a stale-guard).
5. `execute_unaryop` `Transpose` was an identity stub -> `E-INTERP-UNOP-Transpose`.
6. `_execute_intrinsic`: unknown names returned 0 -> `E-INTERP-INTRINSIC-Unknown`;
   under-supplied operands returned 0 -> `E-INTERP-INTRINSIC-Arity`. Both are
   deferred through `last_error` and raised by the `Intrinsic` arm.
7. `mir_interp_call_runtime_fn`'s `case _: 0` -> `E-INTERP-RUNTIME-Unknown`.
8. `LocalKind` binding wildcard `case _: pass` -> explicit Var/Temp/Return arms.

## Scenarios

### MIR interpreter has no silent instruction fallback

#### raises a NAMED, spanned diagnostic through an explicit arm for unexecuted MirInstKind variants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- raises a NAMED, spanned diagnostic through an explicit arm for unexecuted MirInstKind variants
- Before C8 all of these reached `case _:` and were reported as 'unknown instruction'
   - Expected: src contains `E-INTERP-INST-" + "\{variant}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("raises a NAMED, spanned diagnostic through an explicit arm for unexecuted MirInstKind variants")
step("Before C8 all of these reached `case _:` and were reported as 'unknown instruction'")
val src = source_of(INTERP)
expect(src).to_contain("me _unsupported_inst(variant: text, span: Span?) -> InterpError?:")
expect(src.contains("E-INTERP-INST-" + "\{variant}")).to_equal(true)
expect(src).to_contain("case InlineAsm(_, _, _, _, _, _, _):")
expect(src).to_contain("self._unsupported_inst(\"InlineAsm\", inst.span)")
expect(src).to_contain("case LoadGlobal(_, _):")
expect(src).to_contain("case StoreGlobal(_, _):")
expect(src).to_contain("case GpuLaunch(_):")
expect(src).to_contain("case MirSimdLoad(_, _, _, _):")
expect(src).to_contain("case VhdlProcess(_, _):")
expect(src).to_contain("case ResultMatchSemantic(_, _, _, _, _, _, _):")
```

</details>

#### covers every variant of the registry universe with a named arm

- covers every variant of the registry universe with a named arm
- 87 formerly-wildcard variants + 5 renamed arms = 92 helper call sites
   - Expected: count_of(src, "self._unsupported_inst(\"") equals `92`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("covers every variant of the registry universe with a named arm")
step("87 formerly-wildcard variants + 5 renamed arms = 92 helper call sites")
val src = source_of(INTERP)
expect(count_of(src, "self._unsupported_inst(\"")).to_equal(92)
```

</details>

#### names the formerly-unnamed transfer/freeze/snapshot/commit refusals

- names the formerly-unnamed transfer/freeze/snapshot/commit refusals
   - Expected: src does not contain `op: "transfer envelope"`
   - Expected: src does not contain `op: "snapshot"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the formerly-unnamed transfer/freeze/snapshot/commit refusals")
val src = source_of(INTERP)
expect(src).to_contain("self._unsupported_inst(\"TransferOut\", inst.span)")
expect(src).to_contain("self._unsupported_inst(\"TransferIn\", inst.span)")
expect(src).to_contain("self._unsupported_inst(\"FreezeRegion\", inst.span)")
expect(src).to_contain("self._unsupported_inst(\"AcquireSnapshot\", inst.span)")
expect(src).to_contain("self._unsupported_inst(\"CommitUpdates\", inst.span)")
expect(src.contains("op: \"transfer envelope\"")).to_equal(false)
expect(src.contains("op: \"snapshot\"")).to_equal(false)
```

</details>

#### keeps a terminal wildcard only as a LOUD stale-guard carrying the discriminant

- keeps a terminal wildcard only as a LOUD stale-guard carrying the discriminant
   - Expected: src does not contain `op: "unknown instruction"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a terminal wildcard only as a LOUD stale-guard carrying the discriminant")
val src = source_of(INTERP)
expect(src).to_contain("E-INTERP-INST-Unknown")
expect(src).to_contain("val unknown_inst_disc = rt_enum_discriminant(inst.kind)")
expect(src.contains("op: \"unknown instruction\"")).to_equal(false)
```

</details>

### MIR interpreter has no silent value fallback

#### materialises aggregate/string operand constants instead of reading 0

- materialises aggregate/string operand constants instead of reading 0
   - Expected: src does not contain `case _: 0  # Stub for complex constants`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("materialises aggregate/string operand constants instead of reading 0")
val src = source_of(INTERP)
expect(src.contains("case _: 0  # Stub for complex constants")).to_equal(false)
expect(src).to_contain("case _: self._eval_const(value)")
```

</details>

#### names an unknown constant kind

- names an unknown constant kind
   - Expected: src does not contain `case Zero: 0\n            case _: 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names an unknown constant kind")
val src = source_of(INTERP)
expect(src).to_contain("E-INTERP-CONST-Unknown")
expect(src.contains("case Zero: 0\n            case _: 0")).to_equal(false)
```

</details>

#### names an unknown binop and the unexecuted Transpose

- names an unknown binop and the unexecuted Transpose
   - Expected: src does not contain `op: "unknown binop"`
   - Expected: src does not contain `# Stub: Transpose needs matrix support`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names an unknown binop and the unexecuted Transpose")
val src = source_of(INTERP)
expect(src).to_contain("E-INTERP-BINOP-Unknown")
expect(src.contains("op: \"unknown binop\"")).to_equal(false)
expect(src).to_contain("E-INTERP-UNOP-Transpose")
expect(src.contains("# Stub: Transpose needs matrix support")).to_equal(false)
```

</details>

#### names unknown and under-supplied intrinsics and raises them from the Intrinsic arm

- names unknown and under-supplied intrinsics and raises them from the Intrinsic arm
   - Expected: src does not contain `# Unknown intrinsic - return 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names unknown and under-supplied intrinsics and raises them from the Intrinsic arm")
val src = source_of(INTERP)
expect(src).to_contain("E-INTERP-INTRINSIC-Unknown")
expect(src).to_contain("E-INTERP-INTRINSIC-Arity")
expect(src).to_contain("me _intrinsic_arity_error(name: text, got: i64) -> i64:")
expect(src).to_contain("val intrinsic_err = self.last_error")
expect(src).to_contain("val const_err = self.last_error")
expect(src.contains("# Unknown intrinsic - return 0")).to_equal(false)
```

</details>

#### binds every LocalKind explicitly when initialising a callee frame

- binds every LocalKind explicitly when initialising a callee frame
   - Expected: src does not contain `case _: pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds every LocalKind explicitly when initialising a callee frame")
val src = source_of(INTERP)
expect(src).to_contain("case Var: pass")
expect(src).to_contain("case Temp: pass")
expect(src).to_contain("case Return: pass")
expect(src.contains("case _: pass")).to_equal(false)
```

</details>

#### names an unknown runtime hook instead of answering 0

- names an unknown runtime hook instead of answering 0
   - Expected: src does not contain `case _:\n            0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names an unknown runtime hook instead of answering 0")
val src = source_of(RUNTIME)
expect(src).to_contain("E-INTERP-RUNTIME-Unknown")
expect(src.contains("case _:\n            0")).to_equal(false)
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


## Related Documentation

- **Plan:** `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md (lane C8)`
- **Design:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md sections 11.3-11.6`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `71726e98056039674c467c1a14471928c53e78636087b88f3a2eeca6f02113f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71726e98056039674c467c1a14471928c53e78636087b88f3a2eeca6f02113f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71726e98056039674c467c1a14471928c53e78636087b88f3a2eeca6f02113f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/interp/mir_interp_silent_fallback_spec.spl
mirror: doc/06_spec/01_unit/compiler/interp/mir_interp_silent_fallback_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interp/mir_interp_silent_fallback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interp/mir_interp_silent_fallback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interp/mir_interp_silent_fallback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interp/mir_interp_silent_fallback_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'raises a NAMED, spanned diagnostic through an explicit arm for unexecuted MirInstKind variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interp/mir_interp_silent_fallback_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers every variant of the registry universe with a named arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interp/mir_interp_silent_fallback_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the formerly-unnamed transfer/freeze/snapshot/commit refusals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
