# Lean Backend Specification

> Tests covering Lean backend translation core.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Backend Specification

## Scenarios

### Lean backend translation core

#### builds emitted lines with newline separators

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds emitted lines with newline separators
   - Expected: builder.build() equals `first\nsecond`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds emitted lines with newline separators")
var builder = LeanBuilder.create()
builder.emit("first")
builder.emit("second")
expect(builder.build()).to_equal("first\nsecond")
```

</details>

#### end-to-end translation

#### translates a tiny add function into a Lean let-chain returning the result

- translates a tiny add function into a Lean let-chain returning the result
   - Expected: code does not contain `sorry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("translates a tiny add function into a Lean let-chain returning the result")
val code = ok_text(translate_mir_body(add_body()))
expect(code).to_contain("let _l2 := _l0 + _l1")
expect(code).to_contain("_l2")
expect(code.contains("sorry")).to_equal(false)
```

</details>

#### preserves signedness and width in Lean type mapping

- preserves signedness and width in Lean type mapping
   - Expected: ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.I64))) equals `Int`
   - Expected: ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.I32))) equals `Int32`
   - Expected: ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.U32))) equals `UInt32`
   - Expected: ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.U8))) equals `UInt8`
   - Expected: ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.F32))) equals `Float32`
   - Expected: ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.F64))) equals `Float`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves signedness and width in Lean type mapping")
expect(ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.I64)))).to_equal("Int")
expect(ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.I32)))).to_equal("Int32")
expect(ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.U32)))).to_equal("UInt32")
expect(ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.U8)))).to_equal("UInt8")
expect(ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.F32)))).to_equal("Float32")
expect(ok_text(mir_type_to_lean(MirType(kind: MirTypeKind.F64)))).to_equal("Float")
```

</details>

#### deterministic output

#### produces byte-identical Lean for repeated translation of the same MIR

- produces byte-identical Lean for repeated translation of the same MIR
   - Expected: first != "" is true
   - Expected: first equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces byte-identical Lean for repeated translation of the same MIR")
val first = ok_text(translate_mir_body(add_body()))
val second = ok_text(translate_mir_body(add_body()))
expect(first != "").to_equal(true)
expect(first).to_equal(second)
```

</details>

#### orders functions by name regardless of input order

- orders functions by name regardless of input order
   - Expected: forward.len() equals `3`
   - Expected: forward[0].name equals `alpha`
   - Expected: forward[1].name equals `beta`
   - Expected: forward[2].name equals `gamma`
   - Expected: reversed[0].name equals `alpha`
   - Expected: reversed[1].name equals `beta`
   - Expected: reversed[2].name equals `gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders functions by name regardless of input order")
val forward = sort_mir_functions_by_name([named_fn("alpha"), named_fn("beta"), named_fn("gamma")])
val reversed = sort_mir_functions_by_name([named_fn("gamma"), named_fn("beta"), named_fn("alpha")])
expect(forward.len()).to_equal(3)
expect(forward[0].name).to_equal("alpha")
expect(forward[1].name).to_equal("beta")
expect(forward[2].name).to_equal("gamma")
expect(reversed[0].name).to_equal("alpha")
expect(reversed[1].name).to_equal("beta")
expect(reversed[2].name).to_equal("gamma")
```

</details>

#### unsupported constructs hard-fail with named errors

#### rejects a body with no basic blocks instead of emitting sorry

- rejects a body with no basic blocks instead of emitting sorry


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a body with no basic blocks instead of emitting sorry")
val empty = MirBody(name: "ghost", blocks: [], locals: [], arg_count: 0, return_ty: MirType.unit())
val msg = err_text(translate_mir_body(empty))
expect(msg).to_contain("ghost")
expect(msg).to_contain("no MIR basic blocks")
```

</details>

#### rejects unstructured goto control flow, naming the target block

- rejects unstructured goto control flow, naming the target block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects unstructured goto control flow, naming the target block")
val msg = err_text(translate_mir_body(body_with_terminator(MirTerminator.Goto(BlockId(id: 7)))))
expect(msg).to_contain("block7")
expect(msg).to_contain("structured-CFG")
```

</details>

#### rejects conditional branches that the flat translator cannot model

- rejects conditional branches that the flat translator cannot model


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects conditional branches that the flat translator cannot model")
val term = MirTerminator.If(copy_operand(0), BlockId(id: 1), BlockId(id: 2))
val msg = err_text(translate_mir_body(body_with_terminator(term)))
expect(msg).to_contain("structured-CFG")
```

</details>

#### rejects binary operators with no faithful scalar Lean operator

- rejects binary operators with no faithful scalar Lean operator
   - Expected: ok_text(translate_binop(MirBinOp.Shr)) equals `>>>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects binary operators with no faithful scalar Lean operator")
expect(err_text(translate_binop(MirBinOp.MatMul))).to_contain("binary operator")
expect(err_text(translate_binop(MirBinOp.BroadcastAdd))).to_contain("binary operator")
expect(ok_text(translate_binop(MirBinOp.Shr))).to_equal(">>>")
```

</details>

#### rejects MIR types with no faithful Lean representation

- rejects MIR types with no faithful Lean representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects MIR types with no faithful Lean representation")
val msg = err_text(mir_type_to_lean(MirType(kind: MirTypeKind.Vec4f)))
expect(msg).to_contain("no faithful Lean")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/lean_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lean backend translation core.
- Lean backend translation core

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `00306886ece67e0755345f8c821a7027e7fc87da4f86c7647bdbb6d5dd669366`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00306886ece67e0755345f8c821a7027e7fc87da4f86c7647bdbb6d5dd669366`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00306886ece67e0755345f8c821a7027e7fc87da4f86c7647bdbb6d5dd669366`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/backend/lean_backend_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/lean_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/lean_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/lean_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/lean_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/lean_backend_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds emitted lines with newline separators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/lean_backend_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates a tiny add function into a Lean let-chain returning the result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/lean_backend_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves signedness and width in Lean type mapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
