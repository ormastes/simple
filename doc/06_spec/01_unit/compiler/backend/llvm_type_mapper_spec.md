# llvm_type_mapper_spec

> Purpose: Prove that Llvm Type Mapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llvm_type_mapper_spec

Purpose: Prove that Llvm Type Mapper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_type_mapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Llvm Type Mapper.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Llvm Type Mapper

#### maps primitive and pointer types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps primitive and pointer types
- Verify: maps primitive and pointer types
   - Expected: mapper.map_primitive(PrimitiveType.I64) equals `i64`
   - Expected: mapper.map_primitive(PrimitiveType.F32) equals `float`
   - Expected: mapper.map_primitive(PrimitiveType.Bool) equals `i1`
   - Expected: mapper.map_pointer("i64", Mutability.Mutable) equals `ptr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps primitive and pointer types")
step("Verify: maps primitive and pointer types")
# @req: REQ-COMP-LLVM-TYPE-MAPPER-001
val mapper = LlvmTypeMapper.create()

expect(mapper.map_primitive(PrimitiveType.I64)).to_equal("i64")
expect(mapper.map_primitive(PrimitiveType.F32)).to_equal("float")
expect(mapper.map_primitive(PrimitiveType.Bool)).to_equal("i1")
expect(mapper.map_pointer("i64", Mutability.Mutable)).to_equal("ptr")
```

</details>

#### maps structs arrays tuples and function signatures

- maps structs arrays tuples and function signatures
- Verify: maps structs arrays tuples and function signatures
   - Expected: mapper.map_struct([("x", MirType.i64()), ("y", MirType.f64())]) equals `{ i64, double }`
   - Expected: mapper.map_array(MirType.i64(), 3) equals `[3 x i64]`
   - Expected: mapper.map_tuple([MirType.i64(), MirType.bool()]) equals `{ i64, i1 }`
   - Expected: mapper.map_function([MirType.i64()], MirType.i64()) equals `ptr`
   - Expected: mapper.map_function_signature([MirType.i64(), MirType.i64()], MirType.i64()) equals `i64 (i64, i64)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps structs arrays tuples and function signatures")
step("Verify: maps structs arrays tuples and function signatures")
val mapper = LlvmTypeMapper.create()

expect(mapper.map_struct([("x", MirType.i64()), ("y", MirType.f64())])).to_equal("{ i64, double }")
expect(mapper.map_array(MirType.i64(), 3)).to_equal("[3 x i64]")
expect(mapper.map_tuple([MirType.i64(), MirType.bool()])).to_equal("{ i64, i1 }")
expect(mapper.map_function([MirType.i64()], MirType.i64())).to_equal("ptr")
expect(mapper.map_function_signature([MirType.i64(), MirType.i64()], MirType.i64())).to_equal("i64 (i64, i64)")
```

</details>

#### tracks target-specific pointer size and alignment

- tracks target-specific pointer size and alignment
- Verify: tracks target-specific pointer size and alignment
   - Expected: mapper32.target_bits equals `32`
   - Expected: mapper64.target_bits equals `64`
   - Expected: mapper32.size_of(ptr_ty) equals `4`
   - Expected: mapper64.size_of(ptr_ty) equals `8`
   - Expected: mapper32.align_of(ptr_ty) equals `4`
   - Expected: mapper64.align_of(ptr_ty) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks target-specific pointer size and alignment")
step("Verify: tracks target-specific pointer size and alignment")
val mapper32 = LlvmTypeMapper.create_32bit()
val mapper64 = LlvmTypeMapper.create_64bit()
val ptr_ty = MirType.ptr(MirType.i64(), false)

expect(mapper32.target_bits).to_equal(32)
expect(mapper64.target_bits).to_equal(64)
expect(mapper32.size_of(ptr_ty)).to_equal(4)
expect(mapper64.size_of(ptr_ty)).to_equal(8)
expect(mapper32.align_of(ptr_ty)).to_equal(4)
expect(mapper64.align_of(ptr_ty)).to_equal(8)
```

</details>

#### keeps named struct registrations in the context

- keeps named struct registrations in the context
- Verify: keeps named struct registrations in the context
   - Expected: ctx.get_struct("Point") equals `Some("%struct.Point")`
   - Expected: ctx.next_struct_name() equals `%struct.anon.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps named struct registrations in the context")
step("Verify: keeps named struct registrations in the context")
var ctx = LlvmContext.empty()
ctx.register_struct("Point", "%struct.Point")

expect(ctx.get_struct("Point")).to_equal(Some("%struct.Point"))
expect(ctx.get_struct("Missing")).to_be_nil()
expect(ctx.next_struct_name()).to_equal("%struct.anon.0")
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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-LLVM-TYPE-MAPPER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11628d7408e7c8a8972be89a80be7804eca5561673f1057cfffebd918fe2f740`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11628d7408e7c8a8972be89a80be7804eca5561673f1057cfffebd918fe2f740`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11628d7408e7c8a8972be89a80be7804eca5561673f1057cfffebd918fe2f740`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/llvm_type_mapper_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_type_mapper_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_type_mapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_type_mapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_type_mapper_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/llvm_type_mapper_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps primitive and pointer types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_type_mapper_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps structs arrays tuples and function signatures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_type_mapper_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks target-specific pointer size and alignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
