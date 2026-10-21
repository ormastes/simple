# CV-01 exact pure composite values — plugins.backend_lean.lean_backend

Source: `test/03_system/compiler/lean_composite_values_spec.spl`.
Requirements: CV-01 / C2 / C5 / REQ-MC-007. Status: **27 authored scenarios, all execution UNRUN**.
This source-maintained manual is not generated execution evidence. Tests, compiler checks, builds, SPipe doc generation, Lean validation and proofs are UNRUN under the authorized scope. RED is source-predicted only against prerequisite PR4021 `505343ae21f64e7d310e0d63eae8cec7f616b315`.

The tests use real retained MIR constructors and the admitted declaration planner. `cv_outputs` asserts the exact direct translator body and that same body under full/generated module export indentation. `cv_refusal` requires the concrete error from the direct translator and both public exports; any successful result fails. Publication atomicity means no successful public module result escapes a refusal; no claim is made about intermediate internal builder mutation.

## Manual scenarios

For each scenario, construct the actual MIR fixture in the folded source, perform the stated step through the production APIs, and require its literal expected output or concrete refusal. Matrix rows exercise each supplied value independently.

| Case | Observable obligation | Manual step |
|---|---|---|
| 1 | should export a typed nonempty Array constant through actual backend APIs | Construct a two-element U8 MIR array and export its exact Vector literal |
| 2 | should preserve explicit element types for empty Array constants | Export an empty I32 Vector with an explicitly typed empty Array literal |
| 3 | should export zero singleton and multiple Tuple constants with exact retained types | Preserve Unit singleton identity and ordered product representations |
| 4 | should export nested Array and Tuple constants without losing order or types | Recursively construct an Array of typed Tuple values |
| 5 | should construct Array values from genuine nominal Struct locals | Build a Packet then pass ordered local operands to an Array aggregate |
| 6 | should nest real Struct Enum and Array aggregate locals inside a Tuple | Construct an Enum payload and an Array before retaining all three tuple components |
| 7 | should construct zero singleton and multiple Tuple aggregates in source operand order | Build each Tuple arity through the actual Aggregate instruction |
| 8 | should project every Tuple component through the exact right-associated product | Select first middle final and singleton fields with exact result types |
| 9 | should route pure composite parameter returns without incidental nominal instructions | Export instruction-free Array and Tuple identities through exact typed admission |
| 10 | should copy then move pure composite locals while retaining exact type names | Consume one copied composite and return its live destination |
| 11 | should transport composite values across exclusive arms and reject a lost incoming local | Join newly defined composites while intersecting incoming liveness |
| 12 | should preserve scalar and scalar Result identity routing | Export unchanged noncomposite identities through the existing scalar translator |
| 13 | should reject composite constant kind count and leaf mismatches | Require retained Array and Tuple shape and exact scalar leaf kinds |
| 14 | should reject aggregate destination and arity mismatches | Check aggregate shape before binding any composite destination |
| 15 | should preserve signedness and reject physically boxed aggregate operands | Reject equal-width but distinct MIR element types and boxed local representations |
| 16 | should reject negative Array sizes and invalid Tuple projections | Check bounds and selected result types before any projection is published |
| 17 | should retain unsupported scalar Struct and unknown constant refusals | Reject unsupported leaves instead of inventing composite encodings |
| 18 | should reject unknown and kind-mismatched nominal elements inside composites | Resolve nested nominal references against the real declaration context |
| 19 | should consume ordered aggregate operands and projection bases exactly once | Reject repeated Move and reads after a consumed Tuple projection |
| 20 | should reject malformed composite values in either untaken branch | Validate both arms under literal conditions before publishing the module |
| 21 | should preserve Array field and pointer-operation refusals | Refuse unsupported indexing and pointer-to-value reinterpretation |
| 22 | should admit depth 128 and reject depth 129 through the actual constant exporter | Build actual nested singleton Tuple values with root depth one |
| 23 | should admit 65536 actual constant nodes and reject 65537 | Count the Array root and each retained Bool leaf through public exports |
| 24 | should share the 65536-node budget across both terminal and joining arms | Charge both branches and the literal Bool condition against one per-function budget |
| 25 | should recursively emit composite constants used as operands and returned values | Use the same typed constant admission for Return and Aggregate operands |
| 26 | should preserve existing composite-parameter call-only and Result constructor routes | Export canonical rt_array_len and typed rt_enum_new calls with their prior flat bodies |
| 27 | should refuse calls mixed with new composite operations instead of falling back | Keep Array construction and Tuple constants on the exact typed route even when a Call is present |

## Boundary and routing evidence

- Depth fixtures build actual nested singleton Tuple values: 127 wrappers plus one Bool leaf reaches depth 128; 128 wrappers reaches rejected depth 129. Root depth is one.
- Node fixtures build actual Array values: one root plus 65,535 Bool leaves reaches 65,536; one root plus 65,536 leaves reaches rejected 65,537. Their expected Vector literals contain every actual element. No internal budget helper or fabricated counter is invoked.
- Each combined-arm fixture has two Array roots and 65,532 Bool leaves, plus one literal condition and one then-arm Bool constant: exactly 65,536. Both terminal and shared-suffix forms have positive controls. An additional else, prefix, or suffix constant requires rejection at 65,537. Each arm alone is below the limit.
- Fixture builders construct inputs and literal expectations only. They do not invoke a replacement translator, evaluator, codec, or proof authority.
- Array aggregates carry their element type, not the whole Array type. Wrong metadata, equal-width I32/U32 mismatch, boxed/pointer operands, wrong destination shapes, repeated Move, and malformed untaken branches remain explicit refusals.
- Call-only composite-parameter wrappers and canonical `rt_enum_new` Result<Array> construction retain their prior flat export bodies. These compatibility assertions do not establish call or native equivalence. Actual new composite construction mixed with Call must refuse through the typed owner.

## Scope and provenance

The first real Array constant regression was frozen before production changes; immutable external snapshots retain their initial hashes. Corrected contract revision 2 pins root depth, sequential per-function budget sharing, integer Zero acceptance, unsupported constant refusal, exact Vector typing, Tuple formatting and projection terms. Contract revision 2 SHA256: `70c604dbccb1b3a1b0498344fb887364f0b569bd19393a65be5fd8510062004b`. The parent-authorized call-routing addendum SHA256 `d35927480f57542f84f1d7e43f3676e11da3a0db64ed9922b4611e2587e5666b` is exercised in the final two scenarios, including literal Array/Tuple constants hidden in Call, Ret, and If operands.

General heap semantics, Array indexing, Load/Store, mutation, calls mixed with new composite operations, recursive fixed Vectors, unions, general CFG, authenticated replay, native ABI correspondence, measured runtime performance and full C1–C7 remain OPEN. Existing source-array lowering can box elements; these specs require exact retained MIR agreement and do not guess unboxing.

<details>
<summary>Executable SSpec and reusable fixture/checker definitions — all UNRUN</summary>

```simple
# codex-system-test
# @manual: show
# @req: REQ-MC-007, C2, C5
# CV-01 frozen contract; real MIR and public exports. All execution UNRUN.
# RED is source-predicted only; manual generation and Lean compilation UNRUN.
use std.spec
use std.spec.step
use compiler.hir.hir_types.{SymbolId}
use compiler.common.attributes.{vhdl_hardware_metadata_default, DriverManifestAttr, DriverManifestAttrKind}
use compiler.common.diagnostics.span.{Span}
use compiler.mir.mir_instructions.{MirModule, MirFunction, MirBody, MirInst, MirInstKind, AggregateKind, MirBlock, BlockId, MirOperand, MirOperandKind, MirTerminator, MirBinOp, MirUnaryOp}
use compiler.mir.mir_types.{MirType, MirTypeKind, MirConstValue, MirTypeDef, MirTypeDefKind, MirFieldDef, MirVariantDef, MirSignature, MirLocal, LocalId, LocalKind}
use plugins.backend_lean.lean_backend.{LeanBackend, LeanBuilder, VerificationLevel}
use plugins.backend_lean.lean_type_declarations.{lean_plan_type_declarations}
use plugins.backend_lean.lean_nominal_body.{translate_mir_nominal_body}

fn cv_ty(kind: MirTypeKind) -> MirType: MirType(kind: kind)
fn cv_packet_ty() -> MirType: cv_ty(MirTypeKind.Struct(SymbolId(id: 7)))
fn cv_state_ty() -> MirType: cv_ty(MirTypeKind.Enum(SymbolId(id: 9)))
fn cv_copy(id: i64) -> MirOperand: MirOperand(kind: MirOperandKind.Copy(LocalId(id: id)))
fn cv_local(id: i64, type_: MirType, kind: LocalKind) -> MirLocal:
    MirLocal(id: LocalId(id: id), name: nil, type_: type_, kind: kind, is_ghost: false)
fn cv_inst(kind: MirInstKind) -> MirInst: MirInst(kind: kind, span: nil)
fn cv_ret(id: i64) -> MirTerminator: MirTerminator.Ret(Some(cv_copy(id)))

fn cv_base_function(parameters: [MirType], locals: [MirLocal], instructions: [MirInst], return_type: MirType, terminator: MirTerminator) -> MirFunction:
    MirFunction(symbol: SymbolId(id: 20), name: "compositeValue",
        signature: MirSignature(params: parameters, return_type: return_type, is_variadic: false, params_known: true),
        locals: locals,
        blocks: [MirBlock(id: BlockId(id: 0), label: nil, instructions: instructions, terminator: terminator)],
        entry_block: BlockId(id: 0), span: Span.default(), generic_params: [], is_generic_template: false,
        specialization_of: nil, type_bindings: {}, layout_phase: nil, is_kernel: false, gpu_target: "", gpu_backend_order: "", is_export_c: false,
        export_name: "", has_driver_manifest_attr: false, driver_manifest_attr: DriverManifestAttr(kind: DriverManifestAttrKind.Driver, driver_class: 0, vendor: 0, device_ids: [], version: "", abi: ""),
        has_vhdl_metadata: false, vhdl_metadata: vhdl_hardware_metadata_default(), has_fast_math: false, unroll_factor: 0, pipeline_ii: 0, memory_banks: 0, verification_contract: nil)

fn cv_module(function: MirFunction) -> MirModule:
    val packet = MirTypeDef(symbol: SymbolId(id: 7), name: "wire.Packet",
        kind: MirTypeDefKind.Struct([
            MirFieldDef(name: "byte", type_: cv_ty(MirTypeKind.U8), offset: 0, has_bits_attr: false, bits_width: 0),
            MirFieldDef(name: "count", type_: cv_ty(MirTypeKind.I32), offset: 4, has_bits_attr: false, bits_width: 0)]),
        is_export_c: false, export_name: "")
    val state = MirTypeDef(symbol: SymbolId(id: 9), name: "wire.State",
        kind: MirTypeDefKind.Enum([
            MirVariantDef(name: "Idle", discriminant: -3, payload: nil),
            MirVariantDef(name: "Packet", discriminant: 12, payload: Some(cv_packet_ty()))]),
        is_export_c: false, export_name: "")
    var functions: Dict<SymbolId, MirFunction> = {}
    functions[function.symbol] = function
    var types: Dict<SymbolId, MirTypeDef> = {}
    types[packet.symbol] = packet
    types[state.symbol] = state
    MirModule(name: "CompositeValues", functions: functions, statics: {}, constants: {}, types: types)

fn cv_block(id: i64, instructions: [MirInst], terminator: MirTerminator) -> MirBlock:
    MirBlock(id: BlockId(id: id), label: nil, instructions: instructions, terminator: terminator)

# @inline
fn cv_outputs(function: MirFunction, expected: text):
    val module = cv_module(function)
    val context = lean_plan_type_declarations(module, "Simple.CompositeValues").unwrap().context
    expect(translate_mir_nominal_body(function, context).unwrap()).to_equal(expected)
    val backend = LeanBackend.create(VerificationLevel.Contracts)
    val indented = expected.replace("\n", "\n  ")
    expect(backend.export_module(module).unwrap().lean_code).to_contain(indented)
    expect(backend.export_generated_module(module).unwrap().lean_code).to_contain(indented)

# @inline
fn cv_refusal(function: MirFunction, reason: text):
    val module = cv_module(function)
    val context = lean_plan_type_declarations(module, "Simple.CompositeValues").unwrap().context
    match translate_mir_nominal_body(function, context):
        case Err(error): expect(error.message).to_contain(reason)
        case Ok(_): assert(false)
    val backend = LeanBackend.create(VerificationLevel.Contracts)
    match backend.export_module(module):
        case Err(error): expect(error.message).to_contain(reason)
        case Ok(_): assert(false)
    match backend.export_generated_module(module):
        case Err(error): expect(error.message).to_contain(reason)
        case Ok(_): assert(false)

fn cv_constant(value: MirConstValue, type_: MirType) -> MirFunction:
    cv_base_function([], [cv_local(0, type_, LocalKind.Temp)],
        [cv_inst(MirInstKind.Const(LocalId(id: 0), value, type_))], type_, cv_ret(0))

fn cv_operand(value: MirConstValue, type_: MirType) -> MirOperand:
    MirOperand(kind: MirOperandKind.Const(value, type_))
fn cv_move(id: i64) -> MirOperand:
    MirOperand(kind: MirOperandKind.Move(LocalId(id: id)))
fn cv_callee(name: text, parameters: [MirType], return_type: MirType) -> MirOperand:
    val signature = MirSignature(params: parameters, return_type: return_type, is_variadic: false, params_known: true)
    cv_operand(MirConstValue.Str(name), cv_ty(MirTypeKind.FuncPtr(signature)))
fn cv_packet_name() -> text: "_root_.Simple.CompositeValues.__MirTypes.«wire».«Packet»"
fn cv_state_name() -> text: "_root_.Simple.CompositeValues.__MirTypes.«wire».«State»"

fn cv_identity(type_: MirType) -> MirFunction:
    cv_base_function([type_], [cv_local(0, type_, LocalKind.Arg(0))], [], type_, cv_ret(0))

# Fixture-only fixed literal builders; no production traversal or budget helper is called.
fn cv_bool_array(count: i64) -> (MirConstValue, MirType, text, text):
    var values: [MirConstValue] = []
    var literals: [text] = []
    for index in 0..count:
        values.push(MirConstValue.Bool(false))
        literals.push("false")
    val type_ = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), count))
    val name = "_root_.Vector (_root_.Bool) {count}"
    val term = "(_root_.Vector.mk (#[" + literals.join(", ") + "] : _root_.Array (_root_.Bool)) (by rfl) : " + name + ")"
    (MirConstValue.Array(values), type_, name, term)

fn cv_nested_tuple(depth: i64) -> (MirConstValue, MirType, text, text):
    var value = MirConstValue.Bool(true)
    var type_ = cv_ty(MirTypeKind.Bool)
    var name = "_root_.Bool"
    var term = "true"
    for level in 1..depth:
        value = MirConstValue.Tuple([value])
        type_ = cv_ty(MirTypeKind.Tuple([type_]))
        name = "(" + name + ")"
        term = "(" + term + ")"
    (value, type_, name, term)

fn cv_diamond(type_: MirType) -> MirFunction:
    var function = cv_base_function([cv_ty(MirTypeKind.Bool), type_],
        [cv_local(0, cv_ty(MirTypeKind.Bool), LocalKind.Arg(0)), cv_local(1, type_, LocalKind.Arg(1)), cv_local(2, type_, LocalKind.Temp)], [], type_, cv_ret(2))
    function.blocks = [
        cv_block(0, [], MirTerminator.If(cv_copy(0), BlockId(id: 1), BlockId(id: 2))),
        cv_block(1, [cv_inst(MirInstKind.Move(LocalId(id: 2), LocalId(id: 1)))], MirTerminator.Goto(BlockId(id: 3))),
        cv_block(2, [cv_inst(MirInstKind.Copy(LocalId(id: 2), LocalId(id: 1)))], MirTerminator.Goto(BlockId(id: 3))),
        cv_block(3, [], cv_ret(2))]
    function

# Two Array roots plus 65532 Bool leaves + one condition + one arm Bool = 65536.
fn cv_branch_budget(shared_suffix: bool, extra_else: bool) -> (MirFunction, text):
    val (value, type_, name, term) = cv_bool_array(32766)
    var function = cv_base_function([], [cv_local(0, type_, LocalKind.Temp),
        cv_local(1, cv_ty(MirTypeKind.Bool), LocalKind.Temp), cv_local(2, cv_ty(MirTypeKind.Bool), LocalKind.Temp),
        cv_local(3, cv_ty(MirTypeKind.Bool), LocalKind.Temp)], [], type_, cv_ret(0))
    val condition = cv_operand(MirConstValue.Bool(true), cv_ty(MirTypeKind.Bool))
    val array_inst = cv_inst(MirInstKind.Const(LocalId(id: 0), value, type_))
    val scalar_inst = cv_inst(MirInstKind.Const(LocalId(id: 1), MirConstValue.Bool(false), cv_ty(MirTypeKind.Bool)))
    function.blocks = [cv_block(0, [], MirTerminator.If(condition, BlockId(id: 1), BlockId(id: 2))),
        cv_block(1, [array_inst, scalar_inst], cv_ret(0)), cv_block(2, [array_inst], cv_ret(0))]
    if extra_else:
        function.blocks[2].instructions.push(cv_inst(MirInstKind.Const(LocalId(id: 2), MirConstValue.Bool(false), cv_ty(MirTypeKind.Bool))))
    val array_line = "let _l0 : " + name + " := " + term
    var expected = "if true then\n  " + array_line + "\n  let _l1 : _root_.Bool := false\n  _l0\nelse\n  " + array_line + "\n  _l0"
    if shared_suffix:
        function.blocks[1].terminator = MirTerminator.Goto(BlockId(id: 3))
        function.blocks[2].terminator = MirTerminator.Goto(BlockId(id: 3))
        function.blocks.push(cv_block(3, [], cv_ret(0)))
        expected = "let _l0 : " + name + " :=\n  if true then\n    " + array_line + "\n    let _l1 : _root_.Bool := false\n    _l0\n  else\n    " + array_line + "\n    _l0\n_l0"
    (function, expected)

describe "CV-01 exact pure composite values":
    it "should export a typed nonempty Array constant through actual backend APIs":
        step("Construct a two-element U8 MIR array and export its exact Vector literal")
        val type_ = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.U8), 2))
        val value = MirConstValue.Array([MirConstValue.Int(1), MirConstValue.Int(255)])
        val expected = "let _l0 : _root_.Vector (_root_.BitVec 8) 2 := (_root_.Vector.mk (#[(BitVec.ofInt 8 1), (BitVec.ofInt 8 255)] : _root_.Array (_root_.BitVec 8)) (by rfl) : _root_.Vector (_root_.BitVec 8) 2)\n_l0"
        cv_outputs(cv_constant(value, type_), expected)

    it "should preserve explicit element types for empty Array constants":
        step("Export an empty I32 Vector with an explicitly typed empty Array literal")
        val type_ = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.I32), 0))
        cv_outputs(cv_constant(MirConstValue.Array([]), type_), "let _l0 : _root_.Vector (_root_.BitVec 32) 0 := (_root_.Vector.mk (#[] : _root_.Array (_root_.BitVec 32)) (by rfl) : _root_.Vector (_root_.BitVec 32) 0)\n_l0")

    it "should export zero singleton and multiple Tuple constants with exact retained types":
        step("Preserve Unit singleton identity and ordered product representations")
        cv_outputs(cv_constant(MirConstValue.Tuple([]), cv_ty(MirTypeKind.Tuple([]))), "let _l0 : _root_.Unit := ()\n_l0")
        cv_outputs(cv_constant(MirConstValue.Tuple([MirConstValue.Bool(true)]), cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool)]))), "let _l0 : (_root_.Bool) := (true)\n_l0")
        val type_ = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.I32), cv_ty(MirTypeKind.Bool), cv_ty(MirTypeKind.U8)]))
        val value = MirConstValue.Tuple([MirConstValue.Int(-7), MirConstValue.Bool(false), MirConstValue.Zero])
        cv_outputs(cv_constant(value, type_), "let _l0 : (_root_.BitVec 32 × _root_.Bool × _root_.BitVec 8) := ((BitVec.ofInt 32 (-7)), false, (BitVec.ofInt 8 0))\n_l0")

    it "should export nested Array and Tuple constants without losing order or types":
        step("Recursively construct an Array of typed Tuple values")
        val component = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.U8), cv_ty(MirTypeKind.Bool)]))
        val type_ = cv_ty(MirTypeKind.Array(component, 2))
        val value = MirConstValue.Array([MirConstValue.Tuple([MirConstValue.Int(1), MirConstValue.Bool(true)]), MirConstValue.Tuple([MirConstValue.Int(2), MirConstValue.Bool(false)])])
        val name = "_root_.Vector ((_root_.BitVec 8 × _root_.Bool)) 2"
        val term = "(_root_.Vector.mk (#[((BitVec.ofInt 8 1), true), ((BitVec.ofInt 8 2), false)] : _root_.Array ((_root_.BitVec 8 × _root_.Bool))) (by rfl) : " + name + ")"
        cv_outputs(cv_constant(value, type_), "let _l0 : " + name + " := " + term + "\n_l0")

    it "should construct Array values from genuine nominal Struct locals":
        step("Build a Packet then pass ordered local operands to an Array aggregate")
        val type_ = cv_ty(MirTypeKind.Array(cv_packet_ty(), 2))
        val function = cv_base_function([cv_ty(MirTypeKind.U8), cv_ty(MirTypeKind.I32)],
            [cv_local(0, cv_ty(MirTypeKind.U8), LocalKind.Arg(0)), cv_local(1, cv_ty(MirTypeKind.I32), LocalKind.Arg(1)),
             cv_local(2, cv_packet_ty(), LocalKind.Temp), cv_local(3, type_, LocalKind.Temp)],
            [cv_inst(MirInstKind.Aggregate(LocalId(id: 2), AggregateKind.Struct(SymbolId(id: 7)), [cv_copy(0), cv_copy(1)])),
             cv_inst(MirInstKind.Aggregate(LocalId(id: 3), AggregateKind.Array(cv_packet_ty()), [cv_copy(2), cv_copy(2)]))], type_, cv_ret(3))
        val packet = cv_packet_name()
        val name = "_root_.Vector (" + packet + ") 2"
        val expected = "let _l2 : " + packet + " := " + packet + ".mk (_l0) (_l1)\nlet _l3 : " + name + " := (_root_.Vector.mk (#[_l2, _l2] : _root_.Array (" + packet + ")) (by rfl) : " + name + ")\n_l3"
        cv_outputs(function, expected)

    it "should nest real Struct Enum and Array aggregate locals inside a Tuple":
        step("Construct an Enum payload and an Array before retaining all three tuple components")
        val array_type = cv_ty(MirTypeKind.Array(cv_state_ty(), 1))
        val tuple_type = cv_ty(MirTypeKind.Tuple([cv_packet_ty(), cv_state_ty(), array_type]))
        val function = cv_base_function([cv_packet_ty()],
            [cv_local(0, cv_packet_ty(), LocalKind.Arg(0)), cv_local(1, cv_state_ty(), LocalKind.Temp), cv_local(2, array_type, LocalKind.Temp), cv_local(3, tuple_type, LocalKind.Temp)],
            [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), AggregateKind.Enum(SymbolId(id: 9), 12), [cv_copy(0)])),
             cv_inst(MirInstKind.Aggregate(LocalId(id: 2), AggregateKind.Array(cv_state_ty()), [cv_copy(1)])),
             cv_inst(MirInstKind.Aggregate(LocalId(id: 3), AggregateKind.Tuple, [cv_copy(0), cv_copy(1), cv_copy(2)]))], tuple_type, cv_ret(3))
        val packet = cv_packet_name()
        val state = cv_state_name()
        val array_name = "_root_.Vector (" + state + ") 1"
        val tuple_name = "(" + packet + " × " + state + " × " + array_name + ")"
        val expected = "let _l1 : " + state + " := " + state + ".«Packet» (_l0)\nlet _l2 : " + array_name + " := (_root_.Vector.mk (#[_l1] : _root_.Array (" + state + ")) (by rfl) : " + array_name + ")\nlet _l3 : " + tuple_name + " := (_l0, _l1, _l2)\n_l3"
        cv_outputs(function, expected)

    it "should construct zero singleton and multiple Tuple aggregates in source operand order":
        step("Build each Tuple arity through the actual Aggregate instruction")
        val empty = cv_ty(MirTypeKind.Tuple([]))
        cv_outputs(cv_base_function([], [cv_local(0, empty, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 0), AggregateKind.Tuple, []))], empty, cv_ret(0)), "let _l0 : _root_.Unit := ()\n_l0")
        val one = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool)]))
        cv_outputs(cv_base_function([cv_ty(MirTypeKind.Bool)], [cv_local(0, cv_ty(MirTypeKind.Bool), LocalKind.Arg(0)), cv_local(1, one, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), AggregateKind.Tuple, [cv_copy(0)]))], one, cv_ret(1)), "let _l1 : (_root_.Bool) := (_l0)\n_l1")
        val many = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool), cv_ty(MirTypeKind.U8)]))
        cv_outputs(cv_base_function([cv_ty(MirTypeKind.U8), cv_ty(MirTypeKind.Bool)], [cv_local(0, cv_ty(MirTypeKind.U8), LocalKind.Arg(0)), cv_local(1, cv_ty(MirTypeKind.Bool), LocalKind.Arg(1)), cv_local(2, many, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 2), AggregateKind.Tuple, [cv_copy(1), cv_copy(0)]))], many, cv_ret(2)), "let _l2 : (_root_.Bool × _root_.BitVec 8) := (_l1, _l0)\n_l2")

    it "should project every Tuple component through the exact right-associated product":
        step("Select first middle final and singleton fields with exact result types")
        val type_ = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool), cv_ty(MirTypeKind.U8), cv_ty(MirTypeKind.I32)]))
        for (index, selected, name, projection) in [(0, cv_ty(MirTypeKind.Bool), "_root_.Bool", "_root_.Prod.fst (_l0)"), (1, cv_ty(MirTypeKind.U8), "_root_.BitVec 8", "_root_.Prod.fst (_root_.Prod.snd (_l0))"), (2, cv_ty(MirTypeKind.I32), "_root_.BitVec 32", "_root_.Prod.snd (_root_.Prod.snd (_l0))")]:
            val function = cv_base_function([type_], [cv_local(0, type_, LocalKind.Arg(0)), cv_local(1, selected, LocalKind.Temp)], [cv_inst(MirInstKind.GetField(LocalId(id: 1), cv_move(0), index))], selected, cv_ret(1))
            cv_outputs(function, "let _l1 : " + name + " := " + projection + "\n_l1")
        val singleton = cv_ty(MirTypeKind.Tuple([cv_packet_ty()]))
        val function = cv_base_function([singleton], [cv_local(0, singleton, LocalKind.Arg(0)), cv_local(1, cv_packet_ty(), LocalKind.Temp)], [cv_inst(MirInstKind.GetField(LocalId(id: 1), cv_copy(0), 0))], cv_packet_ty(), cv_ret(1))
        cv_outputs(function, "let _l1 : " + cv_packet_name() + " := (_l0)\n_l1")

    it "should route pure composite parameter returns without incidental nominal instructions":
        step("Export instruction-free Array and Tuple identities through exact typed admission")
        for type_ in [cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.U8), 0)), cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 2)), cv_ty(MirTypeKind.Tuple([])), cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool)])), cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.I32), cv_ty(MirTypeKind.Bool)]))]:
            cv_outputs(cv_identity(type_), "_l0")

    it "should copy then move pure composite locals while retaining exact type names":
        step("Consume one copied composite and return its live destination")
        for (type_, name) in [(cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 2)), "_root_.Vector (_root_.Bool) 2"), (cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.U8), cv_ty(MirTypeKind.Bool)])), "(_root_.BitVec 8 × _root_.Bool)")]:
            val function = cv_base_function([type_], [cv_local(0, type_, LocalKind.Arg(0)), cv_local(1, type_, LocalKind.Temp), cv_local(2, type_, LocalKind.Temp)], [cv_inst(MirInstKind.Copy(LocalId(id: 1), LocalId(id: 0))), cv_inst(MirInstKind.Move(LocalId(id: 2), LocalId(id: 1)))], type_, cv_ret(2))
            cv_outputs(function, "let _l1 : " + name + " := _l0\nlet _l2 : " + name + " := _l1\n_l2")

    it "should transport composite values across exclusive arms and reject a lost incoming local":
        step("Join newly defined composites while intersecting incoming liveness")
        for (type_, name) in [(cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 2)), "_root_.Vector (_root_.Bool) 2"), (cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.U8), cv_ty(MirTypeKind.Bool)])), "(_root_.BitVec 8 × _root_.Bool)")]:
            var function = cv_diamond(type_)
            val arm = "    let _l2 : " + name + " := _l1\n    _l2"
            cv_outputs(function, "let _l2 : " + name + " :=\n  if _l0 then\n" + arm + "\n  else\n" + arm + "\n_l2")
            function.blocks[3].terminator = cv_ret(1)
            cv_refusal(function, "use before definition or after move: 1")

    it "should preserve scalar and scalar Result identity routing":
        step("Export unchanged noncomposite identities through the existing scalar translator")
        for type_ in [cv_ty(MirTypeKind.I32), cv_ty(MirTypeKind.Result(cv_ty(MirTypeKind.I32), cv_ty(MirTypeKind.I64)))]:
            cv_outputs(cv_identity(type_), "_l0")

    it "should reject composite constant kind count and leaf mismatches":
        step("Require retained Array and Tuple shape and exact scalar leaf kinds")
        val array = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 1))
        val tuple = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool)]))
        cv_refusal(cv_constant(MirConstValue.Array([]), array), "array length mismatch")
        cv_refusal(cv_constant(MirConstValue.Array([]), cv_ty(MirTypeKind.Bool)), "array constant requires Array type")
        cv_refusal(cv_constant(MirConstValue.Tuple([]), cv_ty(MirTypeKind.Bool)), "tuple constant requires Tuple type")
        cv_refusal(cv_constant(MirConstValue.Array([MirConstValue.Bool(true), MirConstValue.Bool(false)]), array), "array length mismatch")
        cv_refusal(cv_constant(MirConstValue.Tuple([]), tuple), "tuple arity mismatch")
        cv_refusal(cv_constant(MirConstValue.Tuple([MirConstValue.Bool(true), MirConstValue.Bool(false)]), tuple), "tuple arity mismatch")
        cv_refusal(cv_constant(MirConstValue.Array([MirConstValue.Bool(true)]), tuple), "array constant requires Array type")
        cv_refusal(cv_constant(MirConstValue.Tuple([MirConstValue.Bool(true)]), array), "tuple constant requires Tuple type")
        cv_refusal(cv_constant(MirConstValue.Array([MirConstValue.Int(1)]), array), "integer constant requires an exact fixed-width MIR integer type")
        cv_refusal(cv_constant(MirConstValue.Array([MirConstValue.Bool(true)]), cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.U8), 1))), "boolean constant type does not match Bool")

    it "should reject aggregate destination and arity mismatches":
        step("Check aggregate shape before binding any composite destination")
        val array = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 1))
        val tuple = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool)]))
        for (kind, reason) in [(AggregateKind.Array(cv_ty(MirTypeKind.Bool)), "array aggregate requires Array destination"), (AggregateKind.Tuple, "tuple aggregate requires Tuple destination")]:
            val scalar = cv_ty(MirTypeKind.Bool)
            cv_refusal(cv_base_function([], [cv_local(0, scalar, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 0), kind, []))], scalar, cv_ret(0)), reason)
        for (type_, kind, operands, reason) in [(array, AggregateKind.Array(cv_ty(MirTypeKind.Bool)), [], "array length mismatch"), (tuple, AggregateKind.Tuple, [], "tuple arity mismatch"), (tuple, AggregateKind.Array(cv_ty(MirTypeKind.Bool)), [cv_operand(MirConstValue.Bool(true), cv_ty(MirTypeKind.Bool))], "array aggregate requires Array destination"), (array, AggregateKind.Tuple, [cv_operand(MirConstValue.Bool(true), cv_ty(MirTypeKind.Bool))], "tuple aggregate requires Tuple destination")]:
            val function = cv_base_function([], [cv_local(0, type_, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 0), kind, operands))], type_, cv_ret(0))
            cv_refusal(function, reason)

    it "should preserve signedness and reject physically boxed aggregate operands":
        step("Reject equal-width but distinct MIR element types and boxed local representations")
        val array = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.I32), 1))
        val wrong_metadata = cv_base_function([cv_ty(MirTypeKind.I32)], [cv_local(0, cv_ty(MirTypeKind.I32), LocalKind.Arg(0)), cv_local(1, array, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), AggregateKind.Array(cv_ty(MirTypeKind.U32)), [cv_copy(0)]))], array, cv_ret(1))
        cv_refusal(wrong_metadata, "exact MIR type mismatch")
        for actual in [cv_ty(MirTypeKind.U32), cv_packet_ty()]:
            val wrong_operand = cv_base_function([actual], [cv_local(0, actual, LocalKind.Arg(0)), cv_local(1, array, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), AggregateKind.Array(cv_ty(MirTypeKind.I32)), [cv_copy(0)]))], array, cv_ret(1))
            cv_refusal(wrong_operand, "exact MIR type mismatch")
        val pointer = cv_ty(MirTypeKind.Ptr(cv_ty(MirTypeKind.I32), false))
        val boxed = cv_base_function([pointer], [cv_local(0, pointer, LocalKind.Arg(0)), cv_local(1, array, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), AggregateKind.Array(cv_ty(MirTypeKind.I32)), [cv_copy(0)]))], array, cv_ret(1))
        cv_refusal(boxed, "raw pointers require an explicit heap/capability semantics")
        val tuple = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.I32)]))
        val wrong_tuple = cv_base_function([cv_ty(MirTypeKind.U32)], [cv_local(0, cv_ty(MirTypeKind.U32), LocalKind.Arg(0)), cv_local(1, tuple, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), AggregateKind.Tuple, [cv_copy(0)]))], tuple, cv_ret(1))
        cv_refusal(wrong_tuple, "exact MIR type mismatch")

    it "should reject negative Array sizes and invalid Tuple projections":
        step("Check bounds and selected result types before any projection is published")
        cv_refusal(cv_constant(MirConstValue.Array([]), cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), -1))), "negative array length")
        for (type_, index) in [(cv_ty(MirTypeKind.Tuple([])), 0), (cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool)])), -1), (cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool)])), 1)]:
            val function = cv_base_function([type_], [cv_local(0, type_, LocalKind.Arg(0)), cv_local(1, cv_ty(MirTypeKind.Bool), LocalKind.Temp)], [cv_inst(MirInstKind.GetField(LocalId(id: 1), cv_copy(0), index))], cv_ty(MirTypeKind.Bool), cv_ret(1))
            cv_refusal(function, "tuple field index out of range")
        val tuple = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.I32)]))
        val wrong_dest = cv_base_function([tuple], [cv_local(0, tuple, LocalKind.Arg(0)), cv_local(1, cv_ty(MirTypeKind.U32), LocalKind.Temp)], [cv_inst(MirInstKind.GetField(LocalId(id: 1), cv_copy(0), 0))], cv_ty(MirTypeKind.U32), cv_ret(1))
        cv_refusal(wrong_dest, "exact MIR type mismatch")

    it "should retain unsupported scalar Struct and unknown constant refusals":
        step("Reject unsupported leaves instead of inventing composite encodings")
        val bool_tuple = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool)]))
        for (value, reason) in [(MirConstValue.Float(1.5), "floating-point constant requires an exact IEEE format model"), (MirConstValue.Str("value"), "text constant requires an exact UTF-8/runtime representation model"), (MirConstValue.Zero, "zero constant requires an exact fixed-width machine representation")]:
            cv_refusal(cv_constant(MirConstValue.Tuple([value]), bool_tuple), reason)
        cv_refusal(cv_constant(MirConstValue.Zero, bool_tuple), "zero constant requires an exact fixed-width machine representation")
        cv_refusal(cv_constant(MirConstValue.Tuple([MirConstValue.FloatLexeme("1.0")]), bool_tuple), "unsupported constant kind FloatLexeme")
        cv_refusal(cv_constant(MirConstValue.Tuple([MirConstValue.Int(65)]), cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Char)]))), "integer constant requires an exact fixed-width MIR integer type")
        cv_refusal(cv_constant(MirConstValue.Tuple([MirConstValue.Struct({})]), cv_ty(MirTypeKind.Tuple([cv_packet_ty()]))), "struct constant requires its exact emitted aggregate definition")

    it "should reject unknown and kind-mismatched nominal elements inside composites":
        step("Resolve nested nominal references against the real declaration context")
        cv_refusal(cv_identity(cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Struct(SymbolId(id: 99))), 1))), "unresolved nominal symbol 99")
        cv_refusal(cv_identity(cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Enum(SymbolId(id: 7)))]))), "nominal kind mismatch for symbol 7")

    it "should consume ordered aggregate operands and projection bases exactly once":
        step("Reject repeated Move and reads after a consumed Tuple projection")
        for (type_, kind) in [(cv_ty(MirTypeKind.Array(cv_packet_ty(), 2)), AggregateKind.Array(cv_packet_ty())), (cv_ty(MirTypeKind.Tuple([cv_packet_ty(), cv_packet_ty()])), AggregateKind.Tuple)]:
            val function = cv_base_function([cv_packet_ty()], [cv_local(0, cv_packet_ty(), LocalKind.Arg(0)), cv_local(1, type_, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), kind, [cv_move(0), cv_move(0)]))], type_, cv_ret(1))
            cv_refusal(function, "use before definition or after move: 0")
        val ordered_type = cv_ty(MirTypeKind.Array(cv_packet_ty(), 2))
        var ordered = cv_base_function([cv_packet_ty()], [cv_local(0, cv_packet_ty(), LocalKind.Arg(0)), cv_local(1, ordered_type, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), AggregateKind.Array(cv_packet_ty()), [cv_copy(0), cv_move(0)]))], ordered_type, cv_ret(1))
        val packet = cv_packet_name()
        val array_name = "_root_.Vector (" + packet + ") 2"
        cv_outputs(ordered, "let _l1 : " + array_name + " := (_root_.Vector.mk (#[_l0, _l0] : _root_.Array (" + packet + ")) (by rfl) : " + array_name + ")\n_l1")
        ordered.blocks[0].instructions = [cv_inst(MirInstKind.Aggregate(LocalId(id: 1), AggregateKind.Array(cv_packet_ty()), [cv_move(0), cv_copy(0)]))]
        cv_refusal(ordered, "use before definition or after move: 0")
        val tuple = cv_ty(MirTypeKind.Tuple([cv_ty(MirTypeKind.Bool), cv_ty(MirTypeKind.Bool)]))
        val function = cv_base_function([tuple], [cv_local(0, tuple, LocalKind.Arg(0)), cv_local(1, cv_ty(MirTypeKind.Bool), LocalKind.Temp), cv_local(2, cv_ty(MirTypeKind.Bool), LocalKind.Temp)], [cv_inst(MirInstKind.GetField(LocalId(id: 1), cv_move(0), 0)), cv_inst(MirInstKind.GetField(LocalId(id: 2), cv_copy(0), 1))], cv_ty(MirTypeKind.Bool), cv_ret(2))
        cv_refusal(function, "use before definition or after move: 0")

    it "should reject malformed composite values in either untaken branch":
        step("Validate both arms under literal conditions before publishing the module")
        val type_ = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 2))
        for (condition, index) in [(true, 2), (false, 1)]:
            var function = cv_diamond(type_)
            function.blocks[0].terminator = MirTerminator.If(cv_operand(MirConstValue.Bool(condition), cv_ty(MirTypeKind.Bool)), BlockId(id: 1), BlockId(id: 2))
            function.blocks[index].instructions = [cv_inst(MirInstKind.Const(LocalId(id: 2), MirConstValue.Array([MirConstValue.Bool(true)]), type_))]
            cv_refusal(function, "array length mismatch")

    it "should preserve Array field and pointer-operation refusals":
        step("Refuse unsupported indexing and pointer-to-value reinterpretation")
        val type_ = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 1))
        val field = cv_base_function([type_], [cv_local(0, type_, LocalKind.Arg(0)), cv_local(1, cv_ty(MirTypeKind.Bool), LocalKind.Temp)], [cv_inst(MirInstKind.GetField(LocalId(id: 1), cv_copy(0), 0))], cv_ty(MirTypeKind.Bool), cv_ret(1))
        cv_refusal(field, "field projection requires")
        val pointer = cv_base_function([type_], [cv_local(0, type_, LocalKind.Arg(0)), cv_local(1, type_, LocalKind.Temp)], [cv_inst(MirInstKind.GetElementPtr(LocalId(id: 1), cv_copy(0), []))], type_, cv_ret(1))
        cv_refusal(pointer, "unsupported instruction in pure nominal body")

    it "should admit depth 128 and reject depth 129 through the actual constant exporter":
        step("Build actual nested singleton Tuple values with root depth one")
        val (value, type_, name, term) = cv_nested_tuple(128)
        cv_outputs(cv_constant(value, type_), "let _l0 : " + name + " := " + term + "\n_l0")
        val (too_deep, deep_type, _, _) = cv_nested_tuple(129)
        cv_refusal(cv_constant(too_deep, deep_type), "constant nesting limit")

    it "should admit 65536 actual constant nodes and reject 65537":
        step("Count the Array root and each retained Bool leaf through public exports")
        val (value, type_, name, term) = cv_bool_array(65535)
        cv_outputs(cv_constant(value, type_), "let _l0 : " + name + " := " + term + "\n_l0")
        val (too_many, large_type, _, _) = cv_bool_array(65536)
        cv_refusal(cv_constant(too_many, large_type), "constant node budget")

    it "should share the 65536-node budget across both terminal and joining arms":
        step("Charge both branches and the literal Bool condition against one per-function budget")
        for shared_suffix in [false, true]:
            val (function, expected) = cv_branch_budget(shared_suffix, false)
            cv_outputs(function, expected)
            val (too_many, _) = cv_branch_budget(shared_suffix, true)
            cv_refusal(too_many, "constant node budget")
            var prefixed = function
            prefixed.blocks[0].instructions = [cv_inst(MirInstKind.Const(LocalId(id: 3), MirConstValue.Bool(false), cv_ty(MirTypeKind.Bool)))]
            cv_refusal(prefixed, "constant node budget")
        val (suffix_function, _) = cv_branch_budget(true, false)
        var suffix_extra = suffix_function
        suffix_extra.blocks[3].instructions = [cv_inst(MirInstKind.Const(LocalId(id: 3), MirConstValue.Bool(false), cv_ty(MirTypeKind.Bool)))]
        cv_refusal(suffix_extra, "constant node budget")

    it "should recursively emit composite constants used as operands and returned values":
        step("Use the same typed constant admission for Return and Aggregate operands")
        val type_ = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 0))
        val value = MirConstValue.Array([])
        val term = "(_root_.Vector.mk (#[] : _root_.Array (_root_.Bool)) (by rfl) : _root_.Vector (_root_.Bool) 0)"
        cv_outputs(cv_base_function([], [], [], type_, MirTerminator.Ret(Some(cv_operand(value, type_)))), term)
        val tuple = cv_ty(MirTypeKind.Tuple([type_, cv_ty(MirTypeKind.Bool)]))
        val function = cv_base_function([], [cv_local(0, tuple, LocalKind.Temp)], [cv_inst(MirInstKind.Aggregate(LocalId(id: 0), AggregateKind.Tuple, [cv_operand(value, type_), cv_operand(MirConstValue.Bool(true), cv_ty(MirTypeKind.Bool))]))], tuple, cv_ret(0))
        cv_outputs(function, "let _l0 : (_root_.Vector (_root_.Bool) 0 × _root_.Bool) := (" + term + ", true)\n_l0")

    it "should preserve existing composite-parameter call-only and Result constructor routes":
        step("Export canonical rt_array_len and typed rt_enum_new calls with their prior flat bodies")
        val array = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 2))
        val integer = cv_ty(MirTypeKind.I64)
        val call = cv_inst(MirInstKind.Call(Some(LocalId(id: 1)), cv_callee("rt_array_len", [array], integer), [cv_copy(0)]))
        val wrapper = cv_base_function([array], [cv_local(0, array, LocalKind.Arg(0)), cv_local(1, integer, LocalKind.Temp)], [call], integer, cv_ret(1))
        cv_outputs(wrapper, "let _l1 := rt_array_len _l0\n_l1")
        val result = cv_ty(MirTypeKind.Result(array, cv_ty(MirTypeKind.I32)))
        val tag_type = cv_ty(MirTypeKind.I32)
        val constructor = cv_inst(MirInstKind.Call(Some(LocalId(id: 1)), cv_callee("rt_enum_new", [tag_type, tag_type, array], result), [cv_operand(MirConstValue.Int(0), tag_type), cv_operand(MirConstValue.Int(0), tag_type), cv_copy(0)]))
        val result_function = cv_base_function([array], [cv_local(0, array, LocalKind.Arg(0)), cv_local(1, result, LocalKind.Temp)], [constructor], result, cv_ret(1))
        cv_outputs(result_function, "let _l1 := Except.ok _l0\n_l1")

    it "should refuse calls mixed with new composite operations instead of falling back":
        step("Keep Array construction and Tuple constants on the exact typed route even when a Call is present")
        val array = cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 2))
        val integer = cv_ty(MirTypeKind.I64)
        val call = cv_inst(MirInstKind.Call(Some(LocalId(id: 1)), cv_callee("rt_array_len", [array], integer), [cv_copy(0)]))
        var aggregate = cv_base_function([array], [cv_local(0, array, LocalKind.Arg(0)), cv_local(1, integer, LocalKind.Temp), cv_local(2, array, LocalKind.Temp)], [call, cv_inst(MirInstKind.Aggregate(LocalId(id: 2), AggregateKind.Array(cv_ty(MirTypeKind.Bool)), [cv_operand(MirConstValue.Bool(true), cv_ty(MirTypeKind.Bool)), cv_operand(MirConstValue.Bool(false), cv_ty(MirTypeKind.Bool))]))], integer, cv_ret(1))
        cv_refusal(aggregate, "unsupported instruction in pure nominal body")
        val tuple = cv_ty(MirTypeKind.Tuple([]))
        val constant = cv_base_function([array], [cv_local(0, array, LocalKind.Arg(0)), cv_local(1, integer, LocalKind.Temp), cv_local(2, tuple, LocalKind.Temp)], [call, cv_inst(MirInstKind.Const(LocalId(id: 2), MirConstValue.Tuple([]), tuple))], integer, cv_ret(1))
        cv_refusal(constant, "unsupported instruction in pure nominal body")

        for (value, type_, reason) in [(MirConstValue.Array([]), cv_ty(MirTypeKind.Array(cv_ty(MirTypeKind.Bool), 0)), "array constant requires Array type"), (MirConstValue.Tuple([]), cv_ty(MirTypeKind.Tuple([])), "tuple constant requires Tuple type")]:
            val tag = cv_ty(MirTypeKind.I32)
            val result = cv_ty(MirTypeKind.Result(type_, tag))
            val constructor = cv_inst(MirInstKind.Call(Some(LocalId(id: 0)), cv_callee("rt_enum_new", [tag, tag, type_], result), [cv_operand(MirConstValue.Int(0), tag), cv_operand(MirConstValue.Int(0), tag), cv_operand(value, type_)]))
            cv_refusal(cv_base_function([], [cv_local(0, result, LocalKind.Temp)], [constructor], result, cv_ret(0)), "unsupported instruction in pure nominal body")
            val boolean = cv_ty(MirTypeKind.Bool)
            val malformed = cv_operand(value, boolean)
            cv_refusal(cv_base_function([], [], [], boolean, MirTerminator.Ret(Some(malformed))), reason)
            var conditional = cv_base_function([], [], [], boolean, MirTerminator.Ret(Some(cv_operand(MirConstValue.Bool(true), boolean))))
            conditional.blocks = [cv_block(0, [], MirTerminator.If(malformed, BlockId(id: 1), BlockId(id: 2))),
                cv_block(1, [], MirTerminator.Ret(Some(cv_operand(MirConstValue.Bool(true), boolean)))),
                cv_block(2, [], MirTerminator.Ret(Some(cv_operand(MirConstValue.Bool(false), boolean))))]
            cv_refusal(conditional, reason)
```

</details>
