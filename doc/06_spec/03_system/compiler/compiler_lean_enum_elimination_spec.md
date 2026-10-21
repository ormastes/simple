# EE-01 named enum elimination — compiler.backend.backend.lean_backend

Source: `test/03_system/compiler/compiler_lean_enum_elimination_spec.spl`.
Requirements: EE-01 / C2 / REQ-MC-007. **35 authored scenarios; all execution UNRUN.**
This is a source-maintained manual, not generated or executed evidence. Compiler, native, SPipe docgen, Lean, proofs and measured performance are UNRUN. RED is source-predicted only. Positive failures are never skipped: real producer and public exporter Results are unwrapped, so any unexpected Err fails the scenario.

## Production route and ownership

Every named-enum fixture begins with `parse_full_frontend`, `HirLowering` with invocation-local `preserve_enum_semantic_arms_v1 = true`, an explicit target from `mir_target_context_from`, and `lower_module_with_enum_semantics_v1`. For valid source, both public full/generated APIs of this backend owner consume the resulting real module. Non-total source is refused by the producer before any module is returned; `ee_source_refusal` requires the exact EE diagnostic prefix and unchanged HIR serialization. The first fixture uses `ee_enum.spl`, a two-constructor Flag, and exact i32 result terms 11 and 22; it was frozen externally before parent production changes.

Metadata mutations alter actual returned records and actual MIR sites/blocks. `ee_root_call_site` selects exactly one actual `PatternInstruction` by call opcode, exact helper name, scrutinee operand, instruction region and (for payload) retained root node. No obsolete site-kind selection or incidental numeric offset substitutes for that bound operation. There is no hand-built success witness, alternate codec, fake lowering or proof runner. `ee_rehash` changes only the public canonical subject hash for adversarial structural-validation tests; the explicit unknown-adapter structural control additionally updates the affected site identity using the actual instruction serializer; it does not authenticate data or invoke a compiler finalizer. Both refusal exports require the specified error family or inherited typed-body diagnostic and leave the public input serialization unchanged. A successful public result on a negative path fails; internal builder transactionality is not asserted.

## Manual scenarios

Each row constructs the source or mutates the actual producer output as shown below, then checks the specified concrete result through the real APIs.

| Case | Observable obligation | Manual step |
|---|---|---|
| 1 | should export actual frontend nullary enum elimination without runtime carrier helpers | Parse and lower a two-variant Flag match for an explicit target and export both Lean modules |
| 2 | should bind a single variant payload using its exact declared semantic type | Lower a one-variant Box and retain the actual bound payload local |
| 3 | should eliminate multiple variants and every finite tuple payload partition | Cover nullary scalar and tuple payload alternatives without a default |
| 4 | should eliminate a single tuple-valued variant field and require its complete Bool partition | Retain one declared tuple slot and cover all four nested tuple patterns |
| 5 | should prove nested enum payload partitions and reject the missing inner constructor | Specialize the actual inner constructor set instead of treating outer coverage as total |
| 6 | should stop unfolding recursive payloads beneath wildcard patterns | Eliminate a recursive enum while leaving its wildcard tail uninterpreted |
| 7 | should use exact declared discriminants without assuming sequential tags | Capture and eliminate explicit discriminants seven and forty-two |
| 8 | should preserve repeated guarded variants and unconditional fallback order | Evaluate a guard only after its pattern and retain the next matching arm |
| 9 | should preserve each expanded Or guard and its actual false successor | Keep overlapping alternatives distinct even when they share a source body |
| 10 | should expand nested Or inside an enum payload without changing source arm identity | Lower two nested constructor alternatives and retain each actual guard retry continuation |
| 11 | should expand nested Or through a single tuple field in lexical product order | Lower the four Bool product alternatives and preserve original arm identity and guard fallthrough |
| 12 | should lower nested matches with separate preorder match identities | Retain the inner match and selected outer payload without a global registry |
| 13 | should preserve outer locals common result flow and reordered physical blocks | Follow stable block identities while retaining a shared post-match computation |
| 14 | should distinguish full Bool payload coverage from outer-variant coverage | Accept true and false together and reject either missing payload partition |
| 15 | should preserve complementary residuals under overlapping Or alternatives | Reject duplicated true coverage until an unguarded false alternative exists |
| 16 | should require an unconditional residual cover even after a literal true guard | Treat guarded rows as potentially falling through and preserve the real fallback |
| 17 | should retain an integer other-value residual until a wildcard or binder covers it | Keep integer payload reasoning symbolic rather than enumerating its domain |
| 18 | should carry consumed guard state onto false successors without resurrecting locals | Append an actual guard Move and distinguish unused from subsequently read input |
| 19 | should consume live Drop once and retain assignment history after it | Append ordinary Drop operations to actual guard MIR and distinguish dead reads from redefinitions |
| 20 | should refuse dropped enum metadata instead of recognizing runtime helper names as authority | Remove only the actual producer metadata and require both public exports to fail |
| 21 | should reject stale body and signature subjects before emitting a module | Mutate actual retained MIR while leaving its recorded subject identity stale |
| 22 | should reject stale declaration identities and same-name metadata from another module | Keep enum authority bound to the exact declaration owner and payload table |
| 23 | should reject relocated duplicate and modified actual semantic sites after public rehashing | Show that a matching public subject hash cannot authorize corrupt producer sites |
| 24 | should reject cyclic pattern references changed discriminants and mismatched expected types | Validate actual flat pattern nodes structurally instead of trusting their serialized identity |
| 25 | should reject a guard false edge that skips the next expanded alternative | Change the first real guard edge and reject it both before and after updating the public hash |
| 26 | should reject a deleted fallback cyclic edge duplicate block or disconnected block | Invalidate actual retained graph structure without fabricating replacement metadata |
| 27 | should reject invalid Or binding names and unequal declared binding types at the actual frontend | Preserve existing source binding rules before any semantic export is attempted |
| 28 | should publish no partial module after a valid match followed by a residual failure and preserve source ownership | Lower one HIR module then reject its later match without mutating HIR or SymbolTable |
| 29 | should preserve ordinary physical function bytes and types when opting into enum capture | Lower the same source with ordinary and opted HIR policies and compare every original physical function |
| 30 | should isolate repeated lowering invocations and explicit target contexts | Capture fresh metadata for the same source under two explicit targets |
| 31 | should separate representative recursive source acceptance from the syntactic depth limit | Export a depth-eight constructor pattern and refuse a source pattern above height 128 |
| 32 | should enforce the observed symbolic-work boundary using actual produced patterns | Measure production-checker work and test exactly sufficient and one-less budgets |
| 33 | should preserve the existing Result-specific elimination route | Lower actual Result Ok and Err patterns without replacing their established witness |
| 34 | should preserve guard assignment history and refuse false-successor redefinition | Add an ordinary local definition before a false guard and reject assigning it again later |
| 35 | should reject altered payload slot types and unknown bound adapter operations | Select the actual payload call and distinguish stale site hashes from structural adapter refusal |

## Discriminating oracles

- Positive semantic fragments require qualified constructor uses, exact fixed-width scalar terms, declared payload types, and frozen match/arm continuation names. The Flag controls scope 11 and 22 to their specific body continuation definitions, so swapping results cannot satisfy them. Raw `rt_enum_discriminant` and `rt_enum_payload` calls cannot remain in either export.
- Top-level and nested Or guards retain separate capture entries, alternative indexes and false successors while alternatives from one source arm retain the same original arm ID. Nested Or below an enum payload must retain the two inner constructors; Or through a single tuple field must expand in TT, TF, FT, FF product order. Every expanded alternative scopes result 11 to its body; both pattern and guard failure entries must equal the next actual expanded pattern entry, and the emitted false callback must call that exact block. The source fallback retains result 22 and its own source-arm ID. A sibling mutates actual retained HIR so two original arms and their root patterns have equal spans; the producer must still retain original arm positions, not infer them from spans. Each captured failure is checked against the actual guard terminator; within each emitted guard continuation, consecutive trimmed `else` and exact `ee_b{id}` call lines must target that failure block. Guard Move and definition-history fixtures append ordinary instructions after existing captured instruction positions. A both-arm definition is the positive control for an otherwise identical one-arm-only merge read. A public rehash cannot restore availability or erase prior definitions.
- Payload semantic-type corruption, subject-only unknown-adapter mutation, and subject-plus-site-resealed unknown-adapter mutation are separate controls. They require respectively the pattern-type error, stale actual instruction identity error, and physical unknown native adapter error. Updating public hashes cannot authorize a structurally unsupported call.
- The single declared tuple field `Wrap((bool, bool))` must capture one variant child with a two-element Tuple pattern, distinct from the two declared fields in `Pair(bool, bool)`. Its four result terms are scoped to four actual arm bodies. Removing the final Bool partition must return a producer residual error.
- Drop checks append ordinary instructions after captured guard sites, then update only the public subject hash. One live Drop exports successfully; a second Drop, a subsequent Copy read, and redefining the dropped argument each require their distinct inherited typed-body diagnostic through both APIs. The redefinition fixture first saves a live same-type copy, ensuring its failure concerns definition history.
- Bool, nested-enum and tuple payload partitions must cover their full residuals. Outer variant coverage, duplicated Or overlap and guarded rows—including literal true guards—cannot discharge an uncovered payload case. Integer literals leave a symbolic other-value residual until a wildcard/binder covers it.
- The valid-prefix/later-residual fixture checks producer Err directly and independently exports its valid prefix. Source ownership checks compare full HIR codec snapshots (required nonempty), SymbolTable counters, retained module serialization and fresh invocation match IDs. Separate target contexts are supplied explicitly; these are not native target execution claims.
- Ordinary/opted physical parity parses the same source into separate HIR modules with the ordinary default-false and opted true arm-preservation policies. It uses the same explicit target, independent `verification_source_environment_v1` clones, and ordinary `MirLowering.new_for_target` with ambient bootstrap policy disabled. Every original function must retain exact canonical subject bytes (omitting enum metadata through the actual serializer), signature serialization and local IDs/types. Two nominal owners cover already-supported nullary and scalar payload matches; newly admitted nested tuple patterns are explicitly excluded. Both original HIR serializations include their SymbolTables and must remain unchanged, with explicit opted symbol/scope counter checks. Both backend exports consume the opted result.
- Depth fixtures export a representative actual recursive source pattern at height 8 and reject height 129 above the syntactic limit with a fallback. Syntactic height and cumulative symbolic work are distinct bounds; this suite does not claim every height-128 constructor pattern fits the work budget. The separately owned residual component fixture uses the actual decision API and a singleton-Or ladder to check height 128 success and 129 refusal without long value-path work. The totality-budget fixture calls the production checker using real producer patterns, derives consumed work from its returned remaining budget, then tests exactly sufficient and one-less budgets. No test-maintained traversal counter or claimed measured allocation is involved. This is not a claim that a whole exported function consumes exactly 65,536 work units.

## Scope and remaining evidence

The approved contract and focused oracle plan live under the external EE packet's `contract-revision2/` directory. This suite preserves the existing Result-specific route with both a Result-only module and a mixed named-enum/Result module; only the named match receives enum metadata. Capture/schema/CLI work and independent implementation qualification belong to their separate owners.

Full C1–C7, authenticated source/native equivalence, heap/mutation/loops, unrelated calls, recursive fixed Vectors, unions and measured costs remain OPEN. Physical box/unbox correctness is not proven by semantic metadata. No runtime result, Lean kernel acceptance, production source GO or completed formal proof is claimed.

<details>
<summary>Executable SSpec and real frontend/mutation helpers — UNRUN</summary>

```simple
# codex-system-test
# @manual: show
# @req: EE-01, REQ-MC-007, C2
# Real frontend -> target-specific producer -> both public Lean APIs.
# All execution and doc generation UNRUN; RED is source-predicted only.
use std.spec
use std.spec.step
use std.common.crypto.sha256.{sha256_text}
use compiler.common.config.{Logger}
use compiler.common.mir_target_context.{mir_target_context_from}
use compiler.frontend.frontend.{parse_full_frontend}
use compiler.hir.hir_lowering.types.{HirLowering}
use compiler.hir.hir_lowering.items.*
use compiler.hir.hir_codec.{hir_module_encode}
use compiler.hir.hir_types.{HirModule, SymbolId}
use compiler.hir.hir_definitions.{HirExprKind}
use compiler.mir.mir_instructions.{MirModule, MirFunction, MirBlock, BlockId, MirInst, MirInstKind, MirOperand, MirOperandKind, MirTerminator}
use compiler.mir.mir_types.{MirType, MirTypeKind, MirConstValue, MirTypeDefKind, LocalId, MirLocal, LocalKind}
use compiler.mir.mir_json.{serialize_mir_module, serialize_mir_function_subject_v1, serialize_mir_signature, serialize_mir_type, serialize_mir_inst_kind, serialize_operand}
use compiler.mir.mir_lowering_types.{MirLowering}
use compiler.mir._MirLowering.module_lowering.*
use compiler.mir.verification_source_environment_v1.{verification_source_environment_v1}
use compiler.mir.mir_enum_semantic_types.{MirEnumPatternKindV1, MirEnumSiteKindV1}
use compiler.mir.enum_pattern_totality_v1.{enum_pattern_totality_bounded_v1}
use compiler.mir.enum_semantic_lowering_v1.{lower_module_with_enum_semantics_v1}
use compiler.backend.backend.lean_backend.{LeanBackend, VerificationLevel}

fn ee_hir(source: text, preserve_source_arms: bool = true) -> HirModule:
    val parsed = parse_full_frontend(source, "ee_enum.spl", "ee_enum.spl", Logger(level: 0))
    var lowering = HirLowering.with_filename("ee_enum.spl")
    lowering.preserve_enum_semantic_arms_v1 = preserve_source_arms
    val hir = lowering.lower_module(parsed)
    expect(lowering.errors.len()).to_equal(0)
    hir

fn ee_lower(source: text) -> MirModule:
    val hir = ee_hir(source)
    val target = mir_target_context_from("x86_64-unknown-linux-gnu", "unknown", "unknown", "llvm", 1)
    lower_module_with_enum_semantics_v1(hir, target).unwrap()

fn ee_function(module: MirModule, name: text) -> MirFunction?:
    for function in module.functions.values():
        if function.name == "ee_enum." + name or function.name == name:
            return Some(function)
    nil

fn ee_indent(line: text) -> i64:
    var index = 0
    while index < line.len() and line.char_code_at(index) == 32:
        index = index + 1
    index

fn ee_continuation(code: text, label: text) -> text:
    var lines: [text] = []
    var collecting = false
    var indentation = 0
    for line in code.split("\n"):
        val trimmed = line.trim()
        if not collecting:
            if trimmed.starts_with("let " + label + " "):
                collecting = true
                indentation = ee_indent(line)
                lines.push(line)
        else:
            if trimmed != "" and ee_indent(line) <= indentation:
                return lines.join("\n")
            lines.push(line)
    expect(collecting).to_equal(true)
    lines.join("\n")

# @inline
fn ee_outputs(module: MirModule, fragments: [text], bodies: [(text, text)] = [], false_edges: [(text, text)] = []):
    val backend = LeanBackend.create(VerificationLevel.Contracts)
    val full = backend.export_module(module).unwrap().lean_code
    val generated = backend.export_generated_module(module).unwrap().lean_code
    for code in [full, generated]:
        for fragment in fragments:
            expect(code).to_contain(fragment)
        expect(code.contains("rt_enum_discriminant")).to_equal(false)
        expect(code.contains("rt_enum_payload")).to_equal(false)
        for (label, body_term) in bodies:
            expect(ee_continuation(code, label)).to_contain(body_term)
        for (label, successor) in false_edges:
            val guard = ee_continuation(code, label)
            val lines = guard.split("\n")
            var found = false
            for index in 0..(lines.len() - 1):
                val next = lines[index + 1].trim()
                if lines[index].trim() == "else" and (next == successor or next.starts_with(successor + " ")):
                    found = true
            expect(found).to_equal(true)

# @inline
fn ee_refusal(module: MirModule, reason: text):
    val before = serialize_mir_module(module)
    val backend = LeanBackend.create(VerificationLevel.Contracts)
    match backend.export_module(module):
        case Err(error): expect(error.message).to_contain(reason)
        case Ok(_): assert(false)
    expect(serialize_mir_module(module)).to_equal(before)
    match backend.export_generated_module(module):
        case Err(error): expect(error.message).to_contain(reason)
        case Ok(_): assert(false)
    expect(serialize_mir_module(module)).to_equal(before)

fn ee_expanded_guard_outputs(module: MirModule, alternatives: i64):
    val function = ee_function(module, "select").unwrap()
    val semantic = function.enum_matches[0]
    expect(semantic.arms.len()).to_equal(alternatives + 1)
    var bodies: [(text, text)] = []
    var false_edges: [(text, text)] = []
    for index in 0..alternatives:
        val arm = semantic.arms[index]
        expect(arm.source_arm_id).to_equal(0)
        expect(arm.source_arm_id).to_equal(semantic.arms[0].source_arm_id)
        expect(arm.expanded_alternative_index).to_equal(index)
        expect(arm.guard_failure_entry.id).to_equal(semantic.arms[index + 1].pattern_entry_block.id)
        expect(arm.pattern_failure_entry.id).to_equal(semantic.arms[index + 1].pattern_entry_block.id)
        val block_index = ee_block_index(function, arm.guard_entry.unwrap())
        match function.blocks[block_index].terminator:
            case MirTerminator.If(_, _, failure): expect(failure.id).to_equal(arm.guard_failure_entry.id)
            case _: assert(false)
        if index > 0:
            expect(arm.guard_entry.unwrap().id == semantic.arms[index - 1].guard_entry.unwrap().id).to_equal(false)
            expect(arm.guard_failure_entry.id == semantic.arms[index - 1].guard_failure_entry.id).to_equal(false)
        bodies.push(("ee_m0_a{index}_body", "(BitVec.ofInt 32 11)"))
        false_edges.push(("ee_m0_a{index}_guard", "ee_b{arm.guard_failure_entry.id}"))
    expect(semantic.arms[alternatives].source_arm_id).to_equal(1)
    expect(semantic.arms[alternatives].expanded_alternative_index).to_equal(alternatives)
    bodies.push(("ee_m0_a{alternatives}_body", "(BitVec.ofInt 32 22)"))
    ee_outputs(module, ["(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"], bodies, false_edges)

fn ee_flag_source() -> text:
    "enum Flag:\n    Off\n    On\nfn select(value: Flag) -> i32:\n    match value:\n        case Flag.Off: 11\n        case Flag.On: 22\n"

fn ee_block_index(function: MirFunction, id: BlockId) -> i64:
    for index in 0..function.blocks.len():
        if function.blocks[index].id.id == id.id: return index
    assert(false)
    -1

fn ee_argument(function: MirFunction, index: i64) -> MirLocal?:
    for local in function.locals:
        match local.kind:
            case LocalKind.Arg(position):
                if position == index: return Some(local)
            case _: ()
    nil

fn ee_rehash(function: MirFunction) -> MirFunction:
    var changed = function
    val subject = sha256_text(serialize_mir_function_subject_v1(changed))
    for index in 0..changed.enum_matches.len():
        changed.enum_matches[index].subject_identity = subject
    changed

fn ee_copy(id: LocalId) -> MirOperand: MirOperand(kind: MirOperandKind.Copy(id))
fn ee_inst(kind: MirInstKind) -> MirInst: MirInst(kind: kind, span: nil)

# Select an actual captured root call by opcode, callee, operands and its region.
fn ee_root_call_site(function: MirFunction, helper: text, payload: bool) -> i64:
    val semantic = function.enum_matches[0]
    val arm = semantic.arms[0]
    var selected = -1
    var matches = 0
    for index in 0..semantic.sites.len():
        val site = semantic.sites[index]
        match site.kind:
            case MirEnumSiteKindV1.PatternInstruction:
                val block_index = ee_block_index(function, site.block_id)
                var in_region = site.block_id.id == semantic.entry_block.id and site.instruction_index >= semantic.entry_instruction_index
                if payload:
                    in_region = site.block_id.id == arm.body_entry.id and site.instruction_index < arm.body_entry_instruction_index and site.related_pattern_node == arm.pattern_root
                if in_region and site.instruction_index >= 0 and site.instruction_index < function.blocks[block_index].instructions.len():
                    match function.blocks[block_index].instructions[site.instruction_index].kind:
                        case MirInstKind.Call(destination, callee, arguments):
                            match callee.kind:
                                case MirOperandKind.Const(MirConstValue.Str(name), _):
                                    if name == helper and destination != nil and arguments.len() == 1:
                                        if serialize_operand(arguments[0]) == serialize_operand(semantic.scrutinee_operand):
                                            selected = index
                                            matches = matches + 1
                                case _: ()
                        case _: ()
            case _: ()
    expect(matches).to_equal(1)
    expect(selected).to_be_greater_than(-1)
    selected

fn ee_bool_source(arms: text) -> text:
    "enum Box:\n    Box(bool)\nfn select(value: Box) -> i32:\n    match value:\n" + arms

fn ee_guard_source(reuse: bool) -> text:
    val body = if reuse: "carry" else: "11"
    val fallback = if reuse: "carry" else: "22"
    "enum Box:\n    Box(i32)\nfn select(value: Box, flag: bool, carry: i32) -> i32:\n    match value:\n        case Box.Box(item) if flag: " + body + "\n        case _: " + fallback + "\n"

fn ee_overlap_source() -> text:
    "enum Box:\n    Box(i32)\nfn select(value: Box, flag: bool) -> i32:\n    match value:\n        case Box.Box(item) | Box.Box(item) if flag: item\n        case _: 29\n"

fn ee_depth_source(depth: i64) -> text:
    var pattern = "Nest.End"
    for index in 1..depth:
        pattern = "Nest.Next(" + pattern + ")"
    "enum Nest:\n    End\n    Next(Nest)\nfn select(value: Nest) -> i32:\n    match value:\n        case " + pattern + ": 11\n        case _: 22\n"

fn ee_source_refusal(source: text, reason: text, exact_prefix: bool = true):
    val hir = ee_hir(source)
    val before = hir_module_encode(hir)
    expect(before.len()).to_be_greater_than(0)
    val target = mir_target_context_from("x86_64-unknown-linux-gnu", "unknown", "unknown", "llvm", 1)
    match lower_module_with_enum_semantics_v1(hir, target):
        case Err(message):
            if exact_prefix:
                expect(message).to_start_with(reason)
            else:
                expect(message).to_contain(reason)
        case Ok(_): assert(false)
    expect(hir_module_encode(hir)).to_equal(before)

describe "EE-01 producer-bound named enum elimination":
    it "should export actual frontend nullary enum elimination without runtime carrier helpers":
        step("Parse and lower a two-variant Flag match for an explicit target and export both Lean modules")
        val module = ee_lower(ee_flag_source())
        val function = ee_function(module, "select").unwrap()
        expect(function.enum_matches.len()).to_equal(1)
        ee_outputs(module, ["«Flag».«Off»", "«Flag».«On»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"],
            [("ee_m0_a0_body", "(BitVec.ofInt 32 11)"), ("ee_m0_a1_body", "(BitVec.ofInt 32 22)")])

    it "should bind a single variant payload using its exact declared semantic type":
        step("Lower a one-variant Box and retain the actual bound payload local")
        val module = ee_lower("enum Box:\n    Box(i32)\nfn select(value: Box) -> i32:\n    match value:\n        case Box.Box(item): item\n")
        val function = ee_function(module, "select").unwrap()
        var bindings = 0
        for node in function.enum_matches[0].pattern_nodes:
            match node.kind:
                case MirEnumPatternKindV1.Bind(_, destination):
                    expect(node.expected_type.kind).to_equal(MirTypeKind.I32)
                    ee_outputs(module, ["«Box».«Box»", "_l{destination.id}", "_root_.BitVec 32"])
                    bindings = bindings + 1
                case _: ()
        expect(bindings).to_equal(1)

    it "should eliminate multiple variants and every finite tuple payload partition":
        step("Cover nullary scalar and tuple payload alternatives without a default")
        val source = "enum Choice:\n    Empty\n    Code(i32)\n    Pair(bool, bool)\nfn select(value: Choice) -> i32:\n    match value:\n        case Choice.Empty: 3\n        case Choice.Code(item): item\n        case Choice.Pair(true, true): 11\n        case Choice.Pair(true, false): 12\n        case Choice.Pair(false, true): 21\n        case Choice.Pair(false, false): 22\n"
        val module = ee_lower(source)
        ee_outputs(module, ["«Choice».«Empty»", "«Choice».«Code»", "«Choice».«Pair»", "(BitVec.ofInt 32 3)", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 12)", "(BitVec.ofInt 32 21)", "(BitVec.ofInt 32 22)"])
        ee_source_refusal(source.replace("        case Choice.Pair(false, false): 22\n", ""), "EE-E-RESIDUAL")

    it "should eliminate a single tuple-valued variant field and require its complete Bool partition":
        step("Retain one declared tuple slot and cover all four nested tuple patterns")
        val source = "enum Wrap:\n    Wrap((bool, bool))\nfn select(value: Wrap) -> i32:\n    match value:\n        case Wrap.Wrap((true, true)): 11\n        case Wrap.Wrap((true, false)): 12\n        case Wrap.Wrap((false, true)): 21\n        case Wrap.Wrap((false, false)): 22\n"
        val module = ee_lower(source)
        val semantic = ee_function(module, "select").unwrap().enum_matches[0]
        val root = semantic.arms[0].pattern_root
        match semantic.pattern_nodes[root].kind:
            case MirEnumPatternKindV1.Variant(_, _, children):
                expect(children.len()).to_equal(1)
                match semantic.pattern_nodes[children[0]].kind:
                    case MirEnumPatternKindV1.Tuple(fields): expect(fields.len()).to_equal(2)
                    case _: assert(false)
            case _: assert(false)
        ee_outputs(module, ["«Wrap».«Wrap»"],
            [("ee_m0_a0_body", "(BitVec.ofInt 32 11)"), ("ee_m0_a1_body", "(BitVec.ofInt 32 12)"), ("ee_m0_a2_body", "(BitVec.ofInt 32 21)"), ("ee_m0_a3_body", "(BitVec.ofInt 32 22)")])
        ee_source_refusal(source.replace("        case Wrap.Wrap((false, false)): 22\n", ""), "EE-E-RESIDUAL")

    it "should prove nested enum payload partitions and reject the missing inner constructor":
        step("Specialize the actual inner constructor set instead of treating outer coverage as total")
        val source = "enum Inner:\n    Left\n    Right\nenum Outer:\n    Wrap(Inner)\nfn select(value: Outer) -> i32:\n    match value:\n        case Outer.Wrap(Inner.Left): 11\n        case Outer.Wrap(Inner.Right): 22\n"
        ee_outputs(ee_lower(source), ["«Outer».«Wrap»", "«Inner».«Left»", "«Inner».«Right»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])
        ee_source_refusal(source.replace("        case Outer.Wrap(Inner.Right): 22\n", ""), "EE-E-RESIDUAL")

    it "should stop unfolding recursive payloads beneath wildcard patterns":
        step("Eliminate a recursive enum while leaving its wildcard tail uninterpreted")
        val source = "enum Chain:\n    End\n    Link(i32, Chain)\nfn select(value: Chain) -> i32:\n    match value:\n        case Chain.End: 0\n        case Chain.Link(item, _): item\n"
        ee_outputs(ee_lower(source), ["«Chain».«End»", "«Chain».«Link»", "(BitVec.ofInt 32 0)", "_root_.BitVec 32"])

    it "should use exact declared discriminants without assuming sequential tags":
        step("Capture and eliminate explicit discriminants seven and forty-two")
        val source = "enum Flag:\n    Off = 7\n    On = 42\nfn select(value: Flag) -> i32:\n    match value:\n        case Flag.Off: 11\n        case Flag.On: 22\n"
        val module = ee_lower(source)
        val function = ee_function(module, "select").unwrap()
        var tags: [i64] = []
        for node in function.enum_matches[0].pattern_nodes:
            match node.kind:
                case MirEnumPatternKindV1.Variant(_, discriminant, _): tags.push(discriminant)
                case _: ()
        expect(tags).to_equal([7, 42])
        ee_outputs(module, ["«Flag».«Off»", "«Flag».«On»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"],
            [("ee_m0_a0_body", "(BitVec.ofInt 32 11)"), ("ee_m0_a1_body", "(BitVec.ofInt 32 22)")])

    it "should preserve repeated guarded variants and unconditional fallback order":
        step("Evaluate a guard only after its pattern and retain the next matching arm")
        val source = "enum Box:\n    Box(i32)\nfn select(value: Box, flag: bool) -> i32:\n    match value:\n        case Box.Box(item) if flag: 11\n        case Box.Box(item): 22\n"
        ee_outputs(ee_lower(source), ["ee_m0_a0_guard", "ee_m0_a0_body", "ee_m0_a1_body", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])

    it "should preserve each expanded Or guard and its actual false successor":
        step("Keep overlapping alternatives distinct even when they share a source body")
        val module = ee_lower(ee_overlap_source())
        val function = ee_function(module, "select").unwrap()
        val semantic = function.enum_matches[0]
        expect(semantic.arms.len()).to_equal(3)
        expect(semantic.arms[0].source_arm_id).to_equal(semantic.arms[1].source_arm_id)
        expect(semantic.arms[0].expanded_alternative_index).to_equal(0)
        expect(semantic.arms[1].expanded_alternative_index).to_equal(1)
        expect(semantic.arms[0].guard_entry.unwrap().id == semantic.arms[1].guard_entry.unwrap().id).to_equal(false)
        expect(semantic.arms[0].guard_failure_entry.id == semantic.arms[1].guard_failure_entry.id).to_equal(false)
        for index in [0, 1]:
            val guard_block = ee_block_index(function, semantic.arms[index].guard_entry.unwrap())
            match function.blocks[guard_block].terminator:
                case MirTerminator.If(_, _, failure):
                    expect(failure.id).to_equal(semantic.arms[index].guard_failure_entry.id)
                case _: assert(false)
        ee_outputs(module, ["ee_m0_a0_guard", "ee_m0_a1_guard", "(BitVec.ofInt 32 29)"], [],
            [("ee_m0_a0_guard", "ee_b{semantic.arms[0].guard_failure_entry.id}"),
             ("ee_m0_a1_guard", "ee_b{semantic.arms[1].guard_failure_entry.id}")])

    it "should expand nested Or inside an enum payload without changing source arm identity":
        step("Lower two nested constructor alternatives and retain each actual guard retry continuation")
        val source = "enum Inner:\n    Left\n    Right\nenum Outer:\n    Wrap(Inner)\nfn select(value: Outer, flag: bool) -> i32:\n    match value:\n        case Outer.Wrap(Inner.Left | Inner.Right) if flag: 11\n        case _: 22\n"
        val module = ee_lower(source)
        val semantic = ee_function(module, "select").unwrap().enum_matches[0]
        for index in 0..2:
            val root = semantic.arms[index].pattern_root
            match semantic.pattern_nodes[root].kind:
                case MirEnumPatternKindV1.Variant(owner, _, children):
                    expect(owner.id).to_equal(semantic.enum_owner.id)
                    expect(children.len()).to_equal(1)
                    match semantic.pattern_nodes[children[0]].kind:
                        case MirEnumPatternKindV1.Variant(inner_owner, discriminant, inner_children):
                            expect(inner_owner.id == owner.id).to_equal(false)
                            expect(discriminant).to_equal(index)
                            expect(inner_children.len()).to_equal(0)
                        case _: assert(false)
                case _: assert(false)
        ee_expanded_guard_outputs(module, 2)
        ee_outputs(module, ["«Outer».«Wrap»", "«Inner».«Left»", "«Inner».«Right»"])
        var hir = ee_hir(source)
        var changed = 0
        for symbol in hir.functions.keys():
            var function = hir.functions[symbol]
            if function.name == "select" or function.name == "ee_enum.select":
                expect(function.body.has).to_equal(true)
                match function.body.value.kind:
                    case HirExprKind.MatchCase(scrutinee, arms):
                        expect(arms.len()).to_equal(2)
                        var duplicate_spans = arms
                        duplicate_spans[1].span = arms[0].span
                        duplicate_spans[1].pattern.span = arms[0].pattern.span
                        function.body.value.kind = HirExprKind.MatchCase(scrutinee, duplicate_spans)
                        hir.functions[symbol] = function
                        changed = changed + 1
                    case _: assert(false)
        expect(changed).to_equal(1)
        val before = hir_module_encode(hir)
        val duplicate_span_module = lower_module_with_enum_semantics_v1(hir, mir_target_context_from("x86_64-unknown-linux-gnu", "unknown", "unknown", "llvm", 1)).unwrap()
        ee_expanded_guard_outputs(duplicate_span_module, 2)
        expect(hir_module_encode(hir)).to_equal(before)

    it "should expand nested Or through a single tuple field in lexical product order":
        step("Lower the four Bool product alternatives and preserve original arm identity and guard fallthrough")
        val source = "enum Wrap:\n    Wrap((bool, bool))\nfn select(value: Wrap, flag: bool) -> i32:\n    match value:\n        case Wrap.Wrap((true | false, true | false)) if flag: 11\n        case _: 22\n"
        val module = ee_lower(source)
        val semantic = ee_function(module, "select").unwrap().enum_matches[0]
        for index in 0..4:
            val root = semantic.arms[index].pattern_root
            match semantic.pattern_nodes[root].kind:
                case MirEnumPatternKindV1.Variant(_, _, children):
                    expect(children.len()).to_equal(1)
                    match semantic.pattern_nodes[children[0]].kind:
                        case MirEnumPatternKindV1.Tuple(fields):
                            expect(fields.len()).to_equal(2)
                            for field in 0..2:
                                val expected = if field == 0: index < 2 else: index % 2 == 0
                                match semantic.pattern_nodes[fields[field]].kind:
                                    case MirEnumPatternKindV1.Literal(MirConstValue.Bool(value), type_):
                                        expect(value).to_equal(expected)
                                        expect(type_.kind).to_equal(MirTypeKind.Bool)
                                    case _: assert(false)
                        case _: assert(false)
                case _: assert(false)
        ee_expanded_guard_outputs(module, 4)
        ee_outputs(module, ["«Wrap».«Wrap»", "true", "false"])

    it "should lower nested matches with separate preorder match identities":
        step("Retain the inner match and selected outer payload without a global registry")
        val source = "enum Inner:\n    Left\n    Right\nenum Outer:\n    Wrap(Inner)\n    Empty\nfn select(value: Outer) -> i32:\n    match value:\n        case Outer.Wrap(item):\n            match item:\n                case Inner.Left: 11\n                case Inner.Right: 22\n        case Outer.Empty: 33\n"
        val module = ee_lower(source)
        val function = ee_function(module, "select").unwrap()
        expect(function.enum_matches.len()).to_equal(2)
        expect(function.enum_matches[0].match_id).to_equal(0)
        expect(function.enum_matches[1].match_id).to_equal(1)
        ee_outputs(module, ["ee_m0_a0_body", "ee_m1_a0_body", "«Inner».«Left»", "«Inner».«Right»", "(BitVec.ofInt 32 33)"])

    it "should preserve outer locals common result flow and reordered physical blocks":
        step("Follow stable block identities while retaining a shared post-match computation")
        val source = "enum Flag:\n    Off\n    On\nfn select(value: Flag, bias: i32) -> i32:\n    val selected = match value:\n        case Flag.Off: 11\n        case Flag.On: 22\n    selected + bias\n"
        var module = ee_lower(source)
        var function = ee_function(module, "select").unwrap()
        var reordered: [MirBlock] = []
        for offset in 0..function.blocks.len():
            reordered.push(function.blocks[function.blocks.len() - 1 - offset])
        function.blocks = reordered
        function = ee_rehash(function)
        module.functions[function.symbol] = function
        ee_outputs(module, ["«Flag».«Off»", "«Flag».«On»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)", " + "])

    it "should distinguish full Bool payload coverage from outer-variant coverage":
        step("Accept true and false together and reject either missing payload partition")
        val yes = "        case Box.Box(true): 11\n"
        val no = "        case Box.Box(false): 22\n"
        ee_outputs(ee_lower(ee_bool_source(yes + no)), ["«Box».«Box»", "true", "false", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])
        ee_source_refusal(ee_bool_source(yes), "EE-E-RESIDUAL")
        ee_source_refusal(ee_bool_source(no), "EE-E-RESIDUAL")

    it "should preserve complementary residuals under overlapping Or alternatives":
        step("Reject duplicated true coverage until an unguarded false alternative exists")
        val overlap = "        case Box.Box(true) | Box.Box(true): 11\n"
        ee_source_refusal(ee_bool_source(overlap), "EE-E-RESIDUAL")
        ee_outputs(ee_lower(ee_bool_source(overlap + "        case Box.Box(false): 22\n")), ["(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)", "true", "false"])
        ee_source_refusal(ee_bool_source(overlap + "        case Box.Box(false) if true: 22\n"), "EE-E-RESIDUAL")

    it "should require an unconditional residual cover even after a literal true guard":
        step("Treat guarded rows as potentially falling through and preserve the real fallback")
        val guarded = "        case Box.Box(true) if true: 11\n        case Box.Box(false): 22\n"
        ee_source_refusal(ee_bool_source(guarded), "EE-E-RESIDUAL")
        ee_outputs(ee_lower(ee_bool_source(guarded + "        case _: 33\n")), ["ee_m0_a0_guard", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)", "(BitVec.ofInt 32 33)"])

    it "should retain an integer other-value residual until a wildcard or binder covers it":
        step("Keep integer payload reasoning symbolic rather than enumerating its domain")
        val source = "enum Box:\n    Box(i32)\nfn select(value: Box) -> i32:\n    match value:\n        case Box.Box(0): 11\n"
        ee_source_refusal(source, "EE-E-RESIDUAL")
        ee_outputs(ee_lower(source + "        case Box.Box(other): other\n"), ["«Box».«Box»", "(BitVec.ofInt 32 0)", "(BitVec.ofInt 32 11)"])

    it "should carry consumed guard state onto false successors without resurrecting locals":
        step("Append an actual guard Move and distinguish unused from subsequently read input")
        for reuse in [false, true]:
            var module = ee_lower(ee_guard_source(reuse))
            var function = ee_function(module, "select").unwrap()
            val incoming = ee_argument(function, 2).unwrap()
            var identity = 0
            for local in function.locals:
                if local.id.id >= identity: identity = local.id.id + 1
            val destination = LocalId(id: identity)
            function.locals.push(MirLocal(id: destination, name: nil, type_: incoming.type_, kind: LocalKind.Temp, is_ghost: false))
            val guard_index = ee_block_index(function, function.enum_matches[0].arms[0].guard_entry.unwrap())
            function.blocks[guard_index].instructions.push(ee_inst(MirInstKind.Move(destination, incoming.id)))
            function = ee_rehash(function)
            module.functions[function.symbol] = function
            if reuse:
                ee_refusal(module, "EE-E-AVAILABILITY")
            else:
                ee_outputs(module, ["ee_m0_a0_guard", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])

    it "should consume live Drop once and retain assignment history after it":
        step("Append ordinary Drop operations to actual guard MIR and distinguish dead reads from redefinitions")
        for mutation in [0, 1, 2, 3]:
            var module = ee_lower(ee_guard_source(false))
            var function = ee_function(module, "select").unwrap()
            val incoming = ee_argument(function, 2).unwrap()
            var identity = 0
            for local in function.locals:
                if local.id.id >= identity: identity = local.id.id + 1
            val saved = LocalId(id: identity)
            if mutation == 2 or mutation == 3:
                function.locals.push(MirLocal(id: saved, name: nil, type_: incoming.type_, kind: LocalKind.Temp, is_ghost: false))
            val guard_index = ee_block_index(function, function.enum_matches[0].arms[0].guard_entry.unwrap())
            if mutation == 3:
                function.blocks[guard_index].instructions.push(ee_inst(MirInstKind.Copy(saved, incoming.id)))
            function.blocks[guard_index].instructions.push(ee_inst(MirInstKind.Drop(incoming.id)))
            if mutation == 1:
                function.blocks[guard_index].instructions.push(ee_inst(MirInstKind.Drop(incoming.id)))
            elif mutation == 2:
                function.blocks[guard_index].instructions.push(ee_inst(MirInstKind.Copy(saved, incoming.id)))
            elif mutation == 3:
                function.blocks[guard_index].instructions.push(ee_inst(MirInstKind.Copy(incoming.id, saved)))
            module.functions[function.symbol] = ee_rehash(function)
            if mutation == 0:
                ee_outputs(module, ["ee_m0_a0_guard"], [("ee_m0_a0_body", "(BitVec.ofInt 32 11)"), ("ee_m0_a1_body", "(BitVec.ofInt 32 22)")])
            elif mutation == 1:
                ee_refusal(module, "drop before definition or after move: {incoming.id.id}")
            elif mutation == 2:
                ee_refusal(module, "use before definition or after move: {incoming.id.id}")
            else:
                ee_refusal(module, "local redefinition requires mutable state semantics: {incoming.id.id}")

    it "should refuse dropped enum metadata instead of recognizing runtime helper names as authority":
        step("Remove only the actual producer metadata and require both public exports to fail")
        var module = ee_lower(ee_flag_source())
        var function = ee_function(module, "select").unwrap()
        function.enum_matches = []
        module.functions[function.symbol] = function
        ee_refusal(module, "EE-E-METADATA")

    it "should reject stale body and signature subjects before emitting a module":
        step("Mutate actual retained MIR while leaving its recorded subject identity stale")
        var signature_module = ee_lower(ee_flag_source())
        var signature_function = ee_function(signature_module, "select").unwrap()
        signature_function.signature.return_type = MirType(kind: MirTypeKind.Bool)
        signature_module.functions[signature_function.symbol] = signature_function
        ee_refusal(signature_module, "EE-E-SUBJECT")
        var body_module = ee_lower(ee_flag_source())
        var body_function = ee_function(body_module, "select").unwrap()
        val merge = ee_block_index(body_function, body_function.enum_matches[0].merge_block)
        body_function.blocks[merge].terminator = MirTerminator.Unreachable
        body_module.functions[body_function.symbol] = body_function
        ee_refusal(body_module, "EE-E-SUBJECT")

    it "should reject stale declaration identities and same-name metadata from another module":
        step("Keep enum authority bound to the exact declaration owner and payload table")
        var module = ee_lower(ee_flag_source())
        val function = ee_function(module, "select").unwrap()
        val owner = function.enum_matches[0].enum_owner
        var declaration = module.types[owner]
        match declaration.kind:
            case MirTypeDefKind.Enum(variants):
                var changed = variants
                changed[0].discriminant = 99
                declaration.kind = MirTypeDefKind.Enum(changed)
            case _: assert(false)
        module.types[owner] = declaration
        ee_refusal(module, "EE-E-DECLARATION")
        val parsed = parse_full_frontend(ee_flag_source(), "foreign_enum.spl", "foreign_enum.spl", Logger(level: 0))
        var frontend = HirLowering.with_filename("foreign_enum.spl")
        frontend.preserve_enum_semantic_arms_v1 = true
        val hir = frontend.lower_module(parsed)
        expect(frontend.errors.len()).to_equal(0)
        val foreign = lower_module_with_enum_semantics_v1(hir, mir_target_context_from("x86_64-unknown-linux-gnu", "unknown", "unknown", "llvm", 1)).unwrap()
        var foreign_records = function.enum_matches
        var found = false
        for candidate in foreign.functions.values():
            if candidate.name == "foreign_enum.select":
                foreign_records = candidate.enum_matches
                found = true
        expect(found).to_equal(true)
        var original = ee_lower(ee_flag_source())
        var replaced = ee_function(original, "select").unwrap()
        replaced.enum_matches = foreign_records
        replaced = ee_rehash(replaced)
        original.functions[replaced.symbol] = replaced
        ee_refusal(original, "EE-E-DECLARATION")

    it "should reject relocated duplicate and modified actual semantic sites after public rehashing":
        step("Show that a matching public subject hash cannot authorize corrupt producer sites")
        for mutation in [0, 1, 2]:
            var module = ee_lower(ee_flag_source())
            var function = ee_function(module, "select").unwrap()
            val selected = ee_root_call_site(function, "rt_enum_discriminant", false)
            val site = function.enum_matches[0].sites[selected]
            if mutation == 0:
                function.enum_matches[0].sites[selected].instruction_index = site.instruction_index + 1
            elif mutation == 1:
                function.enum_matches[0].sites.push(site)
            else:
                val index = ee_block_index(function, site.block_id)
                expect(site.instruction_index).to_be_greater_than(-1)
                expect(site.instruction_index).to_be_less_than(function.blocks[index].instructions.len())
                function.blocks[index].instructions[site.instruction_index] = ee_inst(MirInstKind.Drop(function.enum_matches[0].result_local))
                function = ee_rehash(function)
            module.functions[function.symbol] = function
            ee_refusal(module, "EE-E-SITE")

    it "should reject cyclic pattern references changed discriminants and mismatched expected types":
        step("Validate actual flat pattern nodes structurally instead of trusting their serialized identity")
        for mutation in [0, 1, 2]:
            var module = ee_lower(ee_flag_source())
            var function = ee_function(module, "select").unwrap()
            val root = function.enum_matches[0].arms[0].pattern_root
            var node = function.enum_matches[0].pattern_nodes[root]
            match node.kind:
                case MirEnumPatternKindV1.Variant(owner, discriminant, children):
                    if mutation == 0:
                        node.kind = MirEnumPatternKindV1.Variant(owner, discriminant, [root])
                    elif mutation == 1:
                        node.kind = MirEnumPatternKindV1.Variant(owner, 9999, children)
                    else:
                        node.expected_type = MirType(kind: MirTypeKind.Bool)
                case _: assert(false)
            function.enum_matches[0].pattern_nodes[root] = node
            module.functions[function.symbol] = function
            ee_refusal(module, "EE-E-PATTERN")

    it "should reject a guard false edge that skips the next expanded alternative":
        step("Change the first real guard edge and reject it both before and after updating the public hash")
        var module = ee_lower(ee_overlap_source())
        var function = ee_function(module, "select").unwrap()
        val semantic = function.enum_matches[0]
        val guard_index = ee_block_index(function, semantic.arms[0].guard_entry.unwrap())
        match function.blocks[guard_index].terminator:
            case MirTerminator.If(condition, yes, _):
                function.blocks[guard_index].terminator = MirTerminator.If(condition, yes, semantic.arms[1].guard_failure_entry)
            case _: assert(false)
        module.functions[function.symbol] = function
        ee_refusal(module, "EE-E-SUBJECT")
        function = ee_rehash(function)
        module.functions[function.symbol] = function
        ee_refusal(module, "EE-E-EDGE")

    it "should reject a deleted fallback cyclic edge duplicate block or disconnected block":
        step("Invalidate actual retained graph structure without fabricating replacement metadata")
        for mutation in [0, 1, 2, 3]:
            var module = ee_lower(ee_guard_source(false))
            var function = ee_function(module, "select").unwrap()
            val fallback = function.enum_matches[0].arms[1].body_entry
            val index = ee_block_index(function, fallback)
            if mutation == 0:
                var retained: [MirBlock] = []
                for block in function.blocks:
                    if block.id.id != fallback.id: retained.push(block)
                function.blocks = retained
            elif mutation == 1:
                function.blocks[index].terminator = MirTerminator.Goto(fallback)
            elif mutation == 2:
                function.blocks.push(function.blocks[index])
            else:
                var identity = 0
                for block in function.blocks:
                    if block.id.id >= identity: identity = block.id.id + 1
                function.blocks.push(MirBlock(id: BlockId(id: identity), label: nil, instructions: [], terminator: MirTerminator.Unreachable))
            function = ee_rehash(function)
            module.functions[function.symbol] = function
            ee_refusal(module, "EE-E-EDGE")

    it "should reject invalid Or binding names and unequal declared binding types at the actual frontend":
        step("Preserve existing source binding rules before any semantic export is attempted")
        val names = "enum Choice:\n    Left(i32)\n    Right(i32)\nfn select(value: Choice) -> i32:\n    match value:\n        case Choice.Left(left) | Choice.Right(right): 11\n        case _: 22\n"
        val parsed = parse_full_frontend(names, "ee_enum.spl", "ee_enum.spl", Logger(level: 0))
        var frontend = HirLowering.with_filename("ee_enum.spl")
        frontend.preserve_enum_semantic_arms_v1 = true
        val _hir = frontend.lower_module(parsed)
        var messages: [text] = []
        for error in frontend.errors: messages.push(error.message)
        expect(messages.join("\n")).to_contain("or-pattern alternatives must bind the same variables")
        ee_source_refusal("enum Choice:\n    Left(i32)\n    Right(bool)\nfn select(value: Choice) -> i32:\n    match value:\n        case Choice.Left(item) | Choice.Right(item): 11\n        case _: 22\n", "every alternative must bind it with the same type", false)

    it "should publish no partial module after a valid match followed by a residual failure and preserve source ownership":
        step("Lower one HIR module then reject its later match without mutating HIR or SymbolTable")
        val source = ee_flag_source() + "enum Box:\n    Box(bool)\nfn bad(value: Box) -> i32:\n    match value:\n        case Box.Box(true): 11\n"
        val hir = ee_hir(source)
        val before = hir_module_encode(hir)
        expect(before.len()).to_be_greater_than(0)
        val next_symbol = hir.symbols.next_symbol_id
        val next_scope = hir.symbols.next_scope_id
        val symbol_keys = hir.symbols.symbols.keys()
        val symbol_count = symbol_keys.len()
        val valid_prefix = ee_lower(ee_flag_source())
        expect(ee_function(valid_prefix, "select").unwrap().enum_matches.len()).to_equal(1)
        ee_outputs(valid_prefix, ["«Flag».«Off»", "«Flag».«On»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])
        match lower_module_with_enum_semantics_v1(hir, mir_target_context_from("x86_64-unknown-linux-gnu", "unknown", "unknown", "llvm", 1)):
            case Err(message): expect(message).to_start_with("EE-E-RESIDUAL")
            case Ok(_): assert(false)
        expect(hir_module_encode(hir)).to_equal(before)
        expect(hir.symbols.next_symbol_id).to_equal(next_symbol)
        expect(hir.symbols.next_scope_id).to_equal(next_scope)
        val final_symbol_keys = hir.symbols.symbols.keys()
        expect(final_symbol_keys.len()).to_equal(symbol_count)

    it "should preserve ordinary physical function bytes and types when opting into enum capture":
        step("Lower the same source with ordinary and opted HIR policies and compare every original physical function")
        # These nullary and scalar payload patterns were already supported by ordinary lowering.
        # Newly admitted nested tuple patterns are excluded from this parity claim.
        val source = "enum Flag:\n    Off\n    On\nenum Box:\n    Box(i32)\nfn flag_value(value: Flag) -> i32:\n    match value:\n        case Flag.Off: 11\n        case Flag.On: 22\nfn box_value(value: Box) -> i32:\n    match value:\n        case Box.Box(item): item\n"
        val ordinary_source_hir = ee_hir(source, false)
        val ordinary_before = hir_module_encode(ordinary_source_hir)
        expect(ordinary_before.len()).to_be_greater_than(0)
        val hir = ee_hir(source, true)
        val before = hir_module_encode(hir)
        expect(before.len()).to_be_greater_than(0)
        val next_symbol = hir.symbols.next_symbol_id
        val next_scope = hir.symbols.next_scope_id
        val target = mir_target_context_from("x86_64-unknown-linux-gnu", "unknown", "unknown", "llvm", 1)
        var ordinary_hir = ordinary_source_hir
        ordinary_hir.symbols = verification_source_environment_v1(ordinary_source_hir.symbols).unwrap()
        var opted_hir = hir
        opted_hir.symbols = verification_source_environment_v1(hir.symbols).unwrap()
        val opted_before = hir_module_encode(opted_hir)
        var ordinary_lowering = MirLowering.new_for_target(ordinary_hir.symbols, target)
        ordinary_lowering.allow_ambient_bootstrap_policy = false
        val ordinary = ordinary_lowering.lower_module(ordinary_hir)
        expect(ordinary_lowering.errors.len()).to_equal(0)
        expect(hir_module_encode(hir)).to_equal(before)
        expect(hir_module_encode(ordinary_source_hir)).to_equal(ordinary_before)
        expect(hir_module_encode(opted_hir)).to_equal(opted_before)
        val opted = lower_module_with_enum_semantics_v1(opted_hir, target).unwrap()
        val original_functions = ordinary.functions.keys()
        expect(original_functions.len()).to_be_greater_than(1)
        expect(opted.functions.keys().len()).to_equal(original_functions.len())
        for symbol in original_functions:
            val original = ordinary.functions[symbol]
            val captured = opted.functions.get(symbol).unwrap()
            expect(serialize_mir_function_subject_v1(captured)).to_equal(serialize_mir_function_subject_v1(original))
            expect(serialize_mir_signature(captured.signature)).to_equal(serialize_mir_signature(original.signature))
            expect(captured.locals.len()).to_equal(original.locals.len())
            for index in 0..original.locals.len():
                expect(captured.locals[index].id.id).to_equal(original.locals[index].id.id)
                expect(serialize_mir_type(captured.locals[index].type_)).to_equal(serialize_mir_type(original.locals[index].type_))
            expect(original.enum_matches.len()).to_equal(0)
        expect(ee_function(opted, "flag_value").unwrap().enum_matches.len()).to_equal(1)
        expect(ee_function(opted, "box_value").unwrap().enum_matches.len()).to_equal(1)
        ee_outputs(opted, ["«Flag».«Off»", "«Flag».«On»", "«Box».«Box»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])
        expect(hir_module_encode(hir)).to_equal(before)
        expect(hir_module_encode(ordinary_source_hir)).to_equal(ordinary_before)
        expect(hir_module_encode(opted_hir)).to_equal(opted_before)
        expect(hir.symbols.next_symbol_id).to_equal(next_symbol)
        expect(hir.symbols.next_scope_id).to_equal(next_scope)

    it "should isolate repeated lowering invocations and explicit target contexts":
        step("Capture fresh metadata for the same source under two explicit targets")
        val hir = ee_hir(ee_flag_source())
        val before = hir_module_encode(hir)
        expect(before.len()).to_be_greater_than(0)
        val first = lower_module_with_enum_semantics_v1(hir, mir_target_context_from("x86_64-unknown-linux-gnu", "unknown", "unknown", "llvm", 1)).unwrap()
        val first_bytes = serialize_mir_module(first)
        val second = lower_module_with_enum_semantics_v1(hir, mir_target_context_from("aarch64-unknown-linux-gnu", "unknown", "unknown", "llvm", 1)).unwrap()
        ee_outputs(second, ["«Flag».«Off»", "«Flag».«On»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])
        expect(serialize_mir_module(first)).to_equal(first_bytes)
        expect(hir_module_encode(hir)).to_equal(before)
        expect(ee_function(first, "select").unwrap().enum_matches[0].match_id).to_equal(0)
        expect(ee_function(second, "select").unwrap().enum_matches[0].match_id).to_equal(0)

    it "should separate representative recursive source acceptance from the syntactic depth limit":
        step("Export a depth-eight constructor pattern and refuse a source pattern above height 128")
        # Syntactic height and cumulative symbolic work are separate bounds.
        # Exact admitted height128 is covered by the component decision API ladder.
        val module = ee_lower(ee_depth_source(8))
        ee_outputs(module, ["«Nest».«Next»", "«Nest».«End»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])
        ee_source_refusal(ee_depth_source(129), "EE-E-LIMIT")

    it "should enforce the observed symbolic-work boundary using actual produced patterns":
        step("Measure production-checker work and test exactly sufficient and one-less budgets")
        val module = ee_lower(ee_bool_source("        case Box.Box(true): 11\n        case Box.Box(false): 22\n"))
        ee_outputs(module, ["«Box».«Box»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])
        val semantic = ee_function(module, "select").unwrap().enum_matches[0]
        val remaining = enum_pattern_totality_bounded_v1(module, semantic, 65536).unwrap()
        val consumed = 65536 - remaining
        expect(consumed).to_be_greater_than(0)
        expect(consumed).to_be_less_than(65537)
        expect(enum_pattern_totality_bounded_v1(module, semantic, consumed).unwrap()).to_equal(0)
        match enum_pattern_totality_bounded_v1(module, semantic, consumed - 1):
            case Err(message): expect(message).to_contain("EE-E-LIMIT")
            case Ok(_): assert(false)
        match enum_pattern_totality_bounded_v1(module, semantic, 65537):
            case Err(message): expect(message).to_contain("EE-E-LIMIT")
            case Ok(_): assert(false)

    it "should preserve the existing Result-specific elimination route":
        step("Lower actual Result Ok and Err patterns without replacing their established witness")
        val source = "fn select(value: Result<i32, i32>) -> i32:\n    match value:\n        case Ok(item): item\n        case Err(error): error\n"
        val module = ee_lower(source)
        val function = ee_function(module, "select").unwrap()
        expect(function.enum_matches.len()).to_equal(0)
        ee_outputs(module, ["| Except.ok ok_payload =>", "| Except.error err_payload =>"])
        val mixed = ee_lower(source + "enum Flag:\n    Off\n    On\nfn named(value: Flag) -> i32:\n    match value:\n        case Flag.Off: 11\n        case Flag.On: 22\n")
        expect(ee_function(mixed, "select").unwrap().enum_matches.len()).to_equal(0)
        expect(ee_function(mixed, "named").unwrap().enum_matches.len()).to_equal(1)
        ee_outputs(mixed, ["| Except.ok ok_payload =>", "| Except.error err_payload =>", "«Flag».«Off»", "«Flag».«On»", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])

    it "should preserve guard assignment history and refuse false-successor redefinition":
        step("Add an ordinary local definition before a false guard and reject assigning it again later")
        for define_in_guard in [false, true]:
            var module = ee_lower(ee_guard_source(false))
            var function = ee_function(module, "select").unwrap()
            val incoming = ee_argument(function, 2).unwrap()
            var identity = 0
            for local in function.locals:
                if local.id.id >= identity: identity = local.id.id + 1
            val destination = LocalId(id: identity)
            function.locals.push(MirLocal(id: destination, name: nil, type_: incoming.type_, kind: LocalKind.Temp, is_ghost: false))
            val definition = ee_inst(MirInstKind.Copy(destination, incoming.id))
            val guard_index = ee_block_index(function, function.enum_matches[0].arms[0].guard_entry.unwrap())
            val fallback_index = ee_block_index(function, function.enum_matches[0].arms[1].body_entry)
            if define_in_guard:
                function.blocks[guard_index].instructions.push(definition)
            function.blocks[fallback_index].instructions.push(definition)
            function = ee_rehash(function)
            module.functions[function.symbol] = function
            if define_in_guard:
                ee_refusal(module, "EE-E-AVAILABILITY")
            else:
                ee_outputs(module, ["ee_m0_a0_guard", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])

        for both_arms in [false, true]:
            var module = ee_lower(ee_guard_source(false))
            var function = ee_function(module, "select").unwrap()
            val incoming = ee_argument(function, 2).unwrap()
            var identity = 0
            for local in function.locals:
                if local.id.id >= identity: identity = local.id.id + 1
            val destination = LocalId(id: identity)
            function.locals.push(MirLocal(id: destination, name: nil, type_: incoming.type_, kind: LocalKind.Temp, is_ghost: false))
            val first = ee_block_index(function, function.enum_matches[0].arms[0].body_entry)
            val fallback = ee_block_index(function, function.enum_matches[0].arms[1].body_entry)
            val merge = ee_block_index(function, function.enum_matches[0].merge_block)
            function.blocks[first].instructions.push(ee_inst(MirInstKind.Copy(destination, incoming.id)))
            if both_arms:
                function.blocks[fallback].instructions.push(ee_inst(MirInstKind.Copy(destination, incoming.id)))
            function.blocks[merge].terminator = MirTerminator.Ret(Some(ee_copy(destination)))
            function = ee_rehash(function)
            module.functions[function.symbol] = function
            if both_arms:
                ee_outputs(module, ["ee_m0_a0_guard", "_l{destination.id}", "(BitVec.ofInt 32 11)", "(BitVec.ofInt 32 22)"])
            else:
                ee_refusal(module, "EE-E-AVAILABILITY")

    it "should reject altered payload slot types and unknown bound adapter operations":
        step("Select the actual payload call and distinguish stale site hashes from structural adapter refusal")
        val source = "enum Packet:\n    Packet(i32, bool)\nfn select(value: Packet) -> i32:\n    match value:\n        case Packet.Packet(item, _): item\n"
        for mutation in [0, 1, 2]:
            var module = ee_lower(source)
            var function = ee_function(module, "select").unwrap()
            val selected = ee_root_call_site(function, "rt_enum_payload", true)
            val site = function.enum_matches[0].sites[selected]
            if mutation == 0:
                function.enum_matches[0].sites[selected].semantic_output_type = MirType(kind: MirTypeKind.Unit)
            else:
                val block_index = ee_block_index(function, site.block_id)
                val instruction = function.blocks[block_index].instructions[site.instruction_index]
                match instruction.kind:
                    case MirInstKind.Call(destination, callee, arguments):
                        match callee.kind:
                            case MirOperandKind.Const(_, type_):
                                val changed = MirOperand(kind: MirOperandKind.Const(MirConstValue.Str("rt_unknown_enum_adapter"), type_))
                                function.blocks[block_index].instructions[site.instruction_index] = ee_inst(MirInstKind.Call(destination, changed, arguments))
                            case _: assert(false)
                    case _: assert(false)
                function = ee_rehash(function)
                if mutation == 2:
                    val changed_kind = function.blocks[block_index].instructions[site.instruction_index].kind
                    function.enum_matches[0].sites[selected].exact_instruction_identity = sha256_text(serialize_mir_inst_kind(changed_kind))
            module.functions[function.symbol] = function
            if mutation == 0:
                ee_refusal(module, "EE-E-SITE: pattern instruction semantic type differs")
            elif mutation == 1:
                ee_refusal(module, "EE-E-SITE: actual instruction identity differs")
            else:
                ee_refusal(module, "EE-E-SITE: unknown native pattern adapter")
```

</details>
