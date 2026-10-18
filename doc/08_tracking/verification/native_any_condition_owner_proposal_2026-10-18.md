# Native Any condition owner proposal — 2026-10-18

Status: source draft, all executable checks UNRUN. This is a future executing-producer repair, not another assertion-fixture retry. The active BDD matrix, frozen producers and all existing receipts are unchanged. Authoritative bug/tag reconciliation belongs to other sessions.

## Actual observed owner failure

The cycle2 BDD negative executable passed tagged false 0x13 to untyped assert_true, whose native body tested the raw word for nonzero. Its failure branch was skipped. Actual retained HIR establishes that the parameter is HirTypeKind.Any, tag24, not Infer, tag21. The condition VarRef has no expression type annotation.

HIR: `C:/dev/p4bdd2-cache/positive/hir/20b22ac6161627eef21c9b55012bf6813abb710be73de1b3fec8df463cb7f04c.parser-v4.hir`, SHA-256 `21012619dd1dbfae2ff71945916df97e3593639d28891fa1560372bd1836031c`. Bounded decoded evidence: `C:/dev/p4bddplan/cycle2-assertion-actual-hir-types.txt`. The underlying COFF evidence is preserved in the cycle2 disassembly artifacts.

The independent final generic-assertion cycle subsequently qualified concrete bool and typed i64/Optional cases, but its strict erased-Any negative still failed qualification: one passed case and one failed case instead of two failures. The owner reports real assert_true$unknown/assert_false$unknown bodies still testing the raw word, with no tag decode. Evidence: `C:/dev/p4bddplan/cycle3-erased_truthiness_negative-terminal-audit.json` and `cycle3-erased_truthiness_negative-1-assertions.disasm.txt`. These are results from the separate completed matrix, not execution of this compiler draft or its new fixture. No fourth assertion cycle is proposed.

Executing f048 `_MirLowering/function_lowering.spl` maps each parameter symbol to its actual argument local and calls `remember_local_hir_type(local.id, param.type_, ...)` before lowering its body. Its Any arm also marks that local as a tagged runtime value. The Any type-lowering arm deliberately uses an i64 tagged slot subject to the existing assurance policy. Therefore `find_local_hir_type` can identify this actual untyped assertion parameter even though the VarRef lacks an annotation. No inference variable or arbitrary i64 is evidence of this ABI.

## Minimal owner change

The change is isolated to `MirLowering.lower_cond_operand` in `mir_lowering_stmts.spl`:

1. Evaluate the expression once through the existing dispatcher.
2. Retain the existing Optional/Nil presence path and its precedence.
3. Identify Any from the registered local HIR owner and require its actual MIR slot to be I64. Only when that HIR owner is absent may an Any expression annotation recover the classification, again requiring an actual MIR I64 slot. A normalized MIR Bool is never decoded as tagged Any through either path.
4. Emit the existing `rt_value_truthy(i64) -> bool` call for the proven Any condition.
5. Keep concrete bool/int/float, unresolved Infer and other conditions on their existing paths. Preserve all assurance diagnostics and runtime-value metadata.

The runtime provider already exists in the actual C cohort (`runtime.h` int8_t return and `runtime_native.c` implementation); root also confirmed the corresponding owned Rust runtime ABI. No provider, handwritten tag decoder or public assertion API is added. The returned normalized Bool flows through the existing branch/not/and/or lowering. MC/DC wrapping remains in `lower_cond_expr`, so decoding does not introduce a duplicate condition probe.

The new path adds one existing runtime predicate call per evaluated Any condition and no allocation or specialization loop. Existing local HIR lookup is reused; either candidate Any path additionally checks the actual MIR local type. Performance measurements are UNRUN. Global masking of I64 branch operands would misread raw integer19 as tagged false and is explicitly avoided.

Third and final bounded source-review revision: independent review found that `lower_assign_var` copies into an existing local, updates the runtime-value flag and remembers the RHS HIR type without changing the destination MIR storage. Thus registered Any metadata alone does not prove I64 storage; both detection paths now require it. The actual failed assertion parameter remains covered because its parameter ABI is proven I64. This prevents an added decode of an already normalized Bool; it does not claim to repair or execute that separate assignment scenario. All executable checks remain UNRUN.

## Established semantics and unresolved distinctions

Existing `test/01_unit/compiler/any_value_condition_spec.spl` requires erased false/nil/zero to be false and true/nonzero/nonempty text to be true, including if/or/not and untyped-list elements. The existing condition-tag regression separately pins statically Optional conditions to presence and documents pre-existing runtime/interpreter truthiness disagreement.

| Input and static owner | Proposed path | Scope |
|---|---|---|
| Any false/true, nil, integer zero/nonzero | Existing runtime-value predicate | Observed bool defect and existing regression contract |
| Any finite float zero/nonzero | Existing float-aware runtime-value predicate | Real regression fixture added, UNRUN |
| Typed bool and i64, including raw19 | Existing native condition path | Regression controls added, UNRUN |
| Typed bool? Some(false)/nil | Existing rt_is_some presence path | Regression controls added, UNRUN |
| Any non-null heap text/array/dict/record | Existing runtime-value predicate regards heap as true | Preserves prior nonzero-heap behavior; not a claim about empty-value presence semantics |
| Any boxed Option.None | Heap remains true under the existing runtime-value table | Not unified with statically Optional presence; existing ambiguity remains |
| Any NaN | Existing C predicate uses !=0.0 and returns true | Pure-Simple RuntimeValue documentation differs; no parity claim or NaN policy change |
| Postfix .? | Existing separate condition branch | No change; collection emptiness/presence unification is outside this repair |

Thus this proposal repairs proven tagged-value decoding without pretending to settle every language-level truthiness disagreement. A future semantic unification would need its own explicit contract and tests. It must not be inferred from this change.

## Real regression fixture and future qualification

`test/fixtures/compiler/any_condition_owner/main.spl` imports the real sibling provider. It uses direct nonzero exit oracles, not std.spec. The provider contains an actually untyped parameter, an explicitly Any parameter, Any return values and concrete scalar/Optional controls. Checks cover if/not/and/or/while, typed local and call-return ownership, untyped list elements, raw i64 value19, finite float values, and single evaluation/short-circuit side effects. The expected successful stdout is `native-any-condition-owner-pass` plus LF, empty stderr and exit0. No fake truthiness helper or replacement runtime object is used.

No fixture was compiled or executed. An unchanged b441 producer cannot execute the changed compiler owner; compiling this fixture with b441 could only characterize the old failure, not qualify the repair. A future admitted producer containing this source, or a dedicated actual parser/HIR/MIR owner harness that executes the new lowering, is required. Preserve canonical source closure and all real runtime dependencies. Do not weaken Any assurance policy to make the test admissible.

Before promotion, verify actual normalized predicate calls and argument/return ABI, passing direct branch oracles and negative controls, absence of predicate calls for typed i64/Bool, Optional presence and no duplicate evaluation. Required compiler/lib/MCP/LSP checks and applicable smoke gates remain UNRUN. No new producer/bootstrap, native test, deployment or fourth BDD attempt is authorized by this proposal.
