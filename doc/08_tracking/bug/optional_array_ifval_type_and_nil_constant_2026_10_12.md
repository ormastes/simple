# Optional array binding type lost before MIR

The real new Simple producer rejects a 19-line Optional([any])/if-val loop with MirType.Tuple (3.974s, exit1, no object). Its HIR cache already records both `items` symbols as Array(Any). The four HIR val/var lowering paths infer the payload for the symbol but place only the explicit source annotation into HirStmtKind.Let.type_; that annotation is absent for `if val`. MIR deliberately reads the Let field instead of the symbol table, losing the proven payload type.

The candidate carries Array/Slice payload type into that existing Let field only when `bind_optional_payload` is true and no explicit annotation exists. All four existing val/var paths are covered. Ordinary `val items = input.?` keeps its nullable type; tuple, Any, scalar and record cases remain unchanged. No runtime tag, nil check, ownership, layout or API changes.

The earlier ExistsCheck-wide payload proposal is held and must not be applied: it could advertise a bare Array outside the guarded binding. The adjacent [HIR proposal](optional_array_ifval_type_and_nil_constant_2026_10_12_hir_proposal.patch) and [nil-copy proposal](optional_array_ifval_type_and_nil_constant_2026_10_12_nil_copy_proposal.patch) preserve these unqualified source changes. Its baseline is byte-identical to the actual producer990 source, so the body can be rebuilt through the existing cached bootstrap module path without importing unrelated source changes.

Seven real source/HIR/MIR SSpec regressions are authored and UNEXECUTED. The expanded native fixture was compiled in cycles2/3, both failing before object generation; the native program was never executed. Slice coverage is an explicit HIR input contract, not a claimed source spelling or native Slice execution. Existing Simple producer compilation fails before codegen; no after-performance or memory claim exists. The six other MCP I64 foreach sites read record fields and remain independent unresolved blockers.

## Cycle 2 and final correction

The HIR-only successor ad02eee compiled the unchanged 45-line fixture through HIR and MIR, then failed LLVM codegen in 4.325s with no object. Its retained IR emits `add ptr 3, 0` in four ExistsCheck None arms. The Some arm already copies an unwrapped i64 through `inttoptr` into the shared pointer slot, and the presence guard compares against `inttoptr(i64 3)`.

The final narrowly scoped correction emits raw i64 sentinel 3 and the existing typed copy only for Array/Slice None arms. It preserves sentinel identity, guards, ownership and ordinary nullable expressions. Root reviewed and approved this for the third and final feature cycle, not general acceptance. No runtime changes are proposed. Expanded native fixture bytes remain unchanged.

A broader backend defect remains separate: `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, method `translate_const`, renders every Int constant with `add {llvm_ty}`, although its type mapper in `llvm_type_text` maps Struct/Enum/Tuple/Array/Dict/Slice/Union to pointer. A general pointer-constant repair would require its own constant/type matrix and is not silently included here. The actual failure proves Array; other pointer-like combinations are source-identified exposure, not executed failures.

## Terminal status: OPEN, cycle cap reached

Final cycle3 exact cb8ce176 successor/unchanged99c36f fixture failed in4.304s, exit1/object0. Retained LLVM still contains `add ptr 3` in the retained cycle3 module. No link or native run occurred. The cause of the raw-word copy not surviving to valid LLVM is not yet proven; source owner hashes and compiler are unchanged, but no pre/post optimization trace was collected. Three separate negative fixtures and seven SSpec cases remain UNEXECUTED. No fourth build or negative compile is authorized for this feature. [Adjacent evidence JSON](optional_array_ifval_type_and_nil_constant_2026_10_12_evidence.json) binds actual evidence and the distinct backend constant-contract next diagnostic.

Authored regression and native reproducer bytes are preserved as adjacent `.spl.repro` report attachments, outside executable test discovery. They are not passing tests or skipped placeholders. The original private source files remain available for explicit future qualification.

Reproduction attachments: [seven authored SSpec cases](optional_array_ifval_type_and_nil_constant_2026_10_12_metadata.spl.repro) and [unchanged native fixture](optional_array_ifval_type_and_nil_constant_2026_10_12_native.spl.repro). The absolute paths inside the evidence JSON identify preserved execution artifacts; those files are not repository-relative links.
