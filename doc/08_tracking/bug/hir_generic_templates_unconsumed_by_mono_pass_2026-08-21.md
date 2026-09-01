# HIR generic templates are never consumed: `rewrite_module` is the identity, and `HirFunction` cannot even record template-ness

**Status:** OPEN
**Filed:** 2026-08-21
**Relates to:** #158 Phase B; plan `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md`

## Summary

Native-path monomorphization (#158 Phase B) is blocked by two independent
defects, neither of which is the four HIR Phase A gates themselves.

1. **The wired mono pass does nothing.** `run_monomorphization`
   (`src/compiler/40.mono/monomorphize_integration.spl:514`) IS wired as driver
   Phase 4 — `src/compiler/80.driver/driver_hir_pipeline_passes.spl:74`, called
   from `driver_orchestration.spl:197` and `:255` — but its `rewrite_module`
   (`monomorphize_integration.spl:407`) returns the module unchanged ("For now,
   return module unchanged"). No specialization is emitted and no call site is
   rewritten, so the pass is an expensive no-op.
   The real substitution engine under `40.mono/monomorphize/` (`engine.spl`,
   `type_subst.spl`, `rewriter.spl`) operates on **frontend AST**
   (`compiler.frontend.ast` `FunctionDef`/`StructDef`/`ClassDef`), not on HIR,
   and has **zero call sites** from the driver HIR path — only `note_sdn`,
   `metadata` and `partition` types are consumed, and only by the linker and
   `.smf` serialization.

2. **`HirFunction` has no `is_generic_template` field.** `HirStruct`
   (`20.hir/hir_definitions.spl:145`), `HirClass` (`:173`), `HirEnum` (`:213`)
   and `HirTrait` (`:342`) each carry the
   `is_generic_template / has_specialization_of / specialization_of /
   type_bindings` group. `HirFunction` (`:34`, ending at
   `verification_contract` `:69`) does **not**. Constructing one with that name
   fails semantic analysis with
   `class HirFunction has no field named is_generic_template` — measured
   2026-08-21, and it briefly broke
   `test/01_unit/compiler/hir/hir_function_span_populate_spec.spl` in another
   lane while being attempted.

## Why this mattered even before monomorphization

Every HIR lowering site hardcoded `is_generic_template: false`, so the flag was
a constant lie on the two types that *do* have it. Consequently every
downstream template check was dead code that could never fire:

- `src/compiler/50.mir/hwir/mir_to_hwir.spl:589` — `HWIR-E-GENERIC` reject
- the VHDL backend's equivalent reject
- `.smf` generic-template partitioning in `src/compiler/80.driver/smf_serialization.spl`
- `src/compiler/80.driver/driver_types.spl:253-313` cache-identity hashing

## What was fixed (2026-08-21)

The struct and class tiers now record template-ness truthfully:

- `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:605`
  (`lower_struct`) — `is_generic_template: struct_type_params.len() > 0`
- `src/compiler/20.hir/hir_lowering/_Items/class_declaration_lowering.spl:115`
  (`lower_class`) — `is_generic_template: class_type_params.len() > 0`

The generic-function gate was additionally routed through a single named
predicate `hir_generic_fn_is_template` (`declaration_lowering.spl:71`, gate at
`:281`) so the refusal condition and the future marking cannot drift apart. Its
behaviour, including the `SIMPLE_BOOTSTRAP` erasure escape hatch
(`bootstrap_erased_len_generic_is_safe`), is unchanged.

Pinned by `test/01_unit/compiler/hir/generic_template_marking_spec.spl`
(2 examples, both green; both asserted `false` before the change).

## What remains

1. Add the `is_generic_template` field group to `HirFunction`
   (`20.hir/hir_definitions.spl`). **Hazard:** that file's own construction
   sites warn that the seed fills partial named constructions POSITIONALLY, so
   the field must be added in declaration order and every construction site
   (including `test/01_unit/compiler/driver/hir_function_count_spec.spl`'s stub)
   re-checked. This is why it was not done in the same change: a full bootstrap
   was reading `src/compiler/20.hir/**` live as source at the time.
2. With that field present, mark the two remaining tiers:
   - `lower_function` — `hir_generic_fn_is_template(fn_.name, fn_.type_params.len())`.
   - the method loops in `lower_class`
     (`class_declaration_lowering.spl`) and `lower_impl`
     (`trait_impl_lowering.spl`). A method of a generic type is a template even
     when it declares no type parameters of its own — it can mention the
     OWNER's `T`, and `lower_function` only ever sees `fn_.type_params` (empty
     there), so the marking must be applied at those two call sites or the
     method body reaches MIR unmarked.
3. Implement `rewrite_module` / `process_specializations` on HIR (plan steps
   1-6), then relax the four Phase A gates into a post-Phase-4 sweep that errors
   on any declaration whose `type_params` are still non-empty after
   monomorphization (plan step 7).

## Do not relax the gates before step 3

The four Phase A gates
(`declaration_lowering.spl:281` and `:558`, `class_declaration_lowering.spl:58`,
`trait_impl_lowering.spl:190`) must stay loud until `rewrite_module` really
specializes. Marking a template is not monomorphizing it; letting an
unmonomorphized generic through today reproduces the original #158 silent
miscompile (a `text` field in a `T` slot truncated to a garbage integer, no
diagnostic).


## Update 2026-08-21 — HIR half of defect 2 is fixed (executed evidence)

`HirFunction` now HAS an `is_generic_template: bool` field
(`src/compiler/20.hir/hir_definitions.spl`, declared **last** on purpose: the
seed fills partial named constructions positionally, so a trailing field is
the only addition that cannot shift an existing named field's slot). All four
`HirFunction(` construction sites were audited and are fully named-field; no
positional construction remains.

Marked tiers:
- **Generic free fn / method lowered through `lower_function`** —
  `_Items/declaration_lowering.spl` sets
  `is_generic_template: hir_generic_fn_is_template(fn_.name, type_params.len())`,
  the same predicate that drives the Phase A loud gate, so marking and refusal
  cannot drift apart.
- **Flat bootstrap functions** — explicitly `false` (that tier carries no type
  params).
- **Trait methods / impl methods** — `_Items/trait_impl_lowering.spl` folds the
  trait-level / impl-level type params into each lowered method.

Executed evidence (`test/01_unit/compiler/hir/generic_template_marking_spec.spl`,
extended with the two fn-tier examples):

    ✓ marks a generic struct as a template and still reports the Phase A gate
    ✓ marks a generic class as a template and still reports the Phase A gate
    ✓ marks a generic free fn as a template (HirFunction tier)
    ✓ does NOT mark a concrete free fn as a template
    Results: 4 total, 4 passed, 0 failed

### Remaining, newly measured: impl-level type params never reach HIR

The impl-method marking is correct but **unreachable from source today**:
`parse_full_frontend` on

    struct Box<T>:
        v: T

    impl Box<T>:
        fn tag(self) -> i64:
            1

yields an `Impl` whose `type_params.len() == 0` (probe run 2026-08-21), so both
`lower_impl`'s Phase A loud gate (`_Items/trait_impl_lowering.spl:189`) and the
new marking are dead for that shape. The gap is in `10.frontend` (owned
elsewhere) and is the concrete next step for this tier; an example for it is
left out of the spec with a comment pointing here rather than asserted as
passing.

Still open and unchanged: defect 1 (`rewrite_module` is the identity function),
so nothing downstream consumes the now-truthful flag yet.

## Update 2026-08-21 (later): defect 1 is FIXED — the pass really specializes

`rewrite_module` is no longer the identity. The seam chosen is **HIR-level
rewriting inside `40.mono`**, not driving the AST engine from the HIR path,
because:

- at driver Phase 4 the frontend AST is gone; only `Dict<text, HirModule>` is
  in hand, so an AST-level engine has nothing to consume;
- the "AST-level engine" framing above was only half right. `engine.spl` is
  already typed on HIR (`specialize_function_with_types(func: HirFunction,
  type_args: [HirType]) -> HirFunction`, `substitute_function`); what was
  actually missing is that `type_subst.spl` stubbed **every** substitution to
  the identity (`substitute_type` returned `ty`, `concrete_to_hir_type`
  returned `HirTypeKind.Error`). `rewriter.spl`/`analyzer.spl` remain the
  unused text-keyed port and are still uncalled.

What landed:

- `40.mono/monomorphize/type_subst.spl` — real recursive `substitute_type`
  (replaces `TypeParam(name)` through Tuple/Array/Slice/Dict/Ref/Ptr/Optional/
  Isolated/Result/Named args/Union/Function), real `concrete_to_hir_type` for
  the forms that carry enough information (`Named`/`Specialized`/`Pointer`
  stay `Error` rather than fabricating a `SymbolId`), and `substitute_function`
  now substitutes PARAMETER types as well as the return type.
- `40.mono/monomorphize_integration.spl` — a SymbolId -> name map built while
  collecting (the old `symbol_id_to_name` returned the placeholder `"sym_{id}"`
  and therefore matched no generic function, so `check_generic_call` could
  never fire); real `process_specializations` that emits a specialized
  `HirFunction` per request with a freshly allocated `SymbolId`; and a
  `rewrite_block`/`rewrite_stmt`/`rewrite_expr` walk that inserts the
  specializations into `module.functions` and repoints each generic call site
  at the specialization with EMPTY `type_args`.

Pinned by `test/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.spl`
(`Results: 3 total, 3 passed, 0 failed`; `2 failed` with the `40.mono` change
stashed). Pre-existing unrelated reds confirmed unchanged by the same
stash A/B: `monomorphize_integration_spec.spl` 17/18,
`monomorphization_native_build_regression_spec.spl` 1/2.

### Still open

- **The four Phase A gates stay closed.** They must: nothing here has been
  demonstrated end to end from SOURCE, because the generic-`fn` gate is what
  prevents a generic `HirFunction` from ever existing on the source path — the
  spec builds HIR by hand for exactly that reason. Opening a gate requires the
  edit in `_Items/`, which this lane does not own.
- `substitute_expr` still substitutes only an expression's own recorded type;
  it does not recurse into sub-expressions (TODO in the file). A specialization's
  BODY therefore still carries the template's expression types. That is why the
  gates must not open on this change alone.
- Method-in-impl and generic struct/class specialization are not emitted; only
  free generic functions are.
- The `SIMPLE_BOOTSTRAP=1` erasure escape is UNCHANGED and still required — it
  lives in HIR lowering (`bootstrap_erased_len_generic_is_safe`), not in this
  lane, and nothing above makes it removable.

## Frontend fix 2026-08-21: `Impl.type_params` was always empty for `impl Box<T>:`

**Root cause (10.frontend).** `parse_impl_decl`
(`src/compiler/10.frontend/core/parser_decls_use.spl`) called
`parse_type_params()` only for the leading `impl<T> ...` form. For the form the
language actually uses — `impl Box<T>:` and `impl Trait for Box<T>:` — the type
parameters sit INSIDE the target type, and the target was handed to
`parser_parse_type()`, which merely CONSUMES `<T>` and discards the names. The
`Impl` node therefore always got `type_params.len() == 0`, which is why
`lower_impl`'s Phase A generic-impl gate could never fire and the impl-method
tier of `is_generic_template` marking in
`20.hir/hir_lowering/_Items/trait_impl_lowering.spl` was unreachable from source.
The `_FlatAstBridge/module_assembly.spl` tag-"9" path already forwarded
`decl_get_type_params` correctly; the names simply never arrived.

**Fix.** New `parse_impl_target_type()` parses the impl target as an identifier
path with optional generic arguments and returns the type-parameter names it
carries (falling back to `parser_parse_type()` for any other target shape).
Names from both the trait-position and self-position targets are merged into the
impl's `type_params`, deduplicated against any explicit `impl<T>` list. A type
argument counts as a parameter only when it has an uppercase initial, so
`impl Box<i64>:` stays concrete with zero params.

**Test.** `test/01_unit/compiler/frontend/impl_head_type_params_spec.spl` — 5
examples (inherent generic, trait impl, multi-param, concrete impl,
concretely-instantiated impl). Verified failing before the fix (`5 examples, 3
failures`, the two zero-param cases passing trivially) and `5 examples, 0
failures` after. `lint-cached.shs` on the changed file: `Lint passed`.

**HIR gates.** Not observed firing from this lane: `bin/simple` is currently the
Rust seed, so a `bin/simple run` of a generic impl does not traverse the
pure-Simple HIR path. What changed is only that the gate is now REACHABLE — the
AST carries the impl's type params. If the Phase A gate starts firing for the
impl-method tier, that is the expected consequence of this fix, not a regression
of it.

## 2026-08-21 — body substitution hole CLOSED

**Hole.** `substitute_expr` substituted only an expression's OWN recorded type
and never recursed; `substitute_function` never touched `func.body` at all. A
specialization therefore had a concrete SIGNATURE and a body still carrying the
template's `TypeParam` types — a silent miscompile, since nothing downstream of
Phase 4 diagnoses a leftover type parameter.

**Fix** (`src/compiler/40.mono/monomorphize/type_subst.spl`). `substitute_expr`
now recurses through every `HirExprKind` variant that holds a nested expression,
block, pattern, closure parameter or call type argument; new
`substitute_block` / `substitute_stmt` / `substitute_pattern` / `substitute_asm`
plus optional/list helpers cover statements, match arms, comprehension clauses,
`with` items, enum and pattern payloads, and inline-asm operands.
`substitute_function` now sets `specialized.body = substitute_block(...)`.
`concrete_to_hir_type`'s conservatism is unchanged: `Named`/`Specialized`/
`Pointer` still yield `Error` rather than fabricating a `SymbolId`.

**Also fixed to get there.** The pass was red on the deployed seed with
`semantic: undefined field: unknown property, key, or method 'mangled' on Dict`
— a `PendingSpec` struct value round-tripped through an ANY-erased class field
arrives as a Dict. `pending_specs: [PendingSpec]` is now the parallel
`pending_mangled: [text]` + `pending_names` / `pending_type_args` dicts, and the
struct is gone. (Renaming it away from the colliding
`70.backend/backend/vhdl/vhdl_testbench_source.spl:104 class PendingSpec` was
NOT sufficient — the erasure, not the name collision, was the cause.)

**Test.** `test/01_unit/compiler/mono/hir_monomorphization_body_subst_spec.spl`
— specializes `fn box_it<T>(v: T) -> [T]` (a `let` annotated `T`, an array
literal with elem type `T` and two `T`-typed elements) and walks the WHOLE
specialized body asserting zero surviving `TypeParam`. A/B proof with only the
`type_subst.spl` change reverted: `Results: 3 total, 2 passed, 1 failed` (the
body walk fails) → `Results: 3 total, 3 passed, 0 failed` after.
`hir_monomorphization_rewrite_spec.spl`: `3 total, 0 passed, 3 failed` (the
`mangled` error) → `3 total, 3 passed, 0 failed`. Also green:
`monomorphize_integration_spec` 18/18, `monomorphize_spec` 1/1,
`generic_template_spec` 20/20.

**Phase A gates.** Deliberately NOT opened here — that remains a separate
decision. The substitution hole that blocked opening them is closed.

## Update 2026-08-21 (step 12): consumed templates are no longer emitted

Plan `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`
section 9.3 **step 12** ("Remove or mark generic templates non-emittable") is
implemented in `src/compiler/40.mono/monomorphize_integration.spl` as a new
Step 5 of `process_modules`: `prune_consumed_templates`, driven by
`template_was_specialized`.

Rule, fail-closed on three axes:

- a definition is a candidate only when it is genuinely generic
  (`type_params` non-empty **or** the HIR `is_generic_template` flag set), so a
  non-generic function can never be dropped;
- it is dropped only when a specialization of that exact name actually reached
  `specialized_functions` (a request that produced no definition licenses
  nothing);
- a specialization is never a candidate — its mangled name carries `$` and so
  cannot equal a template name.

**A generic template with ZERO instantiations is deliberately KEPT.** It is
unreachable and must not be emitted, but removing it here would hide the
remaining half of this bug: **MIR lowering does not skip it.**
`src/compiler/50.mir/_MirLowering/module_lowering.spl:981` (`lower_module`)
iterates `module.functions.values()` with no `type_params` / template check —
that is the exact line a skip belongs on, owned by another lane, so it was not
edited here. Until it lands, an uninstantiated generic template still reaches
canonical MIR; the post-mono verifier's `generic_emitted_definition` counter is
what catches it.

### Executed evidence

- `sh scripts/check/check-post-mono-invariants.shs` -> `PASS — 9 fixture(s)
  checked, 0 unexpected`. The real-pass fixture
  `test/fixtures/mono/post_mono/real_mono_pass_output.spl` now expects `clean`
  (was `generic_emitted_definition=1`); it reported `BAD ... expected
  [generic_emitted_definition=1] got [clean]` against the un-updated header,
  which is the before/after A/B for this change.
- New reproduce spec `test/01_unit/compiler/mono/mono_template_pruning_spec.spl`
  (mirrored to `test/unit/`): `Results: 4 total, 4 passed, 0 failed` — template
  removed, specialization present, non-generic neighbour untouched, and a
  zero-instantiation template kept.
- `test/01_unit/compiler/mono/verify/post_mono_verify_spec.spl`:
  `Results: 9 total, 9 passed, 0 failed`.
- Three examples asserted the OLD "template survives" behaviour and were
  updated in place with a superseded-by note rather than deleted:
  `hir_monomorphization_rewrite_spec.spl` ("removes the consumed generic
  template ...", 3/3) and `hir_monomorphization_body_subst_spec.spl` ("removes
  the consumed template rather than mutating it in place", 3/3).
- Whole `test/01_unit/compiler/mono` suite after the change, all green:
  generic_template 20/20, mold_pure 21/21, mono_cache_efficiency 1/1,
  monomorphize_integration **18/18** (was 17/18 before this lane),
  monomorphization_native_build_regression **2/2** (was 1/2), monomorphize 1/1,
  note_sdn 1/1, note_sdn_bdd 1/1, deferred_deserialize_byte_text 3/3.

### Still open

- MIR lowering's missing template skip (line cited above).
- The four Phase A HIR gates stay closed; nothing here is demonstrated from
  SOURCE.
- `substitute_expr` still does not recurse into sub-expressions.
