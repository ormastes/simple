# Generic instantiation model (stage2 / 40.mono)

Status: design + executable model, 2026-10-10. Lane `work/rel-generics-complete-20261010`.
Scope: every place a type variable can appear or change in the pure-Simple compiler
(params, returns, annotated/unannotated locals, `var` reassignment, fields, impl
methods, nested generics, containers, fn-typed params and closures, every expression
position, recursion, cross-module use, explicit type args, inference).

Executable twin: `src/compiler/40.mono/model/generic_subst_model.spl` (pure, total
functions over a closed type grammar) with its property/refinement specs under
`test/01_unit/compiler/mono/model/`. Production code this refines:
`monomorphize_integration.spl` (`bind_type_params`, `infer_call_type_args`,
`rewrite_call`, `request_specialization`, `mangle_one`), `monomorphize/type_subst.spl`
(`substitute_type`), `monomorphize/mono_key.spl` (`canonical_type_id_of_hir`).

## 1. Objects

- **Type** `τ` ::= constant (`i64`, `f64`, `bool`, `text`, `unit`, …) | constructor
  application `K<τ₁..τₙ>` (Array, Slice, Optional, Dict, Result, Tuple, Function,
  Named(symbol), Union, Ref, Ptr, Isolated, Projection, Tensor) | **type variable** `α`
  (`HirTypeKind.TypeParam(name)`; lowering may also spell a function's own `T` as
  `Named(sym_of_T, [])`, which `canonicalize_template` rewrites to `TypeParam` before
  anything below runs).
- **Type-variable environment** `Γ` : the ordered list of a template's `type_params`
  (`fn f<A, B>` ⇒ Γ = [A, B]). Method templates of a generic impl extend the impl's Γ
  with their own type params (`impl<T> Box<T>: fn map<U>(…)` ⇒ Γ = [T, U]).
- **Substitution** `σ` : finite map from variable names to types
  (`TypeSubstitution.mapping: Dict<text, HirType>`). `σ(τ)` replaces every `TypeParam`
  bound in σ and recurses through every constructor; an unbound variable is left as-is.
- **Closed** type: no `TypeParam`, `Infer`, `Error`, `Any` anywhere (`hir_type_is_concrete`).
  Only closed types may become type arguments.

## 2. Substitution laws (checked by the model, see §7)

- S1 **Idempotence**: if `range(σ)` is closed then `σ(σ(τ)) = σ(τ)`.
- S2 **Composition**: `(σ₂ ∘ σ₁)(τ) = σ₂(σ₁(τ))` where
  `σ₂ ∘ σ₁ = { α ↦ σ₂(σ₁(α)) | α ∈ dom σ₁ } ∪ { α ↦ σ₂(α) | α ∈ dom σ₂ \ dom σ₁ }`.
- S3 **Closedness**: if every variable of τ is in `dom σ` and `range(σ)` is closed,
  then `σ(τ)` is closed. This is the post-mono invariant E-MONO-031 counts.

## 3. One-way unification (matching)

`match(π, τ, β)` unifies a *pattern* π (a declared parameter/return type, may contain
variables) against *evidence* τ (an argument/expected type) extending bindings β:

- `π = α`: if τ is not closed ⇒ **no evidence** (β unchanged, success). Else if
  `α ∈ β` ⇒ success iff `key(β[α]) = key(τ)`, otherwise **conflict**. Else bind `α ↦ τ`.
- `π = K<π₁..πₙ>`, `τ = K<τ₁..τₙ>` ⇒ match pointwise (`Slice<π>` also accepts `Array<τ>`;
  `Named` requires the same symbol and arity).
- `π = K<…>`, τ of a different constructor ⇒ **shape mismatch** (failure).
- π closed (no variable) ⇒ success without checking (type-checker's job).

Laws: U1 **soundness** `match(π, τ) = β ⇒ β(π) = τ` whenever τ is closed and
π's variables ⊆ dom β; U2 **most general** — β binds exactly the variables that
occur in π at positions where evidence exists, nothing else; any σ with `σ(π) = τ`
agrees with β on those variables.

## 4. Inference order (one call site)

Given template `f<Γ>(p₁..pₙ) -> r`, call `f<ε…>(a₁..aₙ)` in context expecting `e`:

1. **Explicit type arguments** ε (`type_args` on `HirExprKind.Call`): if present they
   must be closed and `|ε| = |Γ|`, and they are the instantiation. Argument evidence is
   still matched against `σ_ε(pᵢ)`; a disagreement is a **conflict error**, not a
   silent override.
2. **Argument evidence**: for each positional `aᵢ` with a known closed type `tᵢ`,
   `match(pᵢ, tᵢ)`. Named arguments ⇒ unresolved (fail closed). An argument whose type
   is unknown contributes nothing.
3. **Expected / return evidence**: `match(r, e)` when `e` is closed. `e` comes from
   the `let` annotation, the enclosing fn's declared return (for `return`/tail),
   the lambda's declared return, or an enclosing already-resolved call.
4. **Verdict**: every `α ∈ Γ` bound and closed ⇒ `Resolved([β(α) | α ∈ Γ])`.
   Otherwise `Unresolved(reason)` with reason ∈ {no_evidence, conflict, shape,
   named_args, explicit_arity, explicit_not_closed}. **Never a default**: a variable
   with zero evidence is never guessed as `i64`/`Any` (law I1).

Diagnostics: `E-MONO-032` for no_evidence/shape/named_args, `E-MONO-039` for an
explicit-type-argument conflict or arity error (new in this lane, fail closed).

## 5. Specialization key and identity

- **Key** `κ(f, [τ₁..τₙ]) = owner(f) ‖ "$" ‖ canonical(τ₁) ‖ "," ‖ … ` where
  `canonical` is `canonical_type_id_of_hir` (fully delimited: `[i64]`, `opt<text>`,
  `(i64,i64)`, `sym#<id><…>`, `fn(..)->..;e=[..]`). Laws: K1 deterministic;
  K2 **injective** on closed types: `κ(a) = κ(b) ⇔ a = b` structurally.
- **Display name** (LLVM symbol): `f$<mangle_one(τ)…>` joined by `_`, unchanged for
  the shapes it already handled (`pick$str`, `f$arr_i64`, `opt_`, `fn_`). It is *not*
  injective (`tup_i64_i64 + i64` vs `tup_i64_i64_i64`; `mangle_type` spelled Result/
  Slice/Ref/Ptr/Isolated as `unknown`). Dedup therefore uses κ, not the display name;
  when two distinct κ map to the same display name the later one gets a `_k<n>` suffix.
- **Cross-module identity**: the template's owner module is part of κ and the
  specialization is placed in the owner module; symbol ids are minted from
  `MONO_SYMBOL_BASE = 2^50` (outside any per-module table).

## 6. ABI of `T` per kind (what a specialization's IR must say)

| T kind | param/return/field lowering | evidence |
|---|---|---|
| i64/i32/bool/char | integer of declared width | `define i64 @f$i64` |
| f64/f32 | `double`/`float` | `define double @f$f64` |
| text | `ptr` (runtime string) | `define ptr @f$str` |
| struct/class/enum (Named) | aggregate by value / class handle per existing layout | `@f$Acc` |
| `[T]`, `Dict`, `T?`, `Result` | runtime value `ptr` | `@f$arr_i64`, `@f$opt_text` |
| `fn(..)->..` | `ptr` (FuncPtr), never `i64` | E-MONO-032 record 2026-10-09 |
| tuple | aggregate | `@f$tup_i64_text` |
The caller's `call` result type must equal the callee's `define` return type
(`generic_specialization_symbol_identity_llvm_spec`). Both backends (llvm, cranelift)
consume the same MIR, so the matrix is asserted at MIR type level plus LLVM text.

## 7. Verification plan (what is machine-checked and by what)

- The repo's proof lane is Lean 4 (`src/verification/*`, `scripts/check/check-lean-proofs.shs`).
  Lean is **not installed on the development host**; nothing in this lane claims a
  Lean-checked proof. `in:`/`out(ret):` contracts are type-checked but not discharged.
- Therefore the model's laws S1–S3, U1–U2, I1, K1–K2 are **bounded-exhaustively
  checked** in Simple: the spec enumerates every type of depth ≤ 2 over constants
  {i64, text, bool}, constructors {Array, Optional, Tuple₂, Fn₁, Named<1>} and
  variables {T, U}, and every substitution of {T, U} into closed depth-≤1 types; the
  universe sizes are printed and asserted > 0 (a vacuous sweep fails).
- **Refinement (differential) spec**: the same generated cases are converted to
  `HirType` and run through production `substitute_type`, `bind_type_params`,
  `hir_type_key`, `canonical_type_id_of_hir`; any disagreement with the model fails.
  The proof obligation is thus about the code that runs, over the stated universe.

## 8. Position × type-kind support matrix

Rows: where a type variable appears. Columns: T ∈ {scalar, text, struct/enum,
container ([T], T?, Dict), fn}. ✓ supported and specced; ◐ supported with a listed
restriction; ✗ refused fail-closed (diagnostic named).

| position | scalar | text | struct/enum | container | fn |
|---|---|---|---|---|---|
| fn param / return | ✓ | ✓ | ✓ | ✓ | ✓ (E-MONO-032 lane) |
| annotated local `val x: T` | ✓ | ✓ | ✓ | ✓ | ✓ |
| unannotated local from generic call | ✓ | ✓ | ✓ | ✓ | ✓ (callee return of a resolved spec) |
| `var x: T` reassignment, loop, match arm | ✓ | ✓ | ✓ | ✓ | ✓ |
| explicit `f<T>(…)` | ✓ (this lane) | ✓ | ✓ | ✓ | ✓ |
| generic struct field `a: T` | ✓ (BUG-IT-6) | ✓ | ✓ | ◐ `[T]`/`T?` fields: open, refused by MIR with a diagnostic | ✗ E-MONO-032 |
| impl method on generic receiver | ✓ imported (E-MONO-034) / same-file (this lane) | ✓ | ✓ | ◐ | ✗ |
| method with own type params | ✓ static; instance via Γ extension (this lane) or ✗ E-MONO-034 | ✓ | ✓ | ◐ | ✗ |
| closure capturing T / lambda arg | ✓ | ✓ | ✓ | ◐ | ✓ |
| call in string interpolation / try-catch / type-test | ✓ (BUG-IT-8) | ✓ | ✓ | ✓ | ✓ |
| cross-module template | ✓ | ✓ | ✓ | ✓ | ✓ |
| recursion `f<T>` → `f<[T]>` | ✗ E-MONO-030 beyond depth 16 (polymorphic recursion) |||||

Anything outside the matrix is a diagnostic (E-MONO-03x), never a silently erased
`Any`/`i64`: `post_mono_verify` (E-MONO-031, 035–038) is the backstop.
