# Generic instantiation and the generic flow rule (40.mono / 50.mir)

Status: 2026-10-10, lane `work/rel-generics-complete-20261010`. This note states the rule,
what the code does today, what is checked and how, and every hole found. Nothing here is a
machine-checked proof; §7 says exactly what kind of evidence each claim has.

Code: `src/compiler/40.mono/monomorphize_integration.spl`, `monomorphize/type_subst.spl`,
`50.mir/_MirLoweringExpr/expr_dispatch.spl` (field reads). Model:
`src/compiler/40.mono/model/generic_subst_model.spl` (+ `generic_subst_universe.spl`).

## 1. Objects

- **Type** τ: a constant (`i64`, `text`, …), a constructor application (Array, Optional, Dict,
  Tuple, Function, Named(symbol, args), …) or a **type variable** α (`TypeParam(name)`; HIR
  also spells a declaration's own `T` as `Named(sym_of_T, [])`, which `canonicalize_template`
  / `typesubstitution_canonical` rewrite to `TypeParam` first).
- **Γ**: the ordered type parameters of a template. A method of `impl<T> Box<T>` is a
  template over the impl's Γ with the receiver as parameter 0.
- **Substitution** σ: finite map variable → type; σ(τ) replaces bound variables at every
  depth and leaves unbound ones.
- **Closed**: no `TypeParam`/`Infer`/`Error`/`Any` anywhere (`hir_type_is_concrete`). Only a
  closed type may be a type argument.

## 2. The generic flow rule

> A type argument is fixed **at a call site** (or a constructor / receiver) from *evidence*:
> written type arguments, the types of the arguments, the expected type. From there it is
> carried by **substitution only**. Therefore the type of every value that can reach a
> generic call, a generic field read or a generic method receiver must be known *after each
> way a value changes variable*; where it is not known the site is **refused with a
> diagnostic**, never bound to a default.

Two places need a type and have no type checker to ask (the native path has no expression
type inference pass):

1. **40.mono, `infer_expr_type`** — the argument types of a generic call. It is deliberately
   partial; `nil` means "no evidence" and the call site fails closed (E-MONO-032).
2. **50.mir field reads** — the representation of a field declared with a type parameter.
   40.mono knows the instance type of the base and **stamps** the read (`has_type_`/`type_`)
   with the field type at that instance; 50.mir takes the stamp, else the construct-site
   record of the same function, else the base local's HIR type arguments; a bare-parameter
   field none of them can type keeps the template lowering (a value of a struct named after
   the parameter), so an operator on it is refused (`operator overload for struct T`).

### Per variable-change kind

| kind | how the type is carried | status |
|---|---|---|
| annotated `val x: A = e` | declared type → `env` | ✓ |
| unannotated `val x = e` | `infer_expr_type(e)` → `env` | ✓ for the expression forms below |
| `var` reassignment | type of the declaration (never re-inferred) | ✓ |
| unannotated let **inside a template** | no declared type: nothing to substitute (was a crash) | ✓ fixed |
| parameter | declared type → `env`; in a specialization, the substituted type | ✓ |
| return | callee's declared return under the call's own instantiation (`val a = keep("x")`) | ✓ fixed |
| return (expected-type evidence) | declared return of the enclosing fn / let annotation | ✓ (pre-existing) |
| field of a non-generic struct | declared field type, owner-module aware | ✓ |
| field of a generic instance `b.item`, `b.items` | declaration under [params := instance args] | ✓ fixed (mono) + stamp (MIR) |
| constructor `Box(item: "x")` | field declarations matched against the arguments → `Box<text>` | ✓ fixed |
| array element `xs[i]`, dict value `d[k]`, tuple slot | element / value / slot type | ✓ fixed |
| optional `o ?? d`, `o!` | payload type (still optional when `d` is the same optional) | ✓ fixed |
| `if val v = o` | **the optional itself** (HIR lowers it to `v = o.?`) | ◐ H-IFVAL |
| closure capture | captured symbol keeps its `env` type | ✓ |
| lambda parameter | declared type only | ◐ untyped → refused |
| pattern binding (enum payload, tuple) | declared payload type / tuple slot | ✓ (pre-existing) |
| loop variable | element of an array/slice; `i64` for an `i64..i64` range | ✓ range fixed |
| computed value (`+`, comparison, `if` expression) | builtin operator on primitive operands; agreeing arms | ✓ fixed |
| method result on a generic receiver | method template's return under the receiver's args | ✓ fixed |
| builtin method result (`s.trim()`), `match` as a value | — | ✗ refused (E-MONO-032) |

## 3. Matching and inference (unchanged contract, now checked)

`bind_type_params(π, τ)`: a variable against non-closed evidence binds nothing; a bound
variable must agree structurally (`hir_type_key`), else conflict; constructors must agree
(Slice also accepts Array), else shape mismatch; a parameter-free pattern never fails here.

Call site: written type arguments, else argument evidence, then expected-type evidence;
every Γ variable must end up bound to a closed type, otherwise the site is unresolved
(E-MONO-032). **Never a default.**

Changed here: `hir_type_key` is structural at every depth. It used the engine mangling for
nested positions, which spells `Result`/`Slice`/`Ref`/a function type `unknown`, so
`[fn(i64) -> bool]` and `[fn(text) -> bool]` agreed as witnesses of one `T`.

## 4. Specialization identity

### Executable model key encoding

The model's `mk_key` uses a separate structural encoding rather than
`mt_render` display text. A text component is its decimal length, `:` and its
unchanged contents. Types start with `v` (variable), `c` (constant), or `a`
(application); applications include a framed constructor name followed by
`l<arity>:` and recursively encoded children. The complete key frames module
and function names independently, then includes the encoded type-argument list.
This disambiguates delimiter-bearing names, empty applications, nesting and
argument boundaries. For example, `m::f<i64>` has model key `m1:mf1:fl1:c3:i64`.

The motivating counterexample is closed `Con("Box<i64>")` versus
`App("Box", [Con("i64")])`: their display text is identical. Owner `a::b` with
function `c` also shared the old key with owner `a` and function `b::c`.
The law spec now compares structural keys in the finite universe and adds
explicit adversarial regressions. These are pending executable validation on an
admitted self-hosted runner; no arbitrary-term key proof is claimed. Production
key encodings remain separate: differential assertions compare identity
equivalence or distinctness, not byte-for-byte equality with model key text.

- One specialization per (template, structural `type_key` of the type arguments). The display
  (symbol) name is the old mangling; when two different instantiations mangle alike
  (`keep<Result<i64, E>>` / `keep<Result<bool, E>>` are both `keep$unknown`) the later one is
  `…_k<n>` instead of silently sharing the first body.
- `type_key` spells a declared type by its **name**, like the mangling, because a type
  argument's SymbolId is local to the module that wrote it. Two modules that each declare a
  type of the same name therefore still share a specialization — hole H-NAMED.
- Symbol ids: one pass-wide counter from `MONO_SYMBOL_BASE` (2^50); the id-space rule is
  written at that constant (land branch `work/rel-generic-abi-land-20261010`).

## 5. ABI per kind of `T`

| T | representation of a param / return / field at T | pinned by |
|---|---|---|
| integer / bool / char | integer word of the declared width | `generic_specialization_symbol_identity_llvm_spec` |
| f64 / f32 | `double` / `float` | same |
| text | `ptr` | same; `generic_struct_composite_field_spec` (method result) |
| struct / class / enum | aggregate / handle per existing layout | same |
| `[T]`, `T?`, Dict, Result | runtime value `ptr` | same |
| `fn(..) -> ..` | `ptr` | `generic_walker_fn_param_abi_spec` (incl. riscv32) |

The caller's `call` type must equal the callee's `define` type. Nothing in this lane depends
on pointer width; H-RET32 below is the one known place where a 64-bit assumption leaks.

## 6. Diagnostics

E-MONO-030 polymorphic recursion past depth 16; E-MONO-032 type arguments neither written nor
inferable; E-MONO-031/035–038 post-mono verification. These are always errors.

Two diagnostics can be met in code that compiles today and are therefore **leveled**
(`SIMPLE_MONO_LEVELS="E-MONO-034=error,E-MONO-040=off"`, values `error | warning | off`,
resolved by `mono_diag_level`; the driver prints warnings through `add_warning`):

- **E-MONO-034** (default `warning`) — method of a generic impl that cannot be specialized
  for a known receiver (trait impl, own type parameters, `Owner__method` clash across
  modules). The call stays the unspecialized method call it was before the check existed.
  Census (review round 2): 0 sites in `src/compiler`, about 92 in `src/lib` + `src/app`.
- **E-MONO-040** (default `warning`, new) — a container field over a type parameter
  (`items: [T]`, `first: T?`) is read from a receiver whose instance is unknown; reported
  once per field and module. See H-ANNOT.

Rule for this lane: nothing may turn a module that compiles today into a hard error without
such a switch. The restored 50.mir refusal "operator overload for struct T" is not new: every
unknown-instance route refuses on release without e6a135b3296 (measured: the "refused" group
of `generic_struct_field_instance_paths_spec` is green there).

## 7. Evidence — what is proven, what is only checked

- **Machine-checked model laws:** the manual `GenericSubstModel` Lean target now
  proves substitution laws for the three-constructor `MType` shape, arbitrary
  argument lists and the unknown sentinel (section 11). This is not a proof of
  executable Simple code or HIR refinement. Earlier bounded sweeps below remain
  finite evidence; `in:`/`out:` contracts are not discharged by running the seed.
- **Bounded-exhaustive (Simple code enumerates a finite universe; a claim holds for every
  element of it and for nothing else).** Universe: atoms {i64, text, bool, 'T, 'U}; depth ≤ 1
  = atoms + Array/Optional/Box of an atom + Tuple/Fn/Dict of two atoms (95); plus
  Array/Optional/Box of each non-atom (365 types, 147 closed); 81 substitutions of {T, U} into
  8 closed types. Sizes are asserted, so a vacuous sweep fails.
  - `generic_subst_model_laws_spec` (13 examples): S1 idempotence and S3 closedness
    (29,565 cases), S2 composition (152,000), U1 soundness / U2 most-general matching (6,080),
    U3 conflict / shape / open evidence, I1 "no evidence ⇒ unresolved, never a default"
    (2,304), K1 key determinism, K2 key injectivity (21,609 pairs; 1,668 argument lists).
  - `generic_subst_model_flow_spec` (20 examples): for each of the 19 variable-change kinds,
    F1 a well-typed step stays well typed at the substituted type under every substitution,
    F2 closed inputs give a closed result, F3 no variable is invented. The field kinds need a
    precondition the sweep found necessary: the declared field type must be closed over the
    struct's own parameters.
  - `generic_subst_model_refinement_spec` (6 examples): the **production** functions against
    the model over the same universe — `substitute_type` (9,125 cases), `hir_type_is_concrete`
    (365), `bind_type_params` verdict and bindings (5,225), `hir_type_key` and
    `MonomorphizationPass.type_key` injectivity (21,609 pairs). This is a differential test,
    not a refinement proof.
- **Example-tested.** `generic_variable_flow_spec` (37: one per kind of §2, including the
  refusals), `generic_struct_composite_field_spec` (11), `generic_struct_field_instance_paths_spec`
  (14), `generic_struct_type_param_field_spec` (7). The MIR specs read the LLVM text of one
  named function and count only `call` lines: the runtime's `declare ... @rt_strcat` is in every
  module, so `ir.contains("rt_strcat")` (the first BUG-IT-6 spec's assertion) could never fail.

A note on the sweep itself: it caught its own first universe (380 "types", 15 of them
duplicates) through the size assertions.

### What the model and the differential do NOT cover

- **`infer_expr_type`** — the part of 40.mono that changed most in this lane — has no model.
  It is example-tested only (`generic_variable_flow_spec`).
- **The symbol spelling of a type parameter.** HIR emits a declaration's own `T` as
  `Named(sym_of_T, [])`; the differential feeds `substitute_type` / `bind_type_params` the
  `TypeParam(name)` spelling only, so `TypeSubstitution.by_symbol` and
  `typesubstitution_canonical` are covered by the example specs, not by the sweep.
- **Constructors outside the universe**: Result, Ref, Ptr, Isolated, Union, Projection, Tensor,
  DynTrait, tuples of more than two members, functions of more than one parameter, effects,
  fixed array sizes. `hir_type_key` / `type_key` ignore array sizes, function effects and the
  *values* of tensor dimensions (only their count) by design; two types differing only there
  share a key.
- **A zero-argument nominal pattern** (`p: Acc`) matches anything in production
  (`bind_type_params` cannot compare module-local ids) and has no counterpart in the model,
  whose named types always carry one or two arguments.
- **`mangled_name` / `_k<n>`** is covered since review round 2: the refinement spec checks the
  display name against structural equality over 1,671 type-argument lists (the universe's 147
  singles and 1,521 pairs, plus three lists chosen because their display names clash). Inside
  the universe the display mangling happens to be injective, so without those three the
  suffix path would not run. Two key-sharing defects were found in this area by reading, which
  is why it is in the sweep now; both also have permanent example specs (review probes P1, P2).
- Nothing here says anything about 50.mir or codegen; those are example-tested.

## 8. Holes

Fixed in this lane (each has a spec that was red first, except where noted):

| id | hole | fix |
|---|---|---|
| BUG-IT-3 | `Box<i64>(item: 7).get()`: receiver untyped, method never specialized, undefined symbol at link | constructor typing + method-result typing; callee signature stamped (text result is `ptr`) |
| F-LET-T | unannotated let inside a template aborted substitution (`substitute_type(nil)`) | Let arm skips an absent type — owned by another lane, see STATUS |
| F-RET | `val a = keep("x")` left `a` untyped | generic callee return under its own instantiation |
| F-FIELD | `b.item` / `b.items` on a generic instance untyped in 40.mono | generic field tables by ownership identity |
| F-ELEM | `xs[i]`, `d[k]`, `t.0`, `o ?? d`, `o!`, binary/unary, `if` value, dict literal untyped | new `infer_expr_type` arms |
| F-RANGE | `for i in 0..n` loop variable untyped | bound to i64 for i64 bounds |
| K-SHARE | two instantiations with one mangled name shared a body | structural `type_key`, `_k<n>` (found by reading; the reviewer's probe P1 was red on the pre-fix tree and is a permanent example now) |
| K-BIND | witnesses differing only inside a nested fn/Result/Slice type agreed | structural `hir_type_key` (same: probe P2) |
| E6-LEAK | per-instance field record never reset per function | reset with the other per-function tables |
| E6-SILENT | unknown instance: integer add of two field words instead of the refusal | template lowering kept for an untyped bare-parameter field |
| F-RET-NOM | same-module `fn wrap<T>(x: T) -> Acc` / `-> Box<T>` / `-> [Acc]`: call typed `i64` against `define ptr` | the stamped signature of a local specialization types the call's RETURN (a field read on that result is still an unknown instance, H-ANNOT) |
| F-CONT | `[T]` / `T?` field of an instance **built in the function** (or otherwise known to 40.mono): element / payload typed by the declaration (`T`) → `text` elements added as integers | mono stamp + `struct_field_over_type_param`. Through a parameter it is still wrong — H-ANNOT / E-MONO-040 |

Open:

| id | hole | behaviour today |
|---|---|---|
| H-ANNOT | the arguments of a **same-module** generic type annotation are dropped before HIR (`r: W<text>`, `-> W<text>`, field `w: W<text>` arrive as bare `W`; only names imported by an explicit `use` keep them) | instance unknown on those routes. Bare-parameter field (`v: T`): operator refused, a plain move lowers. **Container field (`items: [T]`, `first: T?`): NOT fail-closed** — `b.items[0] + b.items[1]` through a parameter is lowered as an integer add (right for `Bag<i64>`, WRONG for `Bag<text>`); it cannot be refused outright because the integer case compiles and runs correctly today, so it is flagged by E-MONO-040 (warning by default, error on request). The same holds for a field read on a call result: `boxit("t")` is `call ptr` (only the RETURN is typed), `.item` on it is refused. Fixing it is a frontend change that also needs `bind_type_params` to stop comparing module-local ids (it would turn today's "no evidence" into a mismatch for cross-module callers, e.g. `80.driver/cache/gateway/cache_gateway_adapter.spl`) |
| H-EXPL | written type arguments at a call (`f<T>(x)`, `Box<i64>(…)`) | consumed when HIR carries them (`call_type_args`, `generic_constructor_type`); the parser side belongs to the explicit-type-args lane |
| H-IFVAL | `if val v = o` types `v` as `T?` | specialization at `T?` (`keep$opt_str`); same machine word, pipeline-wide convention |
| H-NAMED | same-named types of two modules share a specialization / display name | unchanged |
| H-XMOD | a nominal type spelled by a template of another module (return type, mixed field type) | 40.mono answers nothing (fail closed) |
| H-RET32 | `fn wrap<T>(x: T) -> Acc` / `-> W<T>` from **another module**: caller `call i64` against `define ptr` | wrong where `ptr` ≠ `i64` (32-bit targets). Fixed for a specialization placed in the caller's own module (F-RET-NOM); the cross-module case still falls back to the name-keyed return-shape registry |
| H-LAMBDA-LET | `collect_lets_expr` does not descend into Call / MethodCall / Binary / Return / StructLit / ArrayLit, so a let inside a lambda passed as an argument is never collected | its uses are refused (E-MONO-032) |
| H-BUILTIN | result type of a builtin method, `match` as a value, untyped lambda parameter | refused (E-MONO-032) |
| H-VISIT | `generated/hir_visitor.spl:walk_hir_comp_clause` never calls `walk_hir_comp_clause_kind`; `post_mono_verify.spl` lacks TryCatch; `hir_subst/body_subst.spl` lacks TryCatch and TypeTest | generated/other-lane files, not touched |
| H-PARSE | `\s: text: …` (typed lambda parameter, documented syntax) is a parse error in the pure parser | not a generics defect; recorded only |

## 9. The parser rule for imported generic annotations (class-params commit in this branch)

An annotation `Foo<i64>` whose base is imported by an explicit `use` item is now
`Named(Foo, [i64])` instead of `Any` (about 1,119 lines in `src/lib`, 66 in `src/app`, 0 in
`src/compiler`). Observable change: such a value has a class identity and type arguments, so
40.mono can specialize methods on it and 50.mir can resolve them; before, it was an erased
word. Because the old `Any` never resolved the base or its arguments, keeping the instance
could have raised `unresolved type` for files that compile today; `lower_named_instance_kind`
therefore withdraws every diagnostic such an annotation raises and leaves it `Any`.

Measured on 10 `src/lib` consumer/provider pairs through HIR + 40.mono (harness with only
those two modules loaded, so most have pre-existing unresolved imports): consumer HIR error
counts are identical to release for all 10 (0, 0, 3, 6, 7, 19, 19, 42, 61, 170); mono errors
0 on both; the two pairs that are clean on release stay clean. Without the withdrawal the same
run had up to 28 extra errors per consumer (`unresolved type: IoError` and the like, all
arguments or bases the erased annotation never looked at). Provider-side counts are higher
than release in 5 pairs (same error kinds reported more often, in modules that already fail
in this harness) — not investigated further.

Cache: the flat-pool label is `spl-flatpool-v6`. Development builds of this lane wrote the
instance-registry layout under the v4 and the v5 label; purge dev caches from that lineage.

## H-ANNOT repair candidate, 2026-10-11 — verification pending

The implementation candidate retains `Name<args>` for registered local names
and forward references, using the existing named-instance flat-pool layout.
The `List<T>` array alias and explicitly imported class precedence remain in the
parser. HIR preserves diagnostics for locally resolved declarations; unresolved
import surfaces retain their existing recovery rule.

Preserving those arguments exposes module-local symbol ids to inference.
`NominalBindingContext` carries the template and caller symbol tables and owner
names. Recursive matching resolves each nominal base through its own table and
compares the declaration's module and name before matching its arguments. It
does not equate nominal bases merely because their raw ids or display names
agree. Existing context-free model tests retain their single-table API.

Acceptance is specified in
`doc/02_requirements/feature/generic_annotation_preservation.md`. The field-path
specs now require concatenation for annotated text instances, integer addition
for annotated integer instances, and refusal only for a genuinely argumentless
receiver. This supersedes the intended H-ANNOT behavior in section 8, but **does
not yet supersede its verified status**: the candidate has not run on an admitted
self-hosted test runtime or rebuilt native compiler. No formal proof of this
parser-to-native path is claimed.

## H-NAMED key repair candidate, 2026-10-11 — verification pending

Specialization identity now includes each nominal type's canonical declaration
module and original name, with length-delimited boundaries. Display mangling is
unchanged; different identities that display alike still receive `_k<n>`.
Unknown ownership propagates failure through nested types and produces
E-MONO-041 instead of registering a specialization by raw symbol id or short
name. Context-bearing inference validates fixed nominal parameters too.

Requirements and execution limits are recorded in
`doc/02_requirements/feature/generic_nominal_identity.md` and
`doc/09_report/generic_nominal_identity_candidate_2026-10-11.md`.
These source changes are not yet an executed acceptance of H-NAMED. They also
do not relocate caller/provider nominal ids across specialization bodies or
return signatures; H-XMOD/H-RET32 remain separate obligations.

## 10. Reduced Lean substitution proof boundary (2026-10-11)

The separate `src/verification/type_inference_compile` Lake project now includes
the manual `GenericsConstraints` library in its default build. Previously that
file was outside the build roots and duplicated the generated model's
`apply_single_subst_var` declaration, so building `Generics` alone did not check
the manual constraints.

The manual file states closed-type substitution invariance, substitution
idempotence when every replacement is closed, preservation of a unary nominal
constructor, and separation of distinct nominal constructor names. A concrete
counterexample rejects unconditional idempotence when replacement types still
contain variables. These statements quantify over the reduced `Generics.Ty`
model; they do not prove the `MType` model above, the parser, HIR owner resolution,
MIR, code generation, or any bootstrap binary. `Ty` has no unknown-type sentinel
and supports only zero-, one-, and two-argument nominal constructors. A canonical
module-qualified owner name is an input requirement, not something the proof
establishes. H-ANNOT, H-NAMED and H-RET32 still need implementation evidence.

Verification entry point: `lake build` in that project using its pinned
`leanprover/lean4:v4.30.0` toolchain, followed by the repository proof-integrity
gate. Proof outputs report kernel axiom dependencies. No model result grants
native, cross-target, release or whole-compiler verification authority.

## 11. Structural MType substitution proofs (2026-10-11)

`src/verification/type_inference_compile/src/GenericSubstModel.lean` is a manual
default Lake target. Its `MType.var`, `con` and `app String (List MType)` match
the Simple model's constructors. Applications have arbitrary finite arity;
`unknown = con "?"` is not closed, including inside another application.
Unlike the smaller `Generics.Ty` proof, this model includes both features.

`Subst = String -> Option MType` abstracts dictionary lookup. It admits infinite
domains, so the theorems apply to finite dictionaries as a special case, provided
their lookup and update semantics are shown to correspond. `apply` performs one
replacement at a variable and recursively maps application children;
`compose outer inner` rewrites each inner binding with outer, using outer only
where inner is absent. Replacement values are not recursively normalized.

| Law | Proved statement and precondition |
|---|---|
| Empty substitution | Identity for every finite MType term |
| Closed invariance | A type with neither variables nor unknown is unchanged |
| S2 composition | Applying composed maps equals inner then outer, with no closed-range assumption |
| S1 idempotence | Requires every value returned by lookup to be closed |
| S3 result closedness | Requires closed range, every input variable bound, and no unknown input constant |
| Unknown behavior | Unknown remains unknown under every substitution and is never closed |
| Constructor preservation | Application name and child-list arity are preserved |

The checked counterexample `T -> U, U -> i64` refutes unconditional idempotence.
The checked nested-unknown example prevents conflating absence of variables with
concreteness. Constructor spelling, builtin arity validity and qualified nominal
ownership are inputs; substitution does not validate them.

### Remaining refinement obligations

| Boundary | Required evidence; current status |
|---|---|
| Simple Dict/array to Lean lookup/list | Lookup, missing-key, overwrite, iteration and order correspondence; **not proved** |
| `ms_apply`, `ms_compose`, `mt_is_closed` to Lean functions | Executable semantic translation/refinement; **not proved** (structural correspondence and finite differential checks only) |
| `substitute_type` TypeParam and bare Named parameter | Relate name and `by_symbol` lookup without owner aliasing; **not proved** |
| HIR constructors to MType applications | Preserve children and distinguish Error/Any/Infer from concrete atoms; **not proved** |
| HIR metadata | Spans, array sizes, function effects, tensor dimensions/device and symbol authority need an explicit relation; **not represented here** |
| Matching, expression inference and specialization keys | Not substitution theorems; existing finite tests and independent repair lanes remain required |
| Native binaries and bootstrap | Exact compiler/runtime admission and execution evidence remain required; **no authority supplied by these proofs** |

Unrestricted display rendering is not injective: closed `Con("Box<i64>")`
and `App("Box", [Con("i64")])` both render `Box<i64>`. Likewise raw owner/name
delimiters can collide. K2 therefore needs a separately verified structural key
encoding, not an assumption that display text is an identity. This counterexample
is outside the bounded identifier universe in section 7; it does not contradict
the reported finite pair counts. No key-injectivity theorem is claimed here.

Validation: pinned Lean 4.30.0 `lake build` checked all 13 jobs, including this
default target. Each theorem prints its kernel dependencies. Dependencies include
Lean's standard `propext` and `Quot.sound`; the open-range counterexample also uses
`Classical.choice`. There are no added axioms, admitted proofs or native-evaluation
proof shortcuts. These model results do not close the refinement obligations.

Executed on Windows on 2026-10-11: the pinned Lean 4.30.0 default build
completed all 11 jobs, including `GenericsConstraints`. The repository guard's
comment-stripping trust scan examined all seven project source files and found
zero bypasses. An independent project copy with `example : False := by decide`
appended to the manual file failed the default build at `GenericsConstraints`.
The empty-substitution, closed-type and idempotence proofs use Lean's `propext`;
the distinct-owner proof reports no axioms. This is reduced-model evidence only.

## H-ANNOT repair candidate, 2026-10-11 — verification pending

The implementation candidate retains `Name<args>` for registered local names
and forward references, using the existing named-instance flat-pool layout.
The `List<T>` array alias and explicitly imported class precedence remain in the
parser. HIR preserves diagnostics for locally resolved declarations; unresolved
import surfaces retain their existing recovery rule.

Preserving those arguments exposes module-local symbol ids to inference.
`NominalBindingContext` carries the template and caller symbol tables and owner
names. Recursive matching resolves each nominal base through its own table and
compares the declaration's module and name before matching its arguments. It
does not equate nominal bases merely because their raw ids or display names
agree. Existing context-free model tests retain their single-table API.

Acceptance is specified in
`doc/02_requirements/feature/generic_annotation_preservation.md`. The field-path
specs now require concatenation for annotated text instances, integer addition
for annotated integer instances, and refusal only for a genuinely argumentless
receiver. This supersedes the intended H-ANNOT behavior in section 8, but **does
not yet supersede its verified status**: the candidate has not run on an admitted
self-hosted test runtime or rebuilt native compiler. No formal proof of this
parser-to-native path is claimed.

## H-NAMED key repair candidate, 2026-10-11 — verification pending

Specialization identity now includes each nominal type's canonical declaration
module and original name, with length-delimited boundaries. Display mangling is
unchanged; different identities that display alike still receive `_k<n>`.
Unknown ownership propagates failure through nested types and produces
E-MONO-041 instead of registering a specialization by raw symbol id or short
name. Context-bearing inference validates fixed nominal parameters too.

Requirements and execution limits are recorded in
`doc/02_requirements/feature/generic_nominal_identity.md` and
`doc/09_report/generic_nominal_identity_candidate_2026-10-11.md`.
These source changes are not yet an executed acceptance of H-NAMED. They also
do not relocate caller/provider nominal ids across specialization bodies or
return signatures; H-XMOD/H-RET32 remain separate obligations.
