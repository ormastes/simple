# No `any` in Safe Code: Inference, Implicit Generics, Thin SFFI

**Status:** owner-approved design, 2026-11-27. **Not implemented** except where
§2 says so. Rollout is warn first, then error (§12).
**Plan:** `doc/03_plan/language/type_system/no_any_inference_plan.md`.
**Numbers:** counts and timings come from the 2026-11-27 usage census, a
read-only analysis that is not checked in. They carry the census's own labels
and were not re-run for this document: **[exact]** one stated regex over the
tree, **[est]** scaled from a sample, **[read]** found by reading code,
**[measured]** run on the census host. Anything without a label is a statement
about what a named file contains.

## 1. Decision

`any` (the erased, runtime-tagged type; `Any` is the same type, and `[any]`
arrays and `any`-valued dicts are included) is allowed **only** in

- `unsafe` code, and
- script mode.

Safe compiled code never **uses** and never **produces** `any`. Where the
compiler cannot determine a type, the result is a **compile-time error**, never
a silent fallback to `any`.

Four elements replace what `any` is used for today:

| # | Element | Replaces `any` used for | Exists today |
|---|---------|-------------------------|--------------|
| 1 | Annotations + HM-style inference + implicit generics | "I did not write a type" | Partly (§2) |
| 2 | SFFI: thin monomorphic C-ABI layer + safe generic Simple wrapper | values crossing the runtime boundary | Raw layer yes; registry and typed wrapper no |
| 3 | Typed sum types (`enum`: `SdnValue`, `JsonValue`) | **closed** heterogeneous data | Yes |
| 4 | Trait objects (`dyn Trait` / `interface`) | **open** heterogeneous data | Yes |

Choosing between 3 and 4: if the set of cases is known where the type is
defined, use an `enum`; if other modules must be able to add cases, use a trait
object.

The census found **no case that needs `any` in safe compiled code**. Every
category maps to a generic, a sum type, a trait object, a typed handle, or a
compile error. What stays dynamic belongs inside `unsafe`: decoding a raw word
whose static type is unknown (heap walkers, `dbg`, `type_of`, `deep_equal` on
erased values, name-based dispatch) and variadic call shims. That is a few
dozen declarations, each of which becomes a generic signature with an `unsafe`
body.

## 2. Current state

### 2.1 Size of the problem

| What | Count | Label |
|------|-------|-------|
| Explicit `any`/`Any` type uses in `src/**/*.spl` | 1,088 lines in 306 files (about 3% false positives) | exact |
| of which in the seed std (`src/compiler_rust/lib/std`, a live seed resolution root) | 401 | exact |
| of which in `src/compiler` | 25 | exact |
| of which inside an `unsafe:`/`danger:` block or `@unsafe` body | 0 (17 are on `@unsafe` signatures) | est |
| Explicit `any` in `test/`, `examples/` | 618, 12 | exact |
| `fn`/`me` declarations in `src` | 190,622 | est |
| with at least one unannotated parameter | 1,376 to 1,390 (0.7%); 1,234 in `src/lib`, 12 in `src/compiler` | est |
| Untyped `var x = []` | 1,963 (27,378 typed) | exact |
| Untyped `= nil` bindings | 58 | exact |
| `\x:` lambdas | about 645 | est |
| `extern fn` declarations | 8,372 (4,377 distinct names) | exact |
| with `any` | 131 (105 in the seed std) | exact |
| generic `extern fn name<T>` (a type variable on the ABI) | 133 | exact |
| Seed sites that manufacture `TypeId::ANY` / `HirType::Any` | 493 in about 45 files | exact |

So essentially all 1,088 explicit uses violate the rule today, and the
implicit surface is small and concentrated: 99.3% of functions are fully
annotated. The unannotated 0.7% is mostly library code copied across the
`gc_async_mut` / `nogc_async_mut` / `nogc_sync_mut` mirrors, so unique work is
roughly a third of the raw count.

By category of explicit use [est, 98-line stratified sample]: JSON/YAML/SDN
values 47%; `any` standing in for a generic 16%; spec helpers 13%; FFI 11%;
callbacks 5%; handles 2%; mixed containers 2%; reflection 1 to 2%.

### 2.2 What already exists

- **Generics are erased, in both compilers.** `src/compiler/40.mono` was
  deleted (commit `200a05f5bc8`); the owner decision of 2026-10-31 is one
  erased body per generic function, with `T` a tagged word boxed and decoded at
  boundaries. The seed resolves a single uppercase letter type name straight to
  `ANY` (`compiler/src/hir/lower/type_resolver.rs`). **There is no
  monomorphizer anywhere.** §6 is about what that means for this design.
- **Self-hosted diagnostics.** `E-ANY-COMPILE-001` / `W-ANY-COMPILE-001`
  (written `Any`, `20.hir/hir_lowering/types.spl`), `E-MC-ANY-001/002` (the
  typed-HIR escape checker in `35.semantics/any_escape/`), `E-MIR-TYPE-Any`,
  and the warn-first families `W-ANY-DECL-001`, `W-HIR-INFER-001/002/003`,
  `W-ANY-USE-001/002` (`doc/07_guide/compiler/robustness/any-warn-rules.md`,
  switched by `SIMPLE_ANY_RULES`). A `type_erasure` unsafe capability exists.
- **A wired HM engine in the self-hosted compiler.** `30.types/type_infer/`:
  `unify` with occurs check, level-based fresh variables, `generalize`,
  `instantiate`, a trait solver, bidirectional `subsume`; run from
  `80.driver/hir_typecheck_consumer_v1.spl`.
- **The seed's type crate** (`src/compiler_rust/type/src/`) has type variables,
  schemes, substitution, `unify` with occurs check, `generalize` and
  `instantiate`.
- **Ratchets.** `scripts/check/check-any-inventory-ratchet.shs`,
  `check-any-warn-rules-ratchet.shs`, `check-any-escape-census.shs` and their
  baselines.
- **Sum types for dynamic data.** `JsonValue` (`lib/common/json/value.spl`),
  `SdnValue` (`lib/common/sdn/value.spl`), `RuntimeValue`
  (`lib/nogc_sync_mut/runtime_value.spl`).
- **Packed array storage, partly.** Both runtimes have byte-packed and
  u64-packed array flags honoured by the accessors.

### 2.3 Gaps that make the rule not hold today [read]

1. **The ban is profile-gated.** It applies only at Robust/Critical strictness
   and only when the mode is not Interpret
   (`80.driver/driver_hir_pipeline_lowering.spl`). Default builds get warnings
   at most.
2. **HM produces diagnostics only.** Inferred types are not written back to HIR
   beyond a finite i64/bool/unit profile (`typed_module_owner_v1.spl`); code
   generation still sees `Any` as an i64.
3. **No fresh variable per unannotated parameter.** `infer_function` binds
   them with `bind_mono(param.type_)` (`type_infer/inference_control.spl`), so
   every unannotated parameter shares the sentinel `Infer(0,0)`, and id 0 is
   also the first real fresh variable (`type_infer/context.spl`). This is the
   concrete first bug to fix.
4. **Two inference engines** in the self-hosted compiler
   (`30.types/type_infer` and `20.hir/inference/types.spl`). Writing types back
   needs one; `30.types/type_infer` is the wired one.
5. **The unsafe carve-out is the `type_erasure` capability, and nothing grants
   it.** The driver passes an empty grant list
   (`80.driver/hir_semantic_consumer_v1.spl`); `type_erasure` is used 0 times
   in `src/lib`, `src/os` and the seed std (4 in `src/app`), against 5,227
   `@unsafe` and 3,954 `unsafe(capabilities: [...])` uses [exact]. See Q5.
6. **No script-mode flag exists** in either compiler, only proxies (§3.2).
7. **The seed has no equivalent.** No any/untyped diagnostic; the production
   pipeline always lowers leniently; the type check result is discarded and its
   errors are downgraded to a warning (`pipeline/lowering.rs`);
   `generalize`/`instantiate` have no callers; strict-mode errors
   (`MissingParameterType`, `CannotInferType`, `EmptyArrayNeedsType`) exist but
   are unreachable in production.
8. **The seed mis-types silently, which is worse than `any`:** an unannotated
   named lambda parameter is `I64`; `[]` is `[I32]`; a value `if`/`match` takes
   the then-arm type and ignores a mismatch; numeric builtins with `ANY`
   arguments are typed `i64`.
9. **Privacy may not be enforced.** Of 553 unannotated functions that are not
   exported, 386 have zero same-file call sites [est]. They are either dead or
   used from other files without an `export`. §5.2 depends on which.

### 2.4 In flight, seed only, uncommitted at the time of writing

- Lane `d29-e` (`work/seed-join-disagreeing-siblings-20261127`): typed join of
  value-position `if`/`match` arms in `hir/lower/expr/control.rs`
  (`join_value_arms`, `join_class`, `join_types_disagree`). Int and float arms
  join by the existing int-to-float widening; any other disagreement between
  judged types is a compile error in safe code. It judges `bool`, integers,
  floats, `text`, arrays and dicts, and deliberately does **not** judge `ANY`,
  struct, enum, `Option`, tuple, or a suffix-guessed method result.
- Lane `d29-c` (`work/seed-join-any-option-disagree-20261127`): stage 1 of
  implicit generics (`hir/lower/implicit_generic.rs`). An unannotated parameter
  is a fresh type variable, not `any`. Stage 1 infers only the identity shape
  (`fn f(x): x`), instantiating at each call site by retyping the result over
  the single erased body. Adds `LowerError::UninferredType` and the
  `__script_entry` attribute (`pipeline/script_detection.rs`,
  `SCRIPT_ENTRY_ATTR`) on the `main` synthesized from a script's top-level
  statements.

## 3. Where `any` is allowed

### 3.1 `unsafe`

`any` may be named, created, stored and passed inside `unsafe` code. A value
may leave an `unsafe` region into safe code only through a **checked decode**:
an operation that inspects the runtime tag and either yields a typed value or
fails (`Option<T>` / `Result<T, E>`). The decode itself is written in `unsafe`.
This is the only place tag checks occur (§7.4).

Whether "unsafe" here means any `unsafe:` block and `@unsafe` function, or only
code granted the `type_erasure` capability, is open (Q5). The decision text
says `unsafe`; the existing escape checker implements the narrower capability;
the warn-rules guide already exempts any `unsafe:`/`danger:` block. In the seed
an `@unsafe` function does not set the unsafe depth today
(`FunctionDef::has_unsafe()` has no callers), so only blocks are visible there.

### 3.2 Script mode

Script mode is a property of the **source unit**, not of how it is executed. A
script is a `.shs` file, or an `.spl` file with top-level statements and no
`fn main`. In such a unit `any` is allowed and unannotated code behaves as it
does today.

The exemption is **per compilation unit**. A library module imported by a
script is still safe compiled code and is checked as such. When a script passes
an `any` value to a typed parameter of a safe function, the conversion happens
on the script side with a runtime tag check and a runtime error on mismatch.

No flag carries this today. Three proxies exist and they do not agree:

| Proxy | Where | Problem as the definition |
|-------|-------|---------------------------|
| Structural: file has top-level statements | seed `pipeline/script_detection.rs` (`has_script_statements`), `is_script_statement` in `pipeline/native_project/compiler.rs`, lane d29-c's `SCRIPT_ENTRY_ATTR` | closest to the definition; not yet a field on the module |
| Execution mode | self-hosted `CompileMode.Interpret` | library code would escape the rule whenever it is run interpreted, which is every `bin/simple test` |
| Path | self-hosted `10.frontend/core/parser.spl`, `parser_path_is_script` (`examples/`, `scripts/`, `test/`, `fixtures/`, `repro/`) | written for the `LOG001` print lint; would exempt every acceptance spec from the rule being tested |

The design adds an explicit source kind (`Module` or `Script`) to the parsed
module, set from the file, with the same predicate in both compilers.

Consequence for tests: a spec file is itself a script unit, so a negative test
("this must be a compile error") cannot be written as top-level code in a spec.
It has to compile a fixture as a non-script module and assert the diagnostic.

## 4. Element 1: annotations and inference

### 4.1 What is always annotated

- `pub` functions and methods, and anything exported from the module (including
  through an `export` list): parameters and non-unit return type.
- Methods, including abstract trait methods; an `impl` takes its types from the
  trait.
- Struct, class and enum payload fields.
- Explicit generic parameters and their bounds.
- `extern fn` declarations.

### 4.2 What is inferred

- Body locals (`val` / `var`), as today.
- Lambda parameters, from the expected function type, else a fresh variable.
  (This removes the seed's `I64` default.)
- Return types, from the body.
- Private functions, by the tiers in §5.

### 4.3 What inference never does

- It never answers `any`. A type variable still unresolved when the module is
  finished is an error at the site that needed the type.
- It never crosses a module boundary. Everything a module's inference needs
  from another module is in that module's annotated signatures.
- It never generalizes anything but a `fn` declaration. `var` bindings and
  lambdas stay monomorphic (value restriction).

Numeric literal defaulting (`42` is `i64`, `3.14` is `f64`) is a determination,
not a fallback, and stays. `var xs = []` gets a fresh element variable solved
by the first push or assignment; unresolved at the end of the function is an
error. `var found = nil` gets `T?` with `T` solved by later assignment. An
argless generic type (`Dict`, `Option`) gets fresh variables solved by use.

Unresolved names, types and imports that the lenient seed currently turns into
`ANY` are **not** an inference problem. They become plain compile errors, last
and warn-first, because they hide real breakage (§10.3).

## 5. Inference tiers (per function)

| Tier | Function | Rule | Functions today [est] | Code generated |
|------|----------|------|-----------------------|----------------|
| T0 | fully annotated | locals inferred | about 189,200 (99.3%) | as today |
| T1 | `pub` / exported, unannotated | must annotate; the error carries the inferred signature | about 600 (93 `pub` + about 503 via `export` lists) | one typed copy |
| T1m | unannotated method | must annotate | 230 | one typed copy |
| T2 | private, same-module call sites **agree** | inferred | about 470 to 500 of 553 | **one** monomorphic copy; cheaper than today (no boxing) |
| T3 | private, call sites **disagree** | implicit generic, instances capped and deduplicated | fewer than 30 | see §6 |
| T4 | over the cap, unsupported recursion, or a body that dispatches on runtime tags | **compile error**: annotate, or use an enum | about 170 raw, about 60 unique | none |
| T5 | `unsafe` / script | `any` allowed | 0 uses inside unsafe today | as today |

Counts are from a line-regex census of 1,376 functions with an unannotated
parameter; the T2/T3/T4 split comes from samples of 15 and 40 and is the
softest number in this document.

### 5.1 Order of work inside a module

1. Collect annotated signatures.
2. Build the call graph of unannotated private functions; take strongly
   connected components in dependency order. Only the unannotated functions
   are nodes.
3. For each component: give every unannotated parameter and return its own
   fresh type variable, generate constraints from the bodies, then from every
   same-module call site and every use of the function as a value.
4. Solve. Generalize at component exit. Classify each function as T2, T3 or T4.
5. Write the solved types back to HIR, so code generation sees types and not
   `Any`.

Within one component the functions are monomorphic with respect to each other
(standard HM), which is what makes polymorphic recursion detectable. The census
found no mutual-recursion cycle among unannotated functions today.

### 5.2 T2: agreement, and the privacy precondition

If the body constraints and all same-module call sites resolve every type
variable to one closed type, the function gets that signature and exactly one
copy of code.

"Private means module-local" has to be **true** for this, and gap 9 in §2.3
says it may not be. Before T2 is relied on, either file privacy is enforced (a
use of a non-exported function from another file is an error), or the scope of
call-site collection is widened to the package, or a private function with no
same-file call sites is treated as T1. A private function with no call sites
at all whose body does not determine its types has nothing to infer from (Q3).

### 5.3 T3: implicit generic

If type variables remain after the body is solved and call sites supply
different closed types, the function is generalized over the remaining
variables and instantiated per distinct call-site type vector. The inferred
variables become ordinary type parameters and take the same path as an
explicit `<T>`. One known real case today: `_join` in
`lib/common/serialization/__init__.spl`, reached with `[i64]` and `[bool]`.

Uses of an inferred `T` inside a T3 body:

| Use | Rule |
|-----|------|
| passed along, stored, returned | fine |
| method call `x.len()` | a **method-presence constraint** checked at each instantiation; if exactly one trait declares the method, infer `T: Trait`; otherwise error "annotate" (S5) |
| tuple index `z.0` | infer a tuple of the arity fixed by use |
| named field `p.name` | T2 only; in T3 an error. No row polymorphism. The seed's receiver-blind field search is the unsound shortcut this replaces |
| arithmetic / comparison | requires a numeric bound, else error. Arithmetic on an erased `T` is a known wrong-code class |

### 5.4 Instance cap and deduplication

- **Dedup key.** Two instantiations that agree on the canonical closed type
  vector are one instance.
- **Cap.** A fixed maximum number of distinct instances per function. Proposed
  default **4** (Q2). With fewer than 30 T3 functions today, that bounds the
  worst case at about 120 specialized bodies, under 0.1% of all functions.
  The cap is a compiler constant with the same value in both compilers, not a
  user flag: a flag would make one source compile on one machine and not
  another.
- **Over the cap** is T4, never a silent switch to something else.

Under the current erased model an instance is a type-level fact and costs no
extra body, so the cap and dedup matter for code size only if §6 is answered
with specialization. They are specified now so that answer does not change the
language rule.

### 5.5 T4: what is refused

- More distinct instances than the cap.
- Polymorphic recursion: a function used at a different instantiation inside
  its own component.
- Higher-rank use: an unannotated parameter that must itself be polymorphic.
- A function value whose type is not fixed where it is taken.
- A body that is genuinely dynamic (dispatches on the runtime tag of a mixed
  array, `type_of`): rewrite to an enum or a record.

### 5.6 Disagreeing arms

A value-position `if`/`match` whose arms have different types is an error that
names **both** arm types and **both** locations. These are joins, not
disagreements:

- an arm that does not produce a value (`return`, `break`, panic);
- int and float arms, joined by the existing int-to-float widening;
- a weak empty literal (`[]`, `{}`) against the same collection kind;
- arms whose types are variants of a declared union, joined to that type;
- a value arm and a `None` arm, joined to `Option<T>` (Q4: lane d29-e leaves
  `Option` unjudged today).

The census found no text-versus-int disagreement in existing source by grep,
so this rule is expected to break little and to stop silent wrong values where
it fires.

## 6. Instances versus the erased-generics decision

This is where this design and an earlier owner decision pull in different
directions. It is **left open for the owner** (Q1; the census calls it D1).

- 2026-10-31: generics are erased; one body per generic; no monomorphizer.
- 2026-11-27: safe code never uses or produces `any`; a T3 function has
  instances with a cap; `FfiCodec<T>` is monomorphized and inlined; collections
  store typed unboxed elements.

The census separates two goals that the decision text treats as one:

| Goal | Needs specialization? | Status |
|------|-----------------------|--------|
| Remove `any` **the type** from safe code: every use statically checked, no silent garbage | **No.** HM with implicit generics works over the erased representation. An inferred `T` has the runtime shape `any` has today but is checked at every use and call site | feasible now; stages S1 to S5 |
| **Zero cost**: inlined codec, unboxed `Array<f64>`, no per-element tag | **Yes.** Without specialization a user-level codec trait is dictionary or dynamic dispatch per call | needs an owner decision that partly reverses 2026-10-31 |

Ways to answer Q1:

| Option | Instances are | Body copies | Run-time cost |
|--------|---------------|-------------|---------------|
| A. Typed signature over one erased body | type-level only; the call site retypes and decodes | 1 | today's boxing |
| B. Selective specialization by representation class | one body per class (word integer, float, reference) for chosen hot functions | small, fixed | removed for those functions |
| C. Full monomorphization | one body per closed type vector, up to the cap | up to the cap | removed |

Lane d29-c's stage 1 is option A. Under A, "never produces `any`" is a
statement about the **type system**: no expression in safe code has type
`any`. The erased body's tagged word is an implementation detail of generated
code, the way a vtable is for `dyn Trait`.

**Design position until Q1 is answered:** the classifier in §5 is the same for
A, B and C; ship A; specify the SFFI layer (§7) so its user-visible API does
not change if B arrives later. S1 to S5 do not depend on Q1. The unboxed half
of S6 does.

## 7. Element 2: SFFI

### 7.1 Layering

```
safe Simple        Handle<T>, typed generic wrappers             generic, safe
-----------        codec: encode/decode at statically known T    static, inlined
unsafe Simple      extern fn rt_*(...)  + checked decode         monomorphic, unsafe
===========  C ABI ============================================  no generics here
Rust runtime | C runtime     twinned implementations of rt_*
```

**Generics never cross the ABI.** Every `rt_*` symbol has one fixed C
signature. Adding a type adds a codec, never an extern.

### 7.2 Where the raw layer stands [census]

- 96.5% of `extern fn` declarations (about 8,080) are already concretely typed
  and fit the thin ABI as they are [est].
- 131 take or return `any`: handles typed as `any` 53, constructors returning
  `any` about 69, callbacks 4, buffers 4, collections 1 [exact]. 105 are in the
  seed std; most of the rest are `unsafe_addr_of(ref: any)` repeated in about
  25 `src/os` files.
- 133 are generic externs (`rt_transient_heap_promote` 28,
  `rt_enum_discriminant` 23, `rt_array_free<T>` 7, ...). Under erasure they
  work, but they put a type variable on the ABI, which this design forbids.
- 23 are typed with the dynamic word (`Value` / `RuntimeValue`); the value
  boxing externs already use `RuntimeValuePtr`, not `any`.
- **Twinning is partial.** Of 2,594 distinct `rt_*` symbols, 609 exist in both
  runtimes, 932 are C-only and 1,053 Rust-only (frozen by
  `check-rt-dual-implementation-ratchet.shs`). "Twinned as today" therefore
  means: no new single-lane symbol. A design that added an extern per type
  would add single-lane debt and be blocked by the ratchet.

### 7.3 One declaration, four outputs

Each raw function is declared once as a row in the SFFI v2 registry, from
which a generator emits

1. the Simple `extern fn` declaration, in an `unsafe` raw module;
2. the Rust `extern "C"` signature;
3. the C prototype;
4. a parity check that the three agree and both runtimes define the symbol.

**This registry does not exist yet** [read]. Today
`check-sffi-v2-authority.shs` aggregates per-module authority guards; the v2
contract types are design-only (`doc/05_design/platform/sffi_v2_hardening.md`);
`rt_alias_map.sdn` is a migration map; `sffi_gen` reads `@Lib` specs and emits
Rust wrappers only; and the seed interpreter has a third, hand-written
dispatch table (`compiler/src/interpreter_extern/mod.rs`) that the parity
check must also cover. Building the registry starts with the hot symbols, not
all 4,377 names.

ABI types allowed in a row: fixed-width integers, `f32`/`f64`, `bool`, the
handle word, the runtime value word (`RuntimeValuePtr`, for rows classed
`tagged`), pointer+length pairs for borrowed text and buffers, out-pointers.
No `any`, no type parameter.

### 7.4 `Handle<T>`

A phantom newtype over the 64-bit handle word. `T` names what the handle refers
to and exists only in the type checker; it is erased at codegen, so a
`Handle<T>` is one machine word with no tag and no check. It stops a socket
being passed where a database is expected without costing an instruction.

Open implementation point [read]: existing handles are `class`/`struct`
wrappers around `value: i64` (81 declarations), and the generic ones such as
`HostTaskHandle<T>` are not phantom-typed. A zero-cost form needs a generic
newtype over `i64`; language support for that was **not verified** and is the
first thing S6 has to establish.

### 7.5 Codec (`FfiCodec<T>`)

The decision specifies `FfiCodec<T>`: encode and decode between `T` and its ABI
representation, monomorphized and inlined, identity for scalars and handles,
with tag checks only in the unsafe decode layer.

What the code allows today [read]:

- No such trait exists (0 hits for `FfiCodec`, `ToFfi`, `FromFfi`, `Boxable`),
  and without specialization a user-level trait would be dispatched per call.
- The compiler already **has** this codec internally: `box_runtime_value` /
  `decode_runtime_value` in `50.mir/_MirLoweringExpr/expr_dispatch.spl`
  (83 call sites), inline for integers of 32 bits or fewer and a runtime call
  for `i64`/`u64`.

So the first realization needs no user-visible trait: the wrapper is written
as `fn get<T>(a: Handle<[T]>, i: i64) -> T` and the compiler inserts, at the
call site where `T` is statically known, the decode it already knows how to
emit. That gives the same API and the same safety. `FfiCodec<T>` as a
user-extensible, inlined trait arrives with option B or C of §6.

### 7.6 Typed, unboxed collection storage

Target: `Array<f64>` stores 8-byte floats, `Array<i64>` words, `Array<u8>`
bytes; element access is a typed load; `[any]` is the tagged-element array and
is `unsafe`/script only.

Today [read]: byte-packed and u64-packed arrays exist in both runtimes.
**There is no f64-packed array in either**; floats are heap-boxed per element.
Adding it follows the existing flag pattern in both runtimes and the
interpreter. All collection externs take the tagged word for container and
element, and compiled code boxes every `i64`/`u64` element through a runtime
call.

Hot-path rule: `[T]` indexing, `len`, `push` and text concatenation stay
**compiler intrinsics**. Moving them into Simple library wrappers would add a
call per element unless wrappers inline. Generic Simple wrappers are for the
long tail: handles, tree maps, hash sets, threads, mutexes. Text is not at
risk: it crosses as a concrete `text` with no codec.

## 8. Elements 3 and 4

Both exist; the work is migration (S8) and one inference gap (S5).

- **Closed:** `enum` with typed payloads and exhaustive `match`. The largest
  single migration is here: JSON/YAML/SDN helper APIs that take `any` (about
  510 uses, 47% of all explicit `any`) take `JsonValue` / `SdnValue` instead.
- **Open:** `dyn Trait` / `interface`. A parameter typed with a plain trait
  name is rewritten to a static generic by
  `src/app/desugar/trait_static_dispatch.spl`; `dyn Trait`, `[Trait]` and
  interfaces stay dynamic. Spec matchers with heterogeneous argument lists are
  the main candidate.
- **Gap (S5):** method calls on an inferred `T` (§5.3). Explicit bounds are
  rare in the tree (116 `<T: Trait>`, 220 `where`, most in the seed std), so
  the trait-bound machinery has little real-world exercise. S5 is the risky
  stage.

## 9. Diagnostics

Messages are the contract and must be identical in both compilers. Each is
reported at the **definition**, names the conflicting uses, never shows a raw
type variable, and where the fix is an annotation shows a signature the user
can paste (reusing the suggestion code behind `W-ANY-DECL-001`).

| Situation | Message shape |
|-----------|---------------|
| Arms disagree | `if/match arms have different types: 'text' at <loc1>, 'i64' at <loc2>; make the arms the same type, or use an enum` |
| Type not determined | `cannot infer a type for <origin> used in <usage>; add a type annotation or an explicit generic (fn f<T>(x: T) -> T). any is allowed only inside unsafe and in script mode` (text from lane d29-c) |
| `pub` unannotated | `public function '<name>' must annotate its parameters and return type; inferred: fn <name>(<p>: <T>) -> <R>` |
| Over cap | `'<name>' is called with <n> different type combinations (limit <cap>); annotate it, for example fn <name><T>(x: T) -> T. Call sites: <loc...>` |
| Polymorphic recursion | `'<name>' calls itself at a different type (<A> at <loc1>, <B> at <loc2>); annotate '<name>'` |
| Higher-rank | `parameter '<p>' of '<name>' is used at more than one type; annotate '<name>'` |
| `any` in safe code | `'any' is allowed only inside unsafe and in script mode; use a type annotation, an enum, or a trait object` |
| Unresolved empty literal | `cannot infer the element type of '[]' at <loc>; annotate it, for example val xs: [i64] = []` |
| Missing method / bound | `'<name>' calls '.<m>()' on a parameter whose type at <call loc> is '<A>', which has no '<m>'; annotate the parameter or add a bound <T: Trait>` |
| Field on generic | `'<name>' reads field '<f>' of a parameter used at more than one type; annotate the parameter` |

During the warn phase the same text is emitted as a warning with the suffix
`(this will become an error)`.

Existing codes are reused where the situation is the one they already name:
`E-ANY-COMPILE-001` and `W-ANY-DECL-001` for a written `any`,
`W-HIR-INFER-001/002/003` for a type inference could not determine,
`W-ANY-USE-001/002` for uses of an `any` value, and the seed's existing
`MissingParameterType`, `CannotInferType`, `EmptyArrayNeedsType`. What changes
is scope (all safe compiled code in every profile, not only `src/compiler/**`
or Robust/Critical) and the end state (error). New codes are needed only for
rows with no existing family.

## 10. Risks and mitigations

### 10.1 Run-time performance

| Risk | Mitigation |
|------|------------|
| Call-site decode on T3 calls under option A | T2 is the common case (about 85 to 90% of unannotated functions) and gets concrete types with no boxing, which is cheaper than today; T3 is fewer than 30 functions |
| Collection access gets slower if moved to library wrappers | indexing, `len`, `push`, concat stay compiler intrinsics (§7.6) |
| Code size growth under B or C | instance cap; dedup; worst case about 120 bodies today |
| Zero-cost claims not met under A | stated, not hidden: A removes `any` the type, not boxing. Unboxed `f64` arrays and an inlined user codec need Q1 |

### 10.2 Build speed

Measured by the census [measured], seed `compile` of generated files of
nine-line functions: 1 function 1.01 s (startup), 500 functions 1.55 s, 2,000
functions 5.18 s. That is 1 to 2 ms per function for parse, lower and codegen
together, so body inference is bounded well below 1 ms per function. A phase
split is **not measurable** today: the seed has no phase profile.

The one real self-hosted data point is a warning: enabling the HIR-backed any
rules costs one extra `check` child process per file, 24 s to 62 s on one
compiler file under the seed interpreter (`any-warn-rules.md`). That is process
and lowering cost, not the unifier.

| Risk | Mitigation |
|------|------------|
| Lowering runs twice | inference lives in the driver's existing typecheck consumer, not in a second child process. This is the main build-speed requirement |
| Whole-program inference | none: inference is module-local because exported signatures are annotated |
| Cache invalidation from inferred signatures | a private function's inferred signature is not part of the module's interface digest, so editing a private body cannot invalidate importers. Checked by a test, not assumed |
| Call-graph pass | only the roughly 1,390 unannotated functions are nodes; SCC ordering is linear in call edges |

### 10.3 Robustness

| Risk | Mitigation |
|------|------------|
| Existing code stops compiling | warn then error; baselines frozen by the existing ratchets; migration by category (S8). About 600 exported functions need an annotation, supplied as a fix-it |
| Bootstrap closure breaks | `src/compiler` has 12 unannotated-parameter functions and 25 `any` uses. Annotate those first; then the seed never has to infer to build the compiler |
| "Private" is not module-local | resolved before T2 is relied on (§5.2) |
| Inference picks a surprising type | T2 requires **all** call sites to agree; no "most common type" heuristic; no defaulting beyond literals |
| Unresolved names turning into `ANY` hide breakage | made errors last, warn first; this is the high-risk rollout item |
| Trait-bound inference is under-exercised | S5 is last among the inference stages and its failure mode is the "annotate" error, not wrong code |
| A negative test passes vacuously | fixtures compiled as non-script modules (§3.2); each has a must-pass twin |
| `unsafe` becomes the escape hatch | grants are counted by ratchet; a migration lane that moves more than a small share of its sites into `unsafe` stops and reports |
| The join fix types a join `ANY` in safe code | lane d29-c section A boxes a scalar arm and types the join `ANY` when the sibling is `ANY`. Correct today; under this design the `ANY` sibling is itself the defect, and the boxing path remains for `unsafe`/script only |

## 11. Seed and self-hosted parity

The rule set is defined once, in this document. How much of it each compiler
implements is a choice with a recommended answer (Q6).

| Piece | Seed | Self-hosted |
|-------|------|-------------|
| Unifier + occurs check | has | has |
| Fresh variable per unannotated parameter | needs (lowering assigns `ANY` before the checker runs) | needs (the `bind_mono` fix) |
| Generalize / instantiate | has, uncalled | has, called |
| Call-site driven inference for private functions | needs | needs |
| Types written back to HIR | needs; the checker returns nothing (large) | partial |
| Trait-bound solving | none | has a solver |
| any/untyped diagnostics | none | has, profile-gated |

**Recommended (census):** do **not** port full inference to the seed. The seed
is bootstrap-only and has to compile `src/compiler` plus the std prefixes it
imports; once those are annotated the seed never needs to infer. The seed gets

- the in-flight lanes (typed arm join; stage-1 identity instantiation);
- fixes for its silent mis-typings (lambda `I64`, `[]` as `[I32]`, then-arm
  join), which are wrong regardless of this design;
- the **syntactic** twins of the checks: written `any` outside unsafe, and an
  unannotated parameter in a non-script module.

The full engine (tiers, write-back, bounds) is built once, in the self-hosted
compiler. The direction of disagreement is then safe: a program the
self-hosted HM accepts is always accepted by the more lenient seed. The reverse
(seed accepts, self-hosted refuses) is expected for unmigrated code and is
what the warn phase reports.

The alternative, full inference in both, doubles the large items (write-back,
call-site inference, bounds) in a compiler that is meant to stay minimal.

Parity that is required either way: same verdict from both compilers on the
shared fixture corpus for every check both implement; same message text and
codes; same cap constant; same script predicate.

## 12. Rollout

Warn first, then error, the same pattern as the other staged rules in
`doc/07_guide/quick_reference/syntax_quick_reference.md` ("Staged warnings").

1. Script source kind and the unsafe rule decided and implemented first; no
   other check is meaningful without them.
2. Diagnostics land as **warnings** in every profile, with baselines frozen so
   new sites fail review and old ones do not.
3. Migration (S8) drives the baselines to zero, bootstrap closure first.
4. A directory flips to **error** when its baseline is empty; the global flip
   follows when `src/` is clean.

Disagreeing arms and uninferable types that would otherwise compute on a
tagged word are errors from the start in the seed lanes: they replace silent
wrong values, not working code.

## 13. Open questions for the owner

- **Q1 (census D1).** Keep one erased body and accept today's boxing cost
  (option A), or allow selective specialization, capped and deduplicated, for
  hot generic code (B or C)? Blocks only the unboxed half of S6 and the
  code-generation half of S3.
- **Q2.** Instance cap value. Proposed 4.
- **Q3.** A private function with no call sites and an undetermined signature:
  error, or unused-code warning?
- **Q4.** `Option` joins: is a value arm with a `None` arm inferred as
  `Option<T>`?
- **Q5 (census D2).** Does plain `unsafe` allow `any`, or only code granted the
  `type_erasure` capability?
- **Q6.** Full inference in the seed, or the bounded seed scope recommended in
  §11? The plan is written for the recommendation.
