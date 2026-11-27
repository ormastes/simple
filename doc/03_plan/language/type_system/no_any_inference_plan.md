# Plan: No `any` in Safe Code (Inference, Implicit Generics, Thin SFFI)

**Design:** `doc/05_design/language/type_system/no_any_inference_generics.md`
(owner-approved 2026-11-27). Section references (§n) and questions (Q1..Q10)
are to that file.
**Status:** S1-A and S2-A are in flight in the seed. Everything else is not
started.
**Numbers** are from the 2026-11-27 usage census and carry its labels
(design, header). They were not re-run for this plan.

## How to read this plan

- A **stage** (S1..S9) is a capability. A **lane** (S1-A, ...) is one PR-sized
  unit one worker can own. Lanes in the same **parallel group** (G0..G6) do
  not depend on each other and can run at the same time.
- **Size** is changed lines including tests: S under 300, M 300 to 1,000,
  L over 1,000. Sizes are estimates from reading code, not measurements.
- **Seed** = `src/compiler_rust`. **Self-hosted** = `src/compiler`.
  **Stdlib** = `src/lib`.
- The plan is written for the **recommended answer to Q6**: the full inference
  engine is built once, in the self-hosted compiler; the seed gets the two
  in-flight lanes, fixes for its silent mis-typings, and syntactic twins of
  the checks. If the owner answers Q6 the other way, S2-C, S2-E, S3-A, S3-B
  and S5-A each gain a seed twin of the same size, and the seed's missing
  write-back of inferred types (large) becomes a prerequisite of all of them.
- Lanes gated on an owner question say so; the questions are collected under
  "Open owner decisions" below.

### Rules for every lane

- Negative fixtures are compiled as **non-script modules** (§3.2). A spec's
  own top-level code is a script unit and proves nothing about safe code.
  Every must-fail fixture has a must-pass twin.
- Acceptance asserts the **location(s)** in a diagnostic, not only its text.
- A lane that changes what a compiler accepts adds the fixture to the shared
  corpus (S1-C) with its expected verdict.
- Inference runs inside the driver's existing typecheck consumer
  (`80.driver/hir_typecheck_consumer_v1.spl`). No lane adds a second lowering
  or a child `check` process (§10.2).
- Seed verification: the lane's test module under
  `src/compiler_rust/compiler/src/hir/lower/tests/` plus
  `sh scripts/check/check-seed-builds-push.shs`. Spec verification:
  `bin/simple test <spec>` with the binary identity recorded
  (`.claude/rules/commands.md`).
- Hot files shared by several lanes: seed `hir/lower/expr/control.rs`,
  `hir/lower/expr/calls.rs`, `hir/lower/module_lowering/function.rs`,
  `hir/lower/error.rs`; self-hosted `30.types/type_infer/inference_control.spl`
  and `inference_expr.spl`. Two lanes in one group that both need new logic
  there put it in their own new file and touch the hot file only to call it.
- The mirrored library trees (`gc_async_mut`, `nogc_async_mut`,
  `nogc_sync_mut`) hold copies of the same code. A migration lane fixes all
  copies of a function in one change.

## Lane table

| Lane | Scope | Group | Size | Depends on |
|------|-------|-------|------|------------|
| S1-A | Seed: disagreeing `if`/`match` arms are a compile error (in flight, lane d29-e) | G0 | M | none |
| S1-B | Seed: extend the judged set to struct, enum, tuple, `Option`; both locations in the message | G1 | M | S1-A; Q4 |
| S1-C | Shared fixture corpus + expected-verdict manifest | G0 | S | none |
| S1-D | Self-hosted: unify value arms, error on mismatch, `Option` join | G1 | M | S1-C, S4-A; Q4 |
| S2-A | Seed: stage-1 implicit generic (identity shape), `UninferredType`, script-entry attribute (in flight, lane d29-c) | G0 | M | none |
| S2-B | Self-hosted: fresh type variable per unannotated parameter (`bind_mono` / `Infer(0,0)` fix) | G0 | S | none |
| S2-C | Self-hosted: one inference engine; write inferred types back to HIR | G1 | L | S2-B |
| S2-D | Privacy precondition: classify the 386 private functions with no same-file call site; enforce file privacy or widen scope | G0 | M | none |
| S2-E | Self-hosted: T2. SCC over unannotated private functions, body + same-module call-site constraints, one monomorphic copy | G2 | L | S2-B, S2-C, S2-D |
| S2-F | Self-hosted: local forms. Empty-literal element variable, `nil` binding as `T?`, lambda parameters from the expected type, argless generic types | G1 | M | S2-B |
| S2-G | Seed: fix silent mis-typings (lambda parameter `I64`, `[]` as `[I32]`, numeric builtins on `ANY`) | G1 | S | S2-A |
| S3-A | Self-hosted: T3. Generalize at SCC exit, instantiate per call-site type vector over the erased body, value restriction, cap + dedup, over-cap error | G3 | M | S2-E |
| S3-B | Self-hosted: refuse polymorphic recursion, higher-rank use, tag-dispatching bodies | G3 | M | S2-E |
| S3-C | Selective specialization of instances (option B or C) | G5 | L | S3-A; **Q1** |
| S4-A | Self-hosted: source kind `Module`/`Script` on the parsed module; stop keying on `CompileMode.Interpret` | G0 | S | none |
| S4-B | Seed: the same source-kind predicate | G1 | S | S2-A |
| S4-C | Unsafe rule per Q5: grant wiring in the self-hosted driver; seed `@unsafe` functions set the unsafe depth | G1 | M | **Q5** |
| S4-D | Self-hosted: `any` diagnostics in every profile as warnings, scope widened from `src/compiler/**` to all safe code | G2 | M | S4-A, S4-C |
| S4-E | Self-hosted: unannotated `pub`/exported function and method diagnostic, with the inferred signature as a fix-it | G3 | M | S2-E |
| S4-F | Seed: syntactic twins (written `any` outside unsafe; unannotated parameter of an **exported** function in a non-script module) | G2 | M | S4-B, S4-C |
| S4-G | Ratchets and baselines, per-directory severity, interface-digest invariance test | G4 | M | S4-D, S4-E, S4-F |
| S5-A | Self-hosted: method-presence and unique-trait bound inference checked at instantiation; numeric bound; tuple index; field-on-generic error | G4 | L | S3-A |
| S5-B | An inferred bound stays static: never silently becomes dynamic dispatch | G5 | S | S5-A |
| S6-A | Zero-cost `Handle<T>` (establish the generic newtype over `i64`); migrate handle externs (53 + about 69 declarations) | G0 | M | none |
| S6-B | Generic externs off the ABI (133): parameter becomes the runtime value word, `<T>` moves to the wrapper; guard against new generic externs | G0 | M | none |
| S6-C | One generic `unsafe_addr_of<T>` (about 25 copies); callback wrappers `<D, R>` (4 `any` + 11 `fn(...)` externs) | G0 | S | none |
| S6-D | Seed std collections: generic `<K, V>` API over the handle externs (92 uses) | G1 | M | S6-A |
| S6-E | SFFI v2 registry + generators (Simple extern, Rust signature, C prototype) + parity check including the seed interpreter table; hot symbols first (about 50) | G1 | L | none |
| S6-F | Compiler-inserted codec at statically known `T` for wrappers; class and ratchet `tagged` rows | G3 | M | S2-C |
| S6-G | `f64`-packed arrays in both runtimes and the interpreter; specialized `[f64]` access; user-level `FfiCodec<T>` | G5 | L | S6-E; **Q1** |
| S7-A | Differential harness: both compilers over the corpus against the manifest | G1 | M | S1-C |
| S7-B | Twin conformance guard: same verdict, text and code for every check both compilers implement; cap constant and script predicate equal | G4 | S | S3-A, S4-F |
| S7-C | Bootstrap-closure proof: seed builds the annotated closure without inferring; self-hosted rules clean on it | G4 | M | S8-A, S4-D, S2-E |
| S8-A | Annotate the bootstrap closure: 12 unannotated-parameter functions and 25 `any` uses in `src/compiler`, plus the std prefixes it imports | G0 | S | none |
| S8-B | JSON/YAML/SDN helper APIs take `JsonValue`/`SdnValue` instead of `any` (about 510 uses) | G1 | M | S9-A |
| S8-C | Explicit `any` to `<T>`: generic stand-ins (about 180) and callbacks / user data (about 55) | G1 | M | none |
| S8-D | Spec helpers (about 145 in `src`, 618 in `test/`): `<T>` for `expect`, a sum type for mixed argument lists (`dyn Matcher` only after S9-B) | G1 | M | none |
| S8-E | Annotation codemod: about 600 exported functions and 230 methods, from the S4-E fix-it | G4 | L | S4-E |
| S8-F | Rewrite genuinely dynamic bodies to enums/records (about 170 raw, about 60 unique) | G4 | M | S3-B |
| S8-G | Seed std remainder (401 explicit uses, less what S6-D and S8-D take) | G2 | M | S6-D, S8-D |
| S8-H | Residual untyped `[]` (1,963 sites), `nil` bindings (58), mixed containers (about 20) that inference does not resolve | G3 | S to M | S2-F |
| S8-I | Unresolved names, types and imports stop becoming `ANY`: warn, then error | G5 | M | S4-G |
| S8-J | Flip to error: per directory as its baseline empties, then global | G6 | S | all |
| S9-A | Fix the enum bugs a sum-type migration hits: payload dict copied on return; `T?` match silent fall-through | G0 | M | none |
| S9-B | Self-hosted: multi-implementor dynamic dispatch for `dyn Trait`; one object layout shared with the seed; object-safety check in the seed | G1 | L | **Q9** |
| S9-C | First `dyn Trait` migration targets (open-set cases left on the baseline by S8) | G5 | M | S9-B |

### Parallel groups

| Group | Lanes that run together | Opens when |
|-------|-------------------------|------------|
| G0 | S1-A, S1-C, S2-A, S2-B, S2-D, S4-A, S6-A, S6-B, S6-C, S8-A, S9-A | now |
| G1 | S1-B, S1-D, S2-C, S2-F, S2-G, S4-B, S4-C, S6-D, S6-E, S7-A, S8-B, S8-C, S8-D, S9-B | their G0 inputs landed; Q4 for S1-B/S1-D, Q5 for S4-C, Q9 for S9-B |
| G2 | S2-E, S4-D, S4-F, S8-G | S2-C, S2-D, S4-A..C landed |
| G3 | S3-A, S3-B, S4-E, S6-F, S8-H | S2-E landed |
| G4 | S4-G, S5-A, S7-B, S7-C, S8-E, S8-F | S3-A, S3-B, S4-D..F landed |
| G5 | S3-C, S5-B, S6-G, S8-I, S9-C | S4-G, S5-A, S9-B landed; Q1 for S3-C and S6-G |
| G6 | S8-J | everything else |

Groups are a lower bound on waiting, not a schedule: a lane may start as soon
as its own "Depends on" cell is satisfied. Three things are worth starting
immediately because nothing blocks them and they shrink everything after:
**S8-A** (after it the seed never has to infer to build the compiler),
**S9-A** (it unblocks S8-B, which is 47% of explicit `any`),
and **S4-A** (no check is meaningful
without a script definition). The critical path is
S2-B, S2-C, S2-E, S3-A, S5-A; S2-C (write-back) is its largest single item.

## Open owner decisions

None of these is settled. Each has a recommended answer that the plan
assumes; a different answer changes the lanes named.

| Decision | Recommended | If answered the other way |
|----------|-------------|---------------------------|
| **Q1** Erased bodies versus selective specialization | keep one erased body for now | S3-C and S6-G open; they are the only source of the zero-cost claims (inlined codec, unboxed `Array<f64>`) |
| **Q5** Does any `unsafe` permit `any`, or only the `type_erasure` capability | owner to choose; the decision text says `unsafe` | changes S4-C and the size of every S8 lane that moves code into `unsafe` |
| **Q7** Script mode by file kind or by execution mode | file kind | S4-A/S4-B shrink to documenting the existing proxy, and library code escapes the rule under `bin/simple test` |
| **Q6** Seed scope: syntactic checks only, or full inference | syntactic only | S2-C, S2-E, S3-A, S3-B, S5-A gain seed twins; seed write-back (L) becomes a prerequisite |
| **Q8** Enforce file privacy (386 of 553 non-exported unannotated functions have no same-file caller) | enforce, after S2-D classifies them | up to 386 functions move from T2 to T1 and S8-E grows |
| **Q9** Trait objects: build multi-implementor dispatch in the self-hosted compiler | owner to choose | without it S9-B and S9-C do not run; open-set `any` sites migrate to enums or stay baselined |
| Q2 cap value, Q3 uncalled private functions, Q4 `Option` joins, Q10 proposals | see design §13 | local to S3-A, S2-E, S1-B/S1-D |

Ask Q5 and Q7 first: S4 cannot start without them and nothing else is
enforceable until S4 exists.

## Recommended order

The census ranks the work by `any` removed per unit of cost. Lanes overlap as
the groups allow; this is the order to staff when workers are scarce.

| # | Work | Lanes |
|---|------|-------|
| 1 | Close the rule gaps: script kind, unsafe rule, enforcement in every profile, seed syntactic twins | S4-A, S4-B, S4-C, S4-D, S4-F |
| 2 | Typed dynamic values (JSON/YAML/SDN enums), after the enum bug fixes | S9-A, S8-B |
| 3 | HM stage 1: fresh variables, write-back, T2, arms, local forms, annotation diagnostic | S1-A..D, S2-A..G, S4-E, S8-A, S8-E |
| 4 | Explicit `any` to `<T>` | S8-C, S8-D, S8-G |
| 5 | Extern declarations off `any` and off generics | S6-A, S6-B, S6-C, S6-D |
| 6 | Implicit generics over the erased body | S3-A, S3-B |
| 7 | Rewrite tag-dispatching code to enums/records | S8-F, S8-H |
| 8 | Constraint inference | S5-A, S5-B |
| 9 | Registry, codec, ratchets, parity | S6-E, S6-F, S4-G, S7-A..C |
| 10 | Flip warn to error | S8-I, S8-J |
| 11 | Only if approved: specialization and trait objects | S3-C, S6-G (Q1); S9-B, S9-C (Q9) |

## S1: disagreeing-arm compile error

**Goal (§5.6):** a value-position `if`/`match` whose arms have different types
is an error naming both types and both locations.

| Lane | Files | Acceptance |
|------|-------|------------|
| S1-A | seed `compiler/src/hir/lower/expr/control.rs` (`join_value_arms`, `join_class`, `join_types_disagree`), `hir/lower/lowerer.rs`, `hir/lower/mod.rs`, `hir/lower/tests/conditional_empty_array_tests.rs`, `driver/src/exec_core.rs` | `1` vs `"a"`, `{}` vs `5`, `[f64]` vs `[i64]` refused in safe code; int vs float joins to float with the int converted; the same sources accepted in `unsafe` and in a script unit |
| S1-B | seed `hir/lower/expr/control.rs` (judged set), `hir/lower/error.rs` | two different structs, two different enums, tuples of different shape refused; declared-union arms accepted; `Option` per Q4; message carries both arm locations |
| S1-C | new corpus `test/fixtures/type_inference/` (must-fail + must-pass twins) and a manifest of verdict, message class and primary location per fixture | a fixture without a twin, or without a manifest row, fails the manifest check |
| S1-D | self-hosted `30.types/type_infer/inference_control.spl`, `inference_expr.spl`; `20.hir/hir_lowering/_Expressions/` | all S1 corpus fixtures: same verdict as the seed |

S1-A does not judge `ANY`, struct, enum, `Option`, tuple or suffix-guessed
method results. That is a stated limit closed by S1-B and S4, not a defect.
The seed's own type crate ignores the unification result for arms
(`type/src/checker_infer.rs`); S1-B decides whether to fix that too or leave
the lowering as the single owner.

## S2: monomorphic inference of private unannotated functions

**Goal (§5.1, §5.2):** an unannotated parameter is a type variable, never
`any`. A private function whose body and same-module call sites determine one
closed type gets that signature and one copy of code. Covers about 85 to 90%
of the 1,390 unannotated functions [est].

| Lane | Files | Acceptance |
|------|-------|------------|
| S2-A | seed `hir/lower/implicit_generic.rs` (new), `hir/lower/tests/implicit_generic_tests.rs` (new), `hir/lower/error.rs`, `hir/lower/expr/{calls,access,control,operators,mod}.rs`, `hir/lower/module_lowering/{function,module_pass}.rs`, `hir/lower/{context,lowerer,stmt_lowering}.rs`, `pipeline/script_detection.rs`, `pipeline/native_project/compiler.rs`, `driver/src/exec_core.rs` | `fn f(x): x` gives `[f64]` for `f([1.5])` and `i64` for `f(3)`; an uninferable result is refused at its typed use in safe code; allowed in `unsafe` and script |
| S2-B | self-hosted `30.types/type_infer/inference_control.spl` (`infer_function`), `type_infer/context.spl` | two unannotated parameters of one function get distinct variables; no variable shares id 0 with the sentinel; a regression spec fails on the old code |
| S2-C | self-hosted `30.types/type_infer/typed_module_owner_v1.spl`, `80.driver/hir_typecheck_consumer_v1.spl`, retire `20.hir/inference/types.spl` as a second engine | after the typecheck consumer, a local whose type was inferred has that type in HIR (not `Any`) for every type kind, not only i64/bool/unit; MIR lowering sees no `Any` for it |
| S2-D | census script; `export` handling in module resolution (both compilers) | each of the 386 functions classified as dead, or used cross-file without export; a decision recorded (enforce, widen, or treat as T1); the chosen rule has a must-fail fixture |
| S2-E | self-hosted: new SCC/call-site module beside `type_infer/generic_calls.spl`; `type_infer/inference.spl` | all call sites agree: one function symbol, no call-site decode (count symbols in the object or IR); a self-recursive private function is inferred; `fn half(x): x / 2.0` is `f64 -> f64` |
| S2-F | self-hosted `type_infer/inference_expr.spl`, `20.hir/hir_lowering/types.spl` (the silent `Any` producers for bare `list`, argless `Dict`/`Option`/`Result`, `fn(...)`) | `var xs = []` then `xs.push(1.5)` is `[f64]`; never-constrained `[]` refused with the paste-able annotation; `var found = nil` then an assignment is `T?`; lambda parameter typed from the expected function type |
| S2-G | seed `hir/lower/expr/control.rs` (lambda default), `compiler/src/type_inference_config.rs` (`[]` default), `hir/lower/expr/calls.rs` (numeric builtins) | a non-`i64` lambda argument is no longer read as `i64`; `[]` filled with text is not `[i32]`; each has a fixture that produced a wrong value before |

## S3: implicit generics, instance cap, dedup

**Goal (§5.3 to §5.5, §6):** fewer than 30 functions today [est]. One known
real case to use as the first fixture: `_join` in
`src/lib/common/serialization/__init__.spl` (`[i64]` and `[bool]`).

| Lane | Files | Acceptance |
|------|-------|------------|
| S3-A | self-hosted `type_infer/generalization.spl`, `type_infer/generic_calls.spl`; one shared constant for the cap | a function called at 2 type vectors has 2 instances and **one** body; the same vector from 5 call sites is 1 instance; `cap + 1` vectors refused with the call sites listed; a `var` binding is not generalized |
| S3-B | self-hosted: detection in the S2-E SCC module; `30.types/higher_rank_poly*.spl` | polymorphic recursion refused with both instantiations and locations; a parameter used at two types in one body refused; a body that dispatches on a runtime tag refused with "use an enum"; ordinary recursion still inferred |
| S3-C | self-hosted `50.mir/_MirLowering/function_lowering.spl`; both runtimes if B/C | per Q1. Under A this lane does not exist. Under B or C: scalar instances contain no tag operations; total bodies bounded by cap times T3 functions |

## S4: script and unsafe definition, `pub` annotations, `any` diagnostics

**Goal (§3, §4.1, §12):** make the rule hold in every profile, as warnings
first, behind one definition of "safe code".

| Lane | Files | Acceptance |
|------|-------|------------|
| S4-A | self-hosted `10.frontend/core/parser.spl` (module carries the source kind; `parser_path_is_script` stays the `LOG001` rule only), `80.driver/driver_hir_pipeline_lowering.spl` and `driver_hir_pipeline_passes.spl` (stop using `CompileMode.Interpret` as the gate) | a library module run interpreted is `Module`; an `.spl` with top-level statements and no `fn main` is `Script`; a `.shs` is `Script`; a module under `test/` that is not a script unit is `Module` |
| S4-B | seed `pipeline/script_detection.rs` (one predicate; `SCRIPT_ENTRY_ATTR` from S2-A), callers that read script state directly | same four cases as S4-A, same verdicts |
| S4-C | self-hosted `80.driver/hir_semantic_consumer_v1.spl` (grant list is empty today), `35.semantics/any_escape/`; seed `hir/lower/context.rs` and `module_lowering/function.rs` (`FunctionDef::has_unsafe()` has no callers) | per Q5: the chosen unsafe forms exempt `any`, others do not; an `@unsafe` function body is unsafe in the seed |
| S4-D | self-hosted `80.driver/driver_hir_pipeline_lowering.spl` (the Robust/Critical gate), `20.hir/hir_lowering/types.spl`, `35.semantics/any_escape/`, `scripts/check/any_warn_rules_scope.txt` | default profile warns on written `any`, `[any]`, `any`-valued dicts and on an expression whose inferred type is `Any` in safe code; nothing warns in unsafe/script; the rules run in the typecheck consumer with no extra process (time one file before and after) |
| S4-E | self-hosted `type_infer/api_signature_projection_v1.spl`, `90.tools/lint/`, the suggestion code behind `W-ANY-DECL-001` | unannotated `pub`, `export`-listed functions and methods warn; the message contains a paste-able signature; private functions and trait `impl` methods do not warn |
| S4-F | seed `hir/lower/error.rs` (`MissingParameterType`, `CannotInferType`, `EmptyArrayNeedsType` reachable as warnings in production), `pipeline/lowering.rs`, `compiler/src/lint/mod.rs` | written `any` outside unsafe and an unannotated parameter of an **exported** function in a `Module` warn in the seed with the same text and code as the self-hosted compiler; a private unannotated function does **not** warn (the seed must never be stricter than the self-hosted rule, design §11) |
| S4-G | `scripts/check/check-any-inventory-ratchet.shs`, `check-any-warn-rules-ratchet.shs`, `check-any-escape-census.shs` and baselines; a new baseline for unannotated exported functions; a per-directory severity table | a new site in a baselined directory fails; a stale baseline fails; a directory with an empty baseline reports errors; changing a private function's inferred type leaves the module's interface digest unchanged |

The digest test in S4-G is the check behind the build-speed argument in §10.2
and must not be dropped as obvious.

## S5: trait-bound inference for method calls

**Goal (§5.3, §8):** the risky stage. Explicit bounds are rare in the tree, so
the solver has had little exercise. Failure mode must be the "annotate" error,
never wrong code.

| Lane | Files | Acceptance |
|------|-------|------------|
| S5-A | self-hosted `type_infer/{traits,trait_collection}.spl`, `25.traits/trait_method_resolution.spl`, `25.traits/trait_solver.spl` | `pub fn pretty_print(value) -> text: value.to_text()` shape, made private and called at two types that both have the method, is accepted; a call site whose type lacks the method is refused at that call site; arithmetic on an unbounded `T` refused; `z.0` infers a tuple; `p.name` on a T3 parameter refused |
| S5-B | self-hosted `type_infer/traits.spl`, `25.traits/trait_solver.spl` | an inferred bound is resolved statically at each instantiation and never becomes dynamic dispatch; a written `dyn Trait` is unaffected |

## S6: SFFI thin ABI, `Handle<T>`, codec, unboxed collections

**Goal (§7):** no `any` and no type parameter on the ABI; typed safe wrappers;
one registry row per raw function. 96.5% of externs already fit [est]; the
work is 131 + 133 + 23 declarations and the registry.

| Lane | Files | Acceptance |
|------|-------|------------|
| S6-A | stdlib handle type; handle externs in the seed std (`collections/btreemap.spl` and peers) and `src/lib` | first, a written answer: does the language have a zero-cost generic newtype over `i64`? If not, that is the lane. Then: passing a `Handle<A>` where `Handle<B>` is expected is a compile error; generated code for a handle call has no wrapper object and no tag operation; every wrapper is `@always_inline` |
| S6-B | the 133 generic `extern fn` declarations (`rt_transient_heap_promote`, `rt_enum_discriminant`, `rt_array_free`, ...); a guard under `scripts/check/` | zero `extern fn name<...>` in `src`; each has a generic wrapper with the old call shape; the guard fails on a new generic extern; no runtime change (`check-rt-dual-implementation-ratchet.shs` delta zero) |
| S6-C | `unsafe_addr_of` copies under `src/os`; `concurrency/threads.spl` and the callback externs | one definition of `unsafe_addr_of<T>`; callbacks typed `<D, R>` over `fn(D) -> R` |
| S6-D | seed std `collections/` (`hashmap.spl`, `btreemap.spl`, ...) | no `any` in the public collection API; existing collection specs pass |
| S6-E | registry rows and schema; generator beside `src/app/sffi_gen.templates/`; generated Simple externs, Rust signatures (`src/compiler_rust/runtime/`), C prototypes (`src/runtime/`); parity guard wired through `config/check/must_check_gates.sdn`; seed interpreter table `compiler/src/interpreter_extern/mod.rs` | for the hot symbols: deleting any one output fails the guard; changing a parameter type in one output fails the guard; regeneration is byte-stable; a row with `any` or a type parameter is rejected by the schema; a symbol missing from the interpreter table fails |
| S6-F | self-hosted `50.mir/_MirLoweringExpr/expr_dispatch.spl` (`box_runtime_value` / `decode_runtime_value`); registry class `tagged`; `check-raw-sffi-unsafe-ratchet.shs`, `check-no-direct-rt.shs` | a generic wrapper call at a known scalar `T` emits the existing inline decode and no tag check in safe code; `[T]` indexing, `len`, `push` and text concat remain compiler intrinsics (no new call per element: compare IR before and after); a call to a `tagged` row from safe Simple fails the guard |
| S6-G | both runtimes (`src/compiler_rust/runtime/src/value/heap.rs`, `collections.rs`; `src/runtime/runtime_native.c`), the legacy boxed C array (`src/runtime/runtime.h`), the seed interpreter array value, the inline packed reader in the LLVM backend; stdlib `FfiCodec<T>` | `Array<f64>` stores 8 bytes per element with no box; interpreter, JIT and native agree on a differential fixture; both runtimes define every new symbol; a scalar codec inlines to nothing |

`rt_sqlite_*` rows stay a mimic over the embedded engine (CLAUDE.md, "No
external SQLite"); the registry does not change that.

## S7: parity and differential test

**Goal (§11):** same verdict from both compilers for every check both
implement, and a bootstrap closure that needs no inference from the seed.

| Lane | Files | Acceptance |
|------|-------|------------|
| S7-A | harness under `scripts/check/` driving both compilers over `test/fixtures/type_inference/` against the manifest | a deliberately divergent fixture makes it fail; a compiler that produces no verdict is an ERROR, not a pass; zero fixtures compared is an ERROR |
| S7-B | a guard reading both compilers' cap constant, script predicate cases and message table | the constants differ: FAIL; a check implemented by both with different text or code: FAIL |
| S7-C | none new; evidence only | with S8-A landed, the seed builds `src/compiler` with its unannotated-parameter warning at zero for the closure; the self-hosted rules report zero on the closure; the sanctioned bootstrap (`.claude/rules/bootstrap.md`) completes |

Until a full-CLI self-hosted binary is deployed, self-hosted lanes are verified
through whichever self-hosted entry point can compile the fixtures; record
which one in the lane's evidence. This is a real constraint, not a formality.

## S8: migration

**Goal (§12):** drive every baseline to zero, bootstrap closure first, then
flip warnings to errors. Lanes are by **kind of site**, because the census
shows the kinds, not the directories, determine the fix.

| Lane | Sites | Where most of them are |
|------|-------|------------------------|
| S8-A | 12 functions + 25 `any` uses | `src/compiler` and imported std prefixes |
| S8-B | about 510 | `src/lib/common/json` (136), `src/lib/common/yaml` (75), `src/app` consumers |
| S8-C | about 235 | seed std collections, `src/lib/tooling`, concurrency |
| S8-D | about 145 + 618 in `test/` | seed std `spec/` |
| S8-E | about 830 declarations | `src/lib` (1,234 of the unannotated functions), mirrored trees |
| S8-F | about 60 unique | persistent collections, `deep_equal`/`type_of` users |
| S8-G | remainder of 401 | seed std `synchronization` (39), `mcp` (36) |
| S8-H | unknown until S2-F lands; expected small | spread |
| S8-I | unknown; hidden today | seed lenient fallbacks (`type_resolver.rs`, `import_loader.rs`) |
| S8-J | n/a | severity table; the "Staged warnings" notes in the guides |

Per-site choice, in this order: add the annotation; make it an explicit
generic; replace a closed `any` with an `enum`; replace an open `any` with a
trait object; only where the code really is a decode of untyped data, move the
body into `unsafe` behind a generic signature. A lane that moves more than a
small share of its sites into `unsafe` stops and reports: that means the
design is missing a case.

Acceptance for each lane: its baseline rows are gone; the affected specs still
pass; no new unsafe grant without a stated reason. S8-B and S8-D change public
API signatures and say so in the PR. A lane over size L is split.

## S9: readiness of elements 3 and 4

**Goal (§8):** the decision text assumes sum types and trait objects already
work. Sum types need bug fixes before the largest migration; trait objects
need language work in the self-hosted compiler.

| Lane | Files | Acceptance |
|------|-------|------------|
| S9-A | the code paths named in `doc/08_tracking/bug/enum_payload_dict_copied_on_function_return_2026-07-28.md` and `enum_pattern_match_optional_value_silent_fallthrough_2026-07-20.md`; regression specs | an enum variant carrying a dict returned from a function keeps its contents in interpreter and JIT; matching a `T?` against payload patterns matches; a `JsonValue.Object` round-trip fixture passes on both |
| S9-B | self-hosted method-call lowering (the "several implementors" compile error), trait metadata and object layout; seed `compiler/src/codegen/llvm/functions/objects.rs` (layout agreement, object-safety check) | a `[dyn Trait]` array holding two implementors dispatches each call to the right one in the self-hosted compiler; seed and self-hosted agree on a differential fixture; a trait that is not object-safe is refused by both |
| S9-C | the open-set sites S8 left on the baseline (spec matchers first) | those baseline rows are gone; no `any` |

S9-A is a prerequisite of S8-B. The related open enum bugs (associated
function on the JIT, bare-name variant collision, large-match build blocker,
enum equality lowering, hashed versus positional discriminants) are outside
S9-A but must be checked against each S8-B change; a migration that trips one
stops and files it. `src/app/desugar/trait_static_dispatch.spl` is a source
rewriter outside the compiler pipeline and is not part of S9-B.

## Risks to the plan itself

- **The deployed compiler is the seed.** Under the recommended Q6 answer,
  T2/T3, write-back and bound inference reach users only when a full-CLI
  self-hosted binary is deployed. Until then `bin/simple` enforces the arm
  join, stage-1 identity, the mis-typing fixes and the syntactic warnings.
- **Enum bugs block the largest migration.** S8-B does not start before S9-A.
- **Wrappers cost a call where nothing inlines** (bootstrap builds, the
  interpreter). S6 lanes mark wrappers `@always_inline` and keep collection
  access as intrinsics; an S6 lane is not accepted on a test pass alone.
- **Q1 unanswered** stalls S3-C and S6-G only.
- **Q5 unanswered** stalls S4-C and, through it, S4-D and S4-F. Ask first.
- **Q6 answered the other way** roughly doubles S2, S3 and S5.
- **S2-C is the long pole.** Nothing after S2 produces better code until
  inferred types reach HIR; before that the engine only diagnoses.
- **S2-D may move functions between tiers.** If privacy is not enforced, up
  to 386 functions move from T2 to T1 and S8-E grows by that many.
- **The T2/T3/T4 split is from samples of 15 and 40.** S2-E should print the
  real split on first run; re-check S3 and S8-F sizes then.
- **Seed lanes collide** in `hir/lower/`. Mitigated by the new-file rule and
  by keeping the seed's scope small.
