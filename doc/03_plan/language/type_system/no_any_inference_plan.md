# Plan: No `any` in Safe Code (Inference, Implicit Generics, Thin SFFI)

**Design:** `doc/05_design/language/type_system/no_any_inference_generics.md`
(owner-approved 2026-11-27). Section references (§n) and questions (Q2..Q11)
are to that file.
**Status:** S1-A and S2-A are in flight in the seed. Everything else is not
started. Adjacent seed fixes landed 2026-11-27: PR #12235 (long `match` chain
JIT stall) and PR #12236 (nested `Option`/`Result` patterns in JIT `match`).
**Decided 2026-11-27 (design §13.1):** full monomorphization (reverses the
2026-10-31 erased-body decision); `any` in any `unsafe` and in script mode;
source mode by file kind and config; syntactic checks only in the seed.
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
- **Seed scope (decided):** the full inference engine is built once, in the
  self-hosted compiler. The seed gets fixes for its silent mis-typings and
  syntactic twins of the checks. Two seed lanes go beyond that and are **open
  owner questions (Q13)**, kept in the table but marked: S2-A (type variables
  in the seed, lane d29-c) and S3-E (seed monomorphization).
- Lanes gated on an owner question say so; the questions still open are
  collected under "Open owner decisions" below.

### Rules for every lane

- Negative fixtures are **compiled-mode** units (§3.2). Until S4-A and S4-B
  land, the seed heuristic treats an entry file with top-level statements as
  script, so top-level code in a spec proves nothing about safe code; put the
  must-fail source in a fixture module. Every must-fail fixture has a
  must-pass twin.
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
| S2-A | Seed: stage-1 implicit generic (identity shape), `UninferredType` as a **warning** first, script-entry attribute (in flight, lane d29-c). Inference in the seed: scope **open (Q13)** | G0 | M | none; **Q13** |
| S2-B | Self-hosted: fresh type variable per unannotated parameter (`bind_mono` / `Infer(0,0)` fix) | G0 | S | none |
| S2-C | Self-hosted: one inference engine; write inferred types back to HIR | G1 | L | S2-B |
| S2-D | Privacy precondition: classify the 386 private functions with no same-file call site; enforce file privacy or widen scope | G0 | M | none |
| S2-E | Self-hosted: T2. SCC over unannotated private functions, body + same-module call-site constraints, one monomorphic copy | G2 | L | S2-B, S2-C, S2-D |
| S2-F | Self-hosted: local forms. Empty-literal element variable, `nil` binding as `T?`, lambda parameters from the expected type, argless generic types | G1 | M | S2-B |
| S2-G | Seed: fix silent mis-typings (lambda parameter `I64`, `[]` as `[I32]`, numeric builtins on `ANY`) | G1 | S | S2-A |
| S3-A | Self-hosted: T3. Generalize at SCC exit, one instance per distinct call-site type vector, value restriction, cap on implicit generics, over-cap error (bodies emitted by S3-D) | G3 | M | S2-E |
| S3-B | Self-hosted: refuse polymorphic recursion, higher-rank use, tag-dispatching bodies | G3 | M | S2-E |
| S3-C | Monomorphization baseline: record binary size, bootstrap time and compile time on the erased build; dry-run instance count for the 1,208 explicit generics: a plain synchronous worklist over the stored `needed-instance|` sections and `open_needs` (outputs of S3-F1, S3-F2), no async engine and no code generation | G1 | M | S3-F0, S3-F1, S3-F2 (early-start stages; they do not depend on S3-D) |
| S3-D | Self-hosted: **specialization query + output invariant** (reframed 2026-11-28; no `40.mono` stage or whole-program pass is restored). A reference to `Template<Args>` requests the instance through the single-flight reader; one async task builds concrete TLDR view, specialized body, MIR and object, each a set-once content-keyed artifact. "No type parameter, `Infer` or `Any` reaches MIR" is checked on every task's output. Remove the erased lowering for safe code. Sub-stages S3-F3, S3-F4 | G2 | L | S3-C, S2-C; pseudo-immutable PI-S1-1..PI-S1-3, PI-S2-1 |
| S3-E | **Open (Q13).** Seed: monomorphize explicit generics; `type_resolver.rs:320-322` stops erasing `T` to `ANY`. Runs only if the owner decides the bootstrap-only seed must monomorphize | G2 | L | S3-C; **Q13** |
| S3-F | Instance traceability through TLDR: needed-instance sections, cross-module dedup by `ConcreteTldrKey` (the single-flight slot), per-instance object keys, reverse references, invalidation, trace queries, remote action, coverage gates. Sub-stages S3-F0..F10 below | G3 | M | S3-D for S3-F3 onward; S3-F0, F1, F2, F6 (early half) and F10 have no S3-D or S3-C dependency |
| S3-G | Budget gates: instance-count, code-size, build-time and run-time benchmark checks against the S3-C baseline | G4 | M | S3-D, S3-E; Q11 |
| S3-H | Retire the erased-model statements: `.claude/rules/language.md`, the 2026-10-31 generics plan header, any guard that assumes erasure, the guides | G5 | S | S3-D, S3-E |
| S4-A | Self-hosted: resolve `source_mode` per unit (file kind, `simple.sdn`, CLI, header attribute), store it on the parsed and HIR module and in the cache key; replace the `CompileMode.Interpret` gates and the `parser_path_is_script` use | G0 | M | none |
| S4-B | Seed: the same resolution; replace the top-level-statement heuristics, including `set_entry_script_mode` (lane d29-e) and `SCRIPT_ENTRY_ATTR` (lane d29-c) | G1 | M | S1-A, S2-A, S4-A |
| S4-C | Unsafe rule: any `unsafe` block or function admits `any`; drop the `type_erasure` requirement from the escape checker and its messages; seed `@unsafe` functions set the unsafe depth; ratchet `any` uses inside unsafe | G0 | M | none |
| S4-D | Self-hosted: `any` diagnostics in every profile as warnings, scope widened from `src/compiler/**` to all safe code | G1 | M | S4-A, S4-C |
| S4-H | Interpreter in compiled mode: the interpreter and the test runner run the front-end checks for compiled-mode units; `simple.sdn` rows for directories that are script by choice | G2 | M | S4-A, S4-B |
| S4-E | Self-hosted: unannotated `pub`/exported function and method diagnostic, with the inferred signature as a fix-it | G3 | M | S2-E |
| S4-F | Seed: syntactic twins (written `any` outside unsafe; unannotated parameter of an **exported** function in a compiled-mode unit) | G2 | M | S4-B, S4-C |
| S4-G | Ratchets and baselines, per-directory severity, interface-digest invariance test | G4 | M | S4-D, S4-E, S4-F |
| S5-A | Self-hosted: method-presence and unique-trait bound inference checked at instantiation; numeric bound; tuple index; field-on-generic error | G4 | L | S3-A |
| S5-B | An inferred bound stays static: never silently becomes dynamic dispatch | G5 | S | S5-A |
| S6-A | Zero-cost `Handle<T>` (establish the generic newtype over `i64`); migrate handle externs (53 + about 69 declarations) | G0 | M | none |
| S6-B | Generic externs off the ABI (133): parameter becomes the runtime value word, `<T>` moves to the wrapper; guard against new generic externs | G0 | M | none |
| S6-C | One generic `unsafe_addr_of<T>` (about 25 copies); callback wrappers `<D, R>` (4 `any` + 11 `fn(...)` externs) | G0 | S | none |
| S6-D | Seed std collections: generic `<K, V>` API over the handle externs (92 uses) | G1 | M | S6-A |
| S6-E | SFFI v2 registry + generators (Simple extern, Rust signature, C prototype) + parity check including the seed interpreter table; hot symbols first (about 50) | G1 | L | none |
| S6-F | Stdlib `FfiCodec<T>` with scalar and handle codecs, monomorphized and inlined (interim: compiler-inserted decode at statically known `T`); class and ratchet `tagged` rows | G3 | M | S3-D |
| S6-G | `f64`-packed arrays in both runtimes, the legacy C array and the interpreter; typed unboxed `Array<f64>` / `Array<i64>` / `Array<u8>` access as the default | G3 | L | S6-E, S3-D |
| S7-A | Differential harness: both compilers over the corpus against the manifest | G1 | M | S1-C |
| S7-B | Twin conformance guard: same verdict, text and code for every check both compilers implement; source-mode resolution equal (and instance keys, if S3-E runs) | G4 | S | S4-B, S4-F |
| S7-C | Bootstrap-closure proof: seed builds the annotated closure without inferring (its S4-F warning covers exported functions only; private ones are checked by the self-hosted rules); self-hosted rules clean on it | G4 | M | S8-A, S4-D, S4-F, S2-E |
| S8-A | Annotate the bootstrap closure: 12 unannotated-parameter functions and 25 `any` uses in `src/compiler`, plus the std prefixes it imports | G0 | S | none |
| S8-B | JSON/YAML/SDN helper APIs take `JsonValue`/`SdnValue` instead of `any` (about 510 uses) | G1 | M | S9-A |
| S8-C | Explicit `any` to `<T>`: generic stand-ins (about 180) and callbacks / user data (about 55) | G1 | M | none |
| S8-D | Spec helpers (about 145 in `src`, 618 in `test/`): `<T>` for `expect`, a sum type for mixed argument lists (`dyn Matcher` only after S9-B) | G1 | M | none |
| S8-E | Annotation codemod: about 600 exported functions and 230 methods, from the S4-E fix-it | G4 | L | S4-E |
| S8-F | Rewrite genuinely dynamic bodies to enums/records (about 170 raw, about 60 unique) | G4 | M | S3-B |
| S8-G | Seed std remainder (401 explicit uses, less what S6-D and S8-D take) | G2 | M | S6-D, S8-D |
| S8-H | Residual untyped `[]` (1,963 sites), `nil` bindings (58), mixed containers (about 20) that inference does not resolve | G3 | S to M | S2-F |
| S8-I | Unresolved names, types and imports stop becoming `ANY`: **warning only**; its error flip is part of S8-J, never earlier | G5 | M | S4-G |
| S8-J | Flip to error: per directory as its baseline empties; global flip needs empty `src/` baselines **and** a deployed self-hosted binary on Windows, macOS and Linux. Covers all compiled-mode safe code whether or not Q9 builds trait objects | G6 | S | all |
| S8-K | Migrate the units the seed untyped-value rule newly flags: 75 library units, 611 sites (oauth, mqtt, persistent collections, compression, dns, benchmark, ...), one sub-lane per family | G1 | L, split per family | S2-A |
| S9-A | Fix the enum bugs a sum-type migration hits: payload dict copied on return; `T?` match silent fall-through | G0 | M | none |
| S9-B | Self-hosted: multi-implementor dynamic dispatch for `dyn Trait`; one object layout shared with the seed; object-safety check in the seed | G1 | L | **Q9** |
| S9-C | First `dyn Trait` migration targets (open-set cases left on the baseline by S8) | G5 | M | S9-B |

### Parallel groups

| Group | Lanes that run together | Opens when |
|-------|-------------------------|------------|
| G0 | S1-A, S1-C, S2-A, S2-B, S2-D, S4-A, S4-C, S6-A, S6-B, S6-C, S8-A, S9-A | now |
| G1 | S1-B, S1-D, S2-C, S2-F, S2-G, S3-C, S4-B, S4-D, S6-D, S6-E, S7-A, S8-B, S8-C, S8-D, S8-K, S9-B | their G0 inputs landed; Q4 for S1-B/S1-D, Q9 for S9-B |
| G2 | S2-E, S3-D, S3-E (if Q13), S4-F, S4-H, S8-G | S2-C, S2-D, S3-C, S4-B landed |
| G3 | S3-A, S3-B, S3-F, S4-E, S6-F, S6-G, S8-H | S2-E, S3-D landed |
| G4 | S3-G, S4-G, S5-A, S7-B, S7-C, S8-E, S8-F | S3-A, S3-B, S3-E, S4-D..F landed |
| G5 | S3-H, S5-B, S8-I, S9-C | S3-G, S4-G, S5-A, S9-B landed |
| G6 | S8-J | everything else |

**Schedule note (2026-11-28).** S3-D is now a specialization query on the async engine, so G2 opens for S3-D only when the pseudo-immutable steps PI-S1-1..PI-S1-3 and PI-S2-1 have landed as well (none is in `src` today; see S3-F1..F10). Everything behind S3-D inherits that wait: S3-F, S3-G, S3-H, S6-F, S6-G. S3-C (baseline) and the early-start set S3-F0, S3-F1, S3-F2, S3-F6 (early half), S3-F10 do not.

Groups are a lower bound on waiting, not a schedule: a lane may start as soon
as its own "Depends on" cell is satisfied. Four things are worth starting
immediately because nothing blocks them and they shrink everything after:
**S8-A** (after it the seed never has to infer to build the compiler),
**S9-A** (it unblocks S8-B, which is 47% of explicit `any`), **S4-A** and
**S4-C** (no check is meaningful without the source-mode and unsafe rules),
and **S3-C** as soon as a worker is free (the mono budgets need a baseline
taken before anything changes). There are now two critical paths: inference
(S2-B, S2-C, S2-E, S3-A, S5-A) and monomorphization (S3-C, S3-D, S3-F, S3-G).
They meet at S2-C: the mono stage needs inferred types written back to HIR.

## Owner decisions

### Decided 2026-11-27

| Decision | Effect on the plan |
|----------|--------------------|
| Full monomorphization, reversing the 2026-10-31 erased-body decision | S3-C..S3-H added (replacing the optional "selective specialization" lane); S6-F and S6-G are default work, no longer gated |
| `any` allowed in any `unsafe` block or function, and in script mode; no `type_erasure` capability | S4-C is unblocked and moves to G0; it removes the capability requirement instead of wiring grants |
| Source mode by file kind and config, not by execution engine | S4-A/S4-B resolve and carry `source_mode`; S4-H added for the interpreter in compiled mode; the seed heuristics from lanes d29-e and d29-c are replaced |
| Seed: syntactic checks only; full HM inference only in the self-hosted compiler | no seed twins of S2-C, S2-E, S3-A, S3-B, S5-A; S2-A and S3-E go beyond syntactic checks and are open (Q13) |
| Source-mode defaults and names: `.shs` / `.sscript` script, `.spl` compiled; `@source_mode(...)` > `--source-mode` > `simple.sdn [source_mode]` > file kind | S4-A and S4-B implement exactly this; no naming question remains |
| Spec files (`*_spec.spl`) and examples are compiled mode | the 618 `any` uses under `test/` are in scope and migrate under S8-D |

### Still open

| Decision | Assumed by the plan | If answered the other way |
|----------|---------------------|---------------------------|
| **Q8** Enforce file privacy (386 of 553 non-exported unannotated functions have no same-file caller) | enforce, after S2-D classifies them | up to 386 functions move from T2 to T1 and S8-E grows |
| **Q13** Seed items beyond syntactic checks: keep S2-A (type variables in the seed) and run S3-E (seed monomorphization)? | S2-A lands as a bounded bug fix with its rejection as a warning; S3-E does not run | if the seed must monomorphize, S3-E (L) runs and S7-B compares instance keys; if S2-A must be reduced, lane d29-c is cut back to the value-join fix |
| **Q12** Disagreeing arms are an error from the start in the seed, with no warning phase | yes (S1-A) | S1-A ships as a warning and joins the S8-J flip |
| **Q9** Trait objects: build multi-implementor dispatch in the self-hosted compiler | owner to choose | without it S9-B and S9-C do not run; open-set `any` sites migrate to enums or stay baselined |
| **Q11** Monomorphization budget values | set from the S3-C baseline | S3-G |
| Q2 cap value, Q3 uncalled private functions, Q4 `Option` joins, Q10 proposals | see design §13.2 | local to S3-A, S2-E, S1-B/S1-D |

## Recommended order

The census ranks the work by `any` removed per unit of cost. Lanes overlap as
the groups allow; this is the order to staff when workers are scarce.

| # | Work | Lanes |
|---|------|-------|
| 1 | Close the rule gaps: source mode, unsafe rule, interpreter in compiled mode, enforcement in every profile, seed syntactic twins | S4-A, S4-B, S4-C, S4-D, S4-F, S4-H |
| 2 | Typed dynamic values (JSON/YAML/SDN enums), after the enum bug fixes | S9-A, S8-B |
| 3 | HM stage 1: fresh variables, write-back, T2, arms, local forms, annotation diagnostic | S1-A..D, S2-A..G, S4-E, S8-A, S8-E |
| 4 | Explicit `any` to `<T>` | S8-C, S8-D, S8-G |
| 5 | Extern declarations off `any` and off generics | S6-A, S6-B, S6-C, S6-D |
| 6 | Monomorphization: baseline, self-hosted `40.mono`, seed pass, cross-module dedup, budgets | S3-C, S3-D, S3-E, S3-F, S3-G |
| 7 | Implicit generics as instances | S3-A, S3-B |
| 8 | Rewrite tag-dispatching code to enums/records | S8-F, S8-H |
| 9 | Constraint inference | S5-A, S5-B |
| 10 | Registry, codec, unboxed arrays, ratchets, parity | S6-E, S6-F, S6-G, S4-G, S7-A..C |
| 11 | Flip warn to error; retire erased-model statements | S8-I, S8-J, S3-H |
| 12 | Only if approved: trait objects | S9-B, S9-C (Q9) |

S3-C (the baseline) is listed sixth by value but should be taken early: it has
no dependency and its numbers cannot be recovered once the build changes.

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

## S3: implicit generics and monomorphization

**Goal (§5.3 to §5.5, §6):** per-type copies for every generic, explicit and
implicit. This **reverses the 2026-10-31 decision** ("one erased body per
generic function";
`doc/03_plan/compiler/generics/generics_refactoring_formal_verification_plan_2026-10-31.md`
§1A, `doc/08_tracking/bug/monomorphization_deleted_2026-10-31.md`), under
which `src/compiler/40.mono` was deleted. Neither compiler monomorphizes
today. Implicit generics are fewer than 30 functions [est], and no real case
is verified yet (the census sample found 0 of 15). The first fixture is
therefore synthetic; real candidates to check when the classifier first runs
are unannotated helpers such as `negate(z)` / `conjugate(z)` in
`src/lib/common/complex/arithmetic.spl`. The
explicit generics are 1,208 declarations [est] with an **unknown** instance
count, which is why S3-C comes first.

| Lane | Files | Acceptance |
|------|-------|------------|
| S3-A | self-hosted `type_infer/generalization.spl`, `type_infer/generic_calls.spl`; one shared constant for the cap | a function called at 2 type vectors has 2 instances; the same vector from 5 call sites is 1 instance; `cap + 1` vectors refused with the call sites listed; a `var` binding is not generalized; an explicit `<T>` function is not capped |
| S3-B | self-hosted: detection in the S2-E SCC module; `30.types/higher_rank_poly*.spl` | polymorphic recursion refused with both instantiations and locations; a parameter used at two types in one body refused; a body that dispatches on a runtime tag refused with "use an enum"; ordinary recursion still inferred |
| S3-C | measurement scripts under `scripts/check/`; a synchronous worklist over the stored `needed-instance|` sections and `open_needs` (S3-F1, S3-F2 outputs; no code generation, no async engine, not a compiler pass); results recorded under `doc/10_metrics/` by the usual generator | recorded on a named binary identity: stage 2/3 binary size, bootstrap wall time per stage, compile time of the generic-heavy modules; instance count per generic and in total for `src/compiler` and `src/lib`; the top generics by instance count listed. No budget is proposed without these numbers |
| S3-D | **No new stage directory.** Request point in the typed-HIR stage; the instance task in `80.driver/` on the shared scheduler; `generic_subst_model` as the one substitution implementation (restored by S3-F0); `50.mir/_MirLowering/function_lowering.spl` (the `TypeParam` to tagged-`i64` lowering) (no generic-call refusal exists on this line: `20.hir/hir_lowering/_Items/declaration_lowering.spl:325` only mentions `E-GEN-001` in a comment). Design: `doc/05_design/compiler/cache/generic_instance_tldr_trace.md`. Historical only: `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md`, `doc/05_design/compiler/generics/generic_instantiation_model.md`, the deleted stage before `200a05f5bc8` | a generic called at `i64` and at `text` produces two function symbols; the `i64` instance contains no box, decode or tag operation (inspect MIR or IR); no `TypeParam`, `Infer` or `Any` reaches MIR from safe code (a task whose output holds one fails, shown by a fixture); generic types and their methods are instantiated too; interpreter, JIT and native agree on the differential fixtures; the bootstrap completes; no pass runs between HIR and MIR for a program with no generic use |
| S3-E | **open (Q13); runs only if the owner decides the seed must monomorphize.** seed `compiler/src/hir/lower/type_resolver.rs` (lines 320-322 resolve a single-letter type name to `ANY`), a real pass behind `PipelineStage::Monomorphize` (`pipeline_parallel.rs`), MIR lowering and codegen for instances | the same two-symbol and no-tag-operation fixtures pass in the seed; the seed builds `src/compiler`; seed and self-hosted agree on instance keys for the shared corpus. Explicit generics only: the seed does not infer |
| S3-F | see S3-F0..F10 below; `80.driver/driver_build/incremental.spl`, object keys, module interface data (`interface_digest_of`), TLDR companion sections | the same instance requested by two modules is emitted once; editing a generic body invalidates its instances and nothing else (consumer module objects stay); editing a private non-generic body still invalidates no importer |
| S3-G | checks under `scripts/check/` wired through `config/check/must_check_gates.sdn`; benchmark fixtures | a build over the size, time or instance budget fails with the offending generics named; a run-time benchmark set is recorded next to size, so a size win cannot hide a speed loss; the budget values are the ones the owner set (Q11) |
| S3-H | `.claude/rules/language.md` ("Generics are erased"), the header of the 2026-10-31 generics plan, any guard under `scripts/check/` that assumes erasure, `doc/07_guide/language/type_system.md`, `doc/05_design/compiler/generics/generic_instantiation_model.md` | every statement that generics are erased is either removed or dated as historical; no guard still enforces an erased-model assumption. Lands only after S3-D and S3-E, never before: until then those statements are true |

Sequencing notes. S3-D needs inferred types in HIR (S2-C); the collector in
S3-C does not, for explicit generics with annotated call sites. S3-A can land
its classifier and diagnostics before S3-D exists, with instances still
sharing the erased body; the acceptance row about distinct symbols is then
met when S3-D lands. If the first S3-C measurement shows an instance count
that cannot fit any reasonable budget, stop and report before S3-D: the
mitigation of sharing bodies between same-representation instances (design
§6.3) would then be part of S3-D, not an afterthought.

### S3-F0..F10: instances as async queries, traceable through TLDR (added 2026-11-28)

Design: `doc/05_design/compiler/cache/generic_instance_tldr_trace.md`
(TLDR beside it). Owner directions of 2026-11-28: instance traceability goes
through TLDR; specialization is an on-demand, fully async, pseudo-immutable
query in the one engine, **not a pass** (wherever this plan still says
"`40.mono`" or "collector", read "specialization query" and "demand closure");
per-instance copies stay; dictionary or witness passing is out of scope;
invalidation and coverage are stages of their own.

"Needs" names steps of the pseudo-immutable design,
`doc/05_design/compiler/cache/pseudo_immutable_cache_async_build_design.md` §19
(S1-1..S1-6, S2-1..S2-7, S3-1..S3-7, A-1..A-3, B-1..B-3, P-1, P-2), written `PI-...` here
so they cannot be read as this plan's S1..S9 lanes. They are **not** the S1/S2/S3 of
`pseudo_immutable_cache_impl_plan.md` §2, which name other things (§5 there slots
these stages into its waves). Guide = high model (Fable), Impl =
lower model, as in that design. "Tests" says who may author the specs.

| Stage | Work | Needs | Acceptance (one line) | Guide / Impl | Tests |
|-------|------|-------|-----------------------|--------------|-------|
| S3-F0 | Restore `generic_subst_model.spl` (706 lines; pure, no HIR dependency) from `200a05f5bc8^:src/compiler/40.mono/model/` as **the one substitution implementation**, in a non-pass location (not a `40.mono` directory), with its three specs from `test/01_unit/compiler/mono/model/` (laws, flow, refinement); state its correspondence to `src/verification/type_inference_compile/src/GenericSubstModel.lean` (`MType` var / con / app, substitution laws S1-S3, key laws K1-K2). `generic_effect_projection.spl` and `generic_subst_universe.spl` come back only if the specs need them | none | the restored laws spec passes with its universe sizes asserted (a vacuous sweep fails); each Lean theorem names the Simple law it mirrors, and each law the theorem; `mt_key_type` output equals the key text the projector writes for the same type | Fable / lower | sonnet (restore specs); opus (Lean correspondence table) |
| S3-F1 | Provider: `open_needs` on `GenericTemplateEntryV1` (trailing field, section schema v3; not in any template fingerprint, it enters each instance key), filled once by the typed-HIR stage; `body_digest` re-documented | S2-C; PI-S3-1 (write-once slot) | editing a body so that it needs one more instance changes the decoded `open_needs` and the keys of that template's instances; a binder rename changes neither; a v2 reader misses | Fable / lower | sonnet (codec, MC/DC) |
| S3-F2 | Consumer: `needed-instance\|` section codec and producer; concrete-view acquisition (`Concrete` only) | S3-F1; S2-C | module B using `Box<i64>` twice and `Box<text>` once writes two rows with three origins; a `Partial` view writes none and marks the set incomplete | Fable / lower | sonnet (codec); opus (acquisition) |
| S3-F3 | Demand closure: `request_instance` through the single-flight reader, set-once slot per `ConcreteTldrKey`, staged slots (`view`, `layout`, `mir0`, `mir1`, `obj`), request replay on cache hits, quiescence rule, per-key depth and node limits, session budget; by-value layout cycle diagnostic | S3-F2; PI-S1-3, PI-S1-5; the five prerequisites of `tldr_caller_async_prerequisites_2026-10-30.md` | two modules requesting one key start one task; the instance set at quiescence is identical and identically ordered across 20 runs with shuffled task order; a key whose argument nesting is 33, or whose arguments exceed the node limit, fails identically from every requester; a build whose modules are all cache hits yields the same instance set as a cold build | Fable / Fable | opus (ordering, failure wake); Fable reviews |
| S3-F4 | Specialization task (the body of S3-D): substitute with the one `generic_subst_model`, lower, emit; per-task invariant; inlining from callee `mir0` with an availability-independent decision; erased lowering removed for safe code | S3-F3; PI-S1-1, PI-S1-2, PI-S2-1 | S3-D's row; plus a task whose output still holds a `TypeParam` fails its slot and every waiter sees the failure | Fable / Fable | Fable (invariant fixtures); sonnet (symbol-count fixtures) |
| S3-F5 | Keys and artifacts: per-instance key record (view / HIR / object levels), argument definition digests and impl coherence digest, target and toolchain fold, packed blobs (`.spmb` has no owning PI step yet: assign one first), ledger accounting, `BuildSession` free after object emit | S3-F4; PI-S2-6, PI-S3-4..PI-S3-6; PI-A-1 until PI-P-1 | one instance, two targets: one concrete view key, two object keys; RSS after emit returns to the pre-instance level within the session bound | Fable / lower | sonnet |
| S3-F6 | Reverse references: first producer for family `generic-specialization` (body / signature / bound -> instance; instance -> requester). Early half: row shapes, read-manifest route and rows for a module's direct needs. Late half (with S3-F4): rows written by instance tasks | S3-F2 (early half); S3-F4 (late half) | after a build the rows for `Box<i64>` name its template facets and both requesting modules; a corrupt shard gives the existing fail-closed fallback | Fable / lower | sonnet (rows); opus (fallback) |
| S3-F7 | **Invalidation**: the dirty-set table of design §7 as executable cases, each with its negative control; no-change build | S3-F5, S3-F6; PI-B-1..PI-B-3 | second identical build runs 0 instance tasks and 0 links; a body edit rebuilds exactly that template's instance objects and no consumer module object; an argument change, a needed-set change and a target change each dirty exactly the row's set; a struct used as `T` gaining a field, and an impl added for an argument type, rebuild the covering instances; with half the module objects cached the link set is complete; an inlining consumer is rebuilt on a body edit and a calling one is not | Fable / lower | opus (cases); Fable (negative controls) |
| S3-F8 | Trace queries: who / why / from where / cost / dry-run impact, as facts for the one `TraceViewProjection` | S3-F6; the projection itself (extreme-typing lane, not implemented) | "who needs `Pair<i64,f64>`" lists every origin span and the `via` chain to a direct source use, with no file re-parsed (read counter) | Fable / lower | sonnet |
| S3-F9 | Remote: instance task as a content-keyed action for the async local runner or the distributed scheduler | S3-F5; `doc/04_architecture/dist_build_scheduler.md` attempt leases and publication fences | the same instance built locally and remotely is byte-identical; a worker with a revoked fence cannot publish; the input manifest holds no full source file | Fable / lower | opus |
| S3-F10 | Coverage gate and spec set, measured as **decision and condition coverage** (owner decision 2026-11-28; line % later): >= 95 % per touched unit module from unit specs, >= 70 % over the module set from unit + integration + system specs; first diagnose the red `generic_tldr_view_v1_mcdc_spec.spl` (26 of 59 failing under seed `simple-local-20261128f`; cause unknown: spec, seed or source) | none for the gate script; runs with every stage | the gate fails a module at 94 %, passes at 95 %, and reports ERROR (not pass) on a failing spec or an empty denominator | Fable / lower | sonnet (specs); opus (gate selftest) |

**Owner decisions, 2026-11-28.** (1) Coverage is gated on decision and
condition coverage; line % later. (2) One object per instance. (3) **Engine
first:** S3-F3, S3-F4 and everything behind them start only after the
pseudo-immutable async steps land; the mono exclusion in
`tldr_async_owner_integration_2026-10-30.md` stays as written until then, and
no instance request runs on the existing FileFiber / `TldrTableV1` path.
(4) `generic_subst_model.spl` is restored from history as the one substitution
implementation (S3-F0). Q13 unchanged.

**Early-start set (no engine step needed):** S3-F0, S3-F1, S3-F2, the early
half of S3-F6, S3-F10. S3-F1 and S3-F2 may precede the write-once slot
(PI-S3-1) by writing their fields at publication time.

**Critical path: which engine step gates which stage.**

| Stage | Gated by (pseudo-immutable plan) | In `src` today? |
|-------|----------------------------------|-----------------|
| S3-F3 demand closure | PI-S1-3 (`read_tldr_async`), PI-S1-5 (wake-on-publish), and the five caller prerequisites | no / no / no |
| S3-F4 specialization task | S3-F3; PI-S1-1, PI-S1-2 (async stage nodes), PI-S2-1 (`CompileInvoker`) | no |
| S3-F5 keys and artifacts | S3-F4; PI-S2-6 (key record), PI-S3-4 (`.sphb`), PI-S3-5 (ledger), PI-S3-6 (mmap writer); PI-A-1 until PI-P-1 | no |
| S3-F6 late half | S3-F4 | - |
| S3-F7 invalidation | S3-F5, S3-F6; PI-B-1..PI-B-3 (no-change build), PI-S3-7 | no |
| S3-F8 trace queries | S3-F6; `TraceViewProjection` (extreme-typing lane) | no |
| S3-F9 remote action | S3-F5; PI-S2-2, PI-S2-4 | no |

So the shortest route to the first instance object is PI-S1-1, PI-S1-2,
PI-S1-3, PI-S1-5, then PI-S2-1, with S3-F0..F2 done meanwhile. Order behind
the gate: F3; F4; F5 and F6-late; F7; F8 and F9.

Notes for the lanes.

- **`generic_subst_model` is not in `src` until S3-F0.** It was
  `40.mono/model/generic_subst_model.spl`, deleted with the stage; what remains
  is its Lean model and the `mt_key_type` key encoding. S3-F0 restores the
  file, not the stage. `10.frontend/core/type_subst.spl` (global mutable
  tables, AST level) is not a second implementation to grow.
- **Coverage measurement.** The seed's report has no line denominator (hit
  lines only) but registers every decision and condition site at load, which is
  why the gate uses those (design §14). Known blind spot: a branch-free
  function that is never called has no decision; the gate therefore also
  requires every exported function of a touched module to appear in the
  report's `functions` table.
- **S3-H additions (edit when S3-F4 lands, not before):** the header comment of
  `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl:44-47` and the
  `body_digest` comment at `:90` ("single erased body"), and the docstring of
  `generic_template_consumed_facets_v1` (`:287`, "the template's own object
  action"). `doc/04_architecture/generic_rr_hir_variant_obj.md` §2 and
  `doc/05_design/generic_rr_hir_variant_obj.md` §1 already carry a superseded
  pointer; `doc/05_design/compiler/incremental_build/generic_instance_prelink_v1.md`
  describes deleted code and carries one too.
- **Shared with the aspect lane** (`work/aspect-tldr-async-trace-20261128`):
  the scheduler and single-flight path, the reverse-reference coordinator and
  the coverage gate script. Neither lane forks them.

## S4: source mode, unsafe rule, `pub` annotations, `any` diagnostics

**Goal (§3, §4.1, §12):** make the rule hold in every profile, as warnings
first, behind one definition of "safe code".

| Lane | Files | Acceptance |
|------|-------|------------|
| S4-A | self-hosted: source-mode resolver in `80.driver/` (file kind from the extension, then `simple.sdn`, CLI flag, file-header attribute; most local wins); the field on the parsed module (`10.frontend/`) and the HIR module (`20.hir/hir_definitions.spl`); cache key; `80.driver/driver_hir_pipeline_passes.spl` (`script_mode = mode == CompileMode.Interpret`) and `driver_hir_pipeline_lowering.spl` (`mode != Interpret` gate) read the field; `10.frontend/core/parser.spl` `parser_path_is_script` stays the `LOG001` rule only | `.shs` and `.sscript` resolve to script; `.spl` resolves to compiled, with or without top-level statements; a `simple.sdn` path row overrides the file kind; the header attribute overrides the config; a library module run by the interpreter is still compiled-mode; an imported unit has its own mode; changing the config row re-checks the unit |
| S4-B | seed: the same resolver in `driver/src/exec_core.rs` (next to the extension dispatch and `interpreter_preference_reason`); the mode on the function context beside `unsafe_depth` (`compiler/src/hir/lower/context.rs`); remove the heuristic switches `set_entry_script_mode` (lane d29-e) and `SCRIPT_ENTRY_ATTR` (lane d29-c), and stop using `has_script_statements` / `is_script_statement` to decide rules (they keep deciding entry synthesis) | the same cases as S4-A with the same verdicts; an entry `.spl` with top-level statements and no `main` is compiled-mode and gets the arm-disagreement error; the fixtures of S1-A and S2-A that relied on the heuristic are moved to an explicit `.sscript` or config row |
| S4-C | self-hosted `35.semantics/any_escape/` (checker and `types.spl`: the `type_erasure` grant and `te_block_depth` logic), `20.hir/hir_lowering/types.spl` (the `E-ANY-COMPILE-001` text names `unsafe(capabilities: [type_erasure])`), `80.driver/hir_semantic_consumer_v1.spl`; seed `hir/lower/context.rs`, `module_lowering/function.rs` (`FunctionDef::has_unsafe()` has no callers); a ratchet for `any` uses inside unsafe | `any` inside a plain `unsafe:` block, inside `unsafe(capabilities: [ffi]):` and inside an `@unsafe` function body is accepted by both compilers; outside it is refused; no message mentions `type_erasure`; the unsafe-`any` count is frozen at its current value |
| S4-D | self-hosted `80.driver/driver_hir_pipeline_lowering.spl` (the Robust/Critical gate), `20.hir/hir_lowering/types.spl`, `35.semantics/any_escape/`, `scripts/check/any_warn_rules_scope.txt` | default profile warns on written `any`, `[any]`, `any`-valued dicts and on an expression whose inferred type is `Any` in compiled-mode safe code; nothing warns in unsafe or script; the rules run in the typecheck consumer with no extra process (time one file before and after) |
| S4-E | self-hosted `type_infer/api_signature_projection_v1.spl`, `90.tools/lint/`, the suggestion code behind `W-ANY-DECL-001` | unannotated `pub`, `export`-listed functions and methods warn; the message contains a paste-able signature; private functions and trait `impl` methods do not warn |
| S4-F | seed `hir/lower/error.rs` (`MissingParameterType`, `CannotInferType`, `EmptyArrayNeedsType` reachable as warnings in production), `pipeline/lowering.rs`, `compiler/src/lint/mod.rs` | written `any` outside unsafe and an unannotated parameter of an **exported** function in a compiled-mode unit warn in the seed with the same text and code as the self-hosted compiler; a private unannotated function does **not** warn (the seed must never be stricter than the self-hosted rule, design §11) |
| S4-G | `scripts/check/check-any-inventory-ratchet.shs`, `check-any-warn-rules-ratchet.shs`, `check-any-escape-census.shs` and baselines; a new baseline for unannotated exported functions; a ratchet for source-mode overrides that move a `.spl` unit to script; a per-directory severity table | a new site in a baselined directory fails; a stale baseline fails; a new script override fails until baselined; a directory with an empty baseline reports errors; changing the inferred type of a private function leaves the interface digest of its module unchanged |
| S4-H | seed interpreter entry (`driver/src/exec_core.rs`, `SIMPLE_JIT_STRICT` fallback path) and the test runner (`src/app/test_runner_new/test_runner_main.spl`, `std.test_runner.test_runner_execute`: interpreter, SMF, native and compile modes); `simple.sdn` rows for directories chosen to be script | a compiled-mode unit run with `--mode` interpreter gets the same safe-code diagnostics as a native build of the same file; a typed lowering error is not demoted to an interpreter fallback; a script-mode unit runs unchanged; the list of directories marked script is explicit in config, not in code |

The digest test in S4-G is the check behind the build-speed argument in §10.2
and must not be dropped as obvious. Spec files and examples are$
compiled-mode (decided), so expect the 618 explicit `any` uses under `test/` to
warn on the first S4-H run; that is S8-D scope, not a reason to mark `test/` script.

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
| S6-F | stdlib `FfiCodec<T>` trait with scalar and handle codecs; self-hosted `50.mir/_MirLoweringExpr/expr_dispatch.spl` (`box_runtime_value` / `decode_runtime_value`, the interim compiler-inserted form); registry class `tagged`; `check-raw-sffi-unsafe-ratchet.shs`, `check-no-direct-rt.shs` | a wrapper instance at a scalar or handle `T` contains no codec call and no tag operation after inlining (inspect IR); a type without a codec is a compile error at the wrapper; `[T]` indexing, `len`, `push` and text concat remain compiler intrinsics (no new call per element: compare IR before and after); a call to a `tagged` row from safe Simple fails the guard |
| S6-G | both runtimes (`src/compiler_rust/runtime/src/value/heap.rs`, `collections.rs`; `src/runtime/runtime_native.c`), the legacy boxed C array (`src/runtime/runtime.h`), the seed interpreter array value, the inline packed reader in the LLVM backend | `Array<f64>` stores 8 bytes per element with no box, by default and without annotation; element get/set in an `f64` instance is a typed load/store; interpreter, JIT and native agree on a differential fixture; both runtimes define every new symbol (`check-rt-dual-implementation-ratchet.shs` delta zero) |

`rt_sqlite_*` rows stay a mimic over the embedded engine (CLAUDE.md, "No
external SQLite"); the registry does not change that.

## S7: parity and differential test

**Goal (§11):** same verdict from both compilers for every check both
implement, and a bootstrap closure that needs no inference from the seed.

| Lane | Files | Acceptance |
|------|-------|------------|
| S7-A | harness under `scripts/check/` driving both compilers over `test/fixtures/type_inference/` against the manifest | a deliberately divergent fixture makes it fail; a compiler that produces no verdict is an ERROR, not a pass; zero fixtures compared is an ERROR |
| S7-B | a guard reading the cap constant, source-mode cases, instance keys and message table of both compilers | the constants differ: FAIL; a check implemented by both with different text or code: FAIL |
| S7-C | none new; evidence only | with S8-A landed, the seed builds `src/compiler` with its S4-F warning (exported functions only) at zero for the closure; the self-hosted rules report zero on the closure; the sanctioned bootstrap (`.claude/rules/bootstrap.md`) completes |

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
| S8-I (warning only) | unknown; hidden today | seed lenient fallbacks (`type_resolver.rs`, `import_loader.rs`) |
| S8-J | n/a | severity table; the "Staged warnings" notes in the guides |
| S8-K | 611 sites in 75 units (lane d29-c finding) | oauth, mqtt, persistent collections, compression, dns, benchmark and the other families the seed rule flags |

**S8-K.** Lane d29-c's seed rule (a value of uninferable type reaching a typed
use) newly rejects 75 library units. It therefore ships as a **warning** and
goes to error with S8-J. One sub-lane per family; the mirrored trees are fixed
together. These overlap S8-E and S8-F: a site fixed there leaves this list.

**S8-J scope.** The flip covers all compiled-mode safe code. If trait objects
are not built (Q9 answered no), open-set `any` sites are resolved before the
flip by an `enum` where the set can be closed, otherwise by an `unsafe` body
behind a generic signature, counted by the unsafe-`any` ratchet with a reason.
No site is exempted by staying on a baseline. S8-I adds warnings only; nothing
from S8-I becomes an error before S8-J.

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

- **The deployed compiler is the seed.** With inference only in the
  self-hosted compiler (decided), T2/T3, write-back and bound inference reach
  users only when a full-CLI
  self-hosted binary is deployed. Until then `bin/simple` enforces the arm
  join, stage-1 identity, the mis-typing fixes and the syntactic warnings.
- **Enum bugs block the largest migration.** S8-B does not start before S9-A.
- **Wrappers cost a call where nothing inlines** (bootstrap builds, the
  interpreter). S6 lanes mark wrappers `@always_inline` and keep collection
  access as intrinsics; an S6 lane is not accepted on a test pass alone.
- **Monomorphization has no numbers yet.** Instance count, size and build-time cost are unknown until S3-C. S3-D is large and touches every generic in the bootstrap closure; a budget miss found late is expensive, so S3-C gates it.
- **Reversing 2026-10-31 discards working code.** The erased execution model stays until S3-D and S3-E pass; S3-H removes the statements only afterwards.
- **Spec files and examples are compiled-mode** (decided): 618 explicit `any` uses under `test/` enter scope (S8-D).
- **S2-C is the long pole.** Nothing after S2 produces better code until
  inferred types reach HIR; before that the engine only diagnoses.
- **S2-D may move functions between tiers.** If privacy is not enforced, up
  to 386 functions move from T2 to T1 and S8-E grows by that many.
- **The T2/T3/T4 split is from samples of 15 and 40.** S2-E should print the
  real split on first run; re-check S3 and S8-F sizes then.
- **Seed lanes collide** in `hir/lower/`. Mitigated by the new-file rule and
  by keeping the seed's scope small.
