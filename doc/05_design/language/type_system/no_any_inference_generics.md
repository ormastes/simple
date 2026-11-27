# No `any` in Safe Code: Inference, Implicit Generics, Thin SFFI

**Status:** owner-approved design, 2026-11-27, with the follow-up owner
decisions of the same day folded in (§13.1): full monomorphization, `any` in
any `unsafe`, source mode by file kind and config, syntactic-only seed.
**Not implemented** except where §2 says so. Rollout is warn first, then error
(§12).
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
| 3 | Typed sum types (`enum`: `SdnValue`, `JsonValue`) | **closed** heterogeneous data | Yes, with open enum bugs to fix first (§8.1) |
| 4 | Trait objects (`dyn Trait` / `interface`) | **open** heterogeneous data | **No**, not for heterogeneous values in the self-hosted compiler (§8.2) |

Choosing between 3 and 4: if the set of cases is known where the type is
defined, use an `enum`; if other modules must be able to add cases, use a trait
object. Until §8.2 is closed, element 3 is the only working answer for
heterogeneous data and element 1 for homogeneous data.

**What is decided and what is proposed.** The owner decision fixes: the `any`
rule, the four elements, the tiers (locals inferred; `pub`/cross-module
annotated; private agree gives one copy; private disagree gives a capped,
deduplicated implicit generic; over cap or unsupported recursion is an
"annotate" error; disagreeing arms are an error naming both), and warn then
error. Everything more specific in this document is a **proposal** made to
fill in that decision and is listed for confirmation in §13: the
source-mode config names, treating all unannotated methods as must-annotate, the value
restriction, the cap value, the rules for method, field and arithmetic uses of
an inferred `T`, keeping collection access as compiler intrinsics, and
realizing the codec inside the compiler first.

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
  `ANY` (`compiler/src/hir/lower/type_resolver.rs:320-322`). **There is no
  monomorphizer anywhere.** The 2026-11-27 decision reverses this (§6); the
  bullet describes the code as it is today.
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
   `@unsafe` and 3,954 `unsafe(capabilities: [...])` uses [exact]. Decided:
   any `unsafe` admits `any` and the capability requirement goes (§3.1).
6. **No source-mode flag exists** in either compiler, only proxies (§3.2).
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

### 2.4 Seed work landed and in flight

Landed on `release/1.0.0` on 2026-11-27 (seed, adjacent to this design):

- PR #12235 (`work/seed-long-match-chain-stall-20261127`): long `match` chain
  JIT stall.
- PR #12236 (`work/jit-nested-option-result-match-20261127`): nested `Option`
  / `Result` patterns in JIT `match`; the remaining nested optional pattern
  holes found in review are filed under `doc/08_tracking/bug/`.

In flight, not on the release line when this was written:

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

Both lanes decide "script" with an ad-hoc heuristic (an entry file with
top-level statements and no `main`: `set_entry_script_mode` in d29-e,
`SCRIPT_ENTRY_ATTR` in d29-c). That is **not** the decided definition and is
to be replaced by the resolved source mode (§3.2, plan S4-A/S4-B).

Finding from lane d29-c: its seed rule (a value of uninferable type reaching a
typed use is rejected in safe code) newly rejects **75 library units, 611
sites** (oauth, mqtt, persistent collections, compression, dns, benchmark and
others). The rule therefore ships as a warning first (§12, plan S8-K).

## 3. Where `any` is allowed

### 3.1 `unsafe` (decided 2026-11-27)

`any` may be named, created, stored and passed inside **any** `unsafe` code:
an `unsafe:` block (with or without a capability list) and the body of an
`@unsafe` / `unsafe fn` function. There is **no separate `type_erasure`
capability requirement**. The existing escape checker implements the narrower
capability rule and the driver passes it an empty grant list; both change
(plan S4-C). In the seed an `@unsafe` function does not set the unsafe depth
today (`FunctionDef::has_unsafe()` has no callers), so only blocks are visible
there; that is fixed in the same lane.

A value may leave an `unsafe` region into safe code only through a **checked
decode**: an operation that inspects the runtime tag and either yields a typed
value or fails (`Option<T>` / `Result<T, E>`). The decode itself is written in
`unsafe`. This is the only place tag checks occur (§7.5).

Because every `unsafe` now admits `any`, the count of `any` uses inside unsafe
code is ratcheted (it is 0 today), so growth is visible in review.

### 3.2 Source mode: script or compiled (decided 2026-11-27)

**Decision:** whether a source unit is in script mode is determined by its
**file kind**, and a **config setting can change it**. It is not determined by
which engine runs the code: the interpreter can run a unit in compiled mode,
which is what the test runner does.

Two axes that must not be conflated:

| Axis | Question | Values | Set by |
|------|----------|--------|--------|
| **Source mode** | which language rules apply to this unit | `script`, `compiled` | file kind, then config |
| **Execution engine** | what runs it | interpreter, JIT, native (AOT), SMF | CLI / `SIMPLE_EXECUTION_MODE` / test-runner `--mode` |

Every combination is legal. `compiled` source run by the interpreter is the
normal case for `bin/simple test`; `script` source is never an input to a
native build of a library.

#### What the tree specifies today

Read from the tree. No single document states the whole rule, so the gaps are
named and filled as proposals below.

- **File kinds.** `doc/07_guide/language/naming_convention.md` §8 defines two
  extensions: `.spl` (Simple source: application, library, compiler and test
  code) and `.shs` (shell scripts). The seed driver additionally accepts
  `.simple` and `.sscript` as Simple source (`driver/src/exec_core.rs`,
  `driver/src/cli/basic.rs`) and diverts `.shs` to the interpreter
  (`interpreter_preference_reason` returns `shs-extension`).
- **Config precedence that already exists for a neighbouring setting.**
  `doc/07_guide/language/strictness_tiers.md` ("Strictness Tiers (Script
  Modes)") selects `moderate` / `lib` / `reliable` with most-local-wins
  precedence: file-header attribute `@lint_profile(...)`, then CLI
  `--profile`, then `simple.sdn` `[lints] profile`. `moderate` is described
  there as the tier for scripts, prototypes and examples.
- **Engine selection.** `SIMPLE_EXECUTION_MODE`, the test runner `--mode`
  (`TestExecutionMode`: interpreter, SMF, native, compile, safe mode) and the
  self-hosted `CompileMode` (`Interpret`, `Jit`, `Aot`, `Check`, `Sdn`,
  `SmfExec`). These choose an engine and say nothing about source mode.
- **Not in the tree before this decision:** a config key that sets source
  mode, and a statement of which mode a `.spl` file with top-level statements
  is in. Both are now decided (§13.1, D5 and D6) and specified below.

#### Default by file kind

| File kind | Default source mode |
|-----------|---------------------|
| `.shs` | `script` |
| `.sscript` | `script` (the extension exists for this; today the seed only treats it as Simple source) |
| `.spl`, `.simple` | `compiled` |

A `.spl` file is `compiled` by default **whether or not it has top-level
statements**. Top-level statements decide how an entry point is synthesized,
not which rules apply. This is where the decided rule differs from the
heuristics now in the tree (below). Decided (D6): spec files (`*_spec.spl`)
and examples are compiled-mode source and follow the safe-code rules.

#### Config, and precedence (decided, D5)

Most-local wins, the same order the strictness tier already uses:

1. **File-header attribute** on the unit: `@source_mode(script)` /
   `@source_mode(compiled)`.
2. **CLI flag** for the invocation: `--source-mode=script|compiled`,
   applying to the entry unit only.
3. **`simple.sdn`**: `[source_mode]`, a project default
   (`default = "compiled"`) plus path-prefix rows.
4. **File kind** default from the table above.

The row syntax inside `[source_mode]` is an implementation detail of plan
S4-A. An environment variable is
deliberately not in the list: mode must be a property of the source tree, so
that the same file means the same thing on every machine.

Source mode is separate from the strictness tier. A `script` unit normally
also runs at `moderate`, but the tier governs lint severity while source mode
governs the `any` and inference rules; neither implies the other.

Overrides are visible: a config row or attribute that moves a `.spl` unit to
`script` is counted by a ratchet, like unsafe uses, because it is the other
way to switch the rule off.

#### Interpreter in compiled mode

When the interpreter runs a `compiled` unit it applies the same front end as a
native build: parse, HIR lowering, type inference and the safe-code checks run
and their errors are errors. Only code generation differs. The dynamic value
representation inside the interpreter is an implementation detail and does not
make the source "script". The test runner already works this way in spirit: it
selects an engine per run (`--mode`) over the same spec source, and the seed
`SIMPLE_JIT_STRICT` path already refuses to demote a typed lowering error to
an interpreter fallback.

What has to change for this to be true everywhere: today the self-hosted
driver computes `script_mode = (mode == CompileMode.Interpret)`
(`80.driver/driver_hir_pipeline_passes.spl`) and gates the `any` ban on
`mode != Interpret` (`driver_hir_pipeline_lowering.spl`). Left as is, library
code would escape the rule on every `bin/simple test`. Both sites read the
source mode of the unit instead.

#### How lowering and the type checker learn the mode

1. The **driver** resolves the mode once per unit, from path, extension,
   config and header attribute, before parsing the body.
2. It is stored on the **parsed module** as `source_mode` and copied to the
   HIR module.
3. **HIR lowering** reads it from the module (the seed function context
   carries it next to `unsafe_depth`); the **type checker** and the
   `any`-escape pass read it from the HIR module.
4. It is part of the **cache key** of the unit, so a config change re-checks
   the unit, and it is **not** inherited across imports: each imported unit
   has its own mode.
5. No pass re-derives it from the path, the engine or the AST shape.

#### What differs between the two modes

| Rule | `compiled` | `script` |
|------|-----------|----------|
| `any`, `[any]` | only in `unsafe` | allowed |
| Unannotated parameter | type variable; tiers of §5 | dynamic, as today |
| Undeterminable type | compile error | dynamic value |
| Disagreeing `if`/`match` arms | compile error | allowed |
| Exported function unannotated | error (after rollout) | allowed |
| Top-level statements | allowed (entry synthesis) | allowed |
| Imported by compiled code | yes | only through annotated exports, checked at the boundary |
| Native / AOT build target | yes | no; scripts are run, not linked into libraries |
| Calling a typed function with a dynamic value | n/a | runtime tag check at the call, runtime error on mismatch |

#### Heuristics to be replaced

Three proxies exist today. None is the decided definition; S4-A and S4-B
replace all of them with the resolved `source_mode`.

| Proxy | Where | Why it is wrong |
|-------|-------|-----------------|
| Entry file with top-level statements and no `main` | seed: `has_script_statements` (`pipeline/script_detection.rs`), `is_script_statement` (`pipeline/native_project/compiler.rs`), and the ad-hoc switches added by the in-flight seed lanes: `set_entry_script_mode` (lane d29-e) and `SCRIPT_ENTRY_ATTR` / `__script_entry` (lane d29-c) | a `.spl` spec or example is `compiled` by file kind; AST shape is not the rule. **To be replaced** |
| Execution engine | self-hosted `CompileMode.Interpret` | exempts library code whenever it is interpreted |
| Path | self-hosted `parser_path_is_script` (`10.frontend/core/parser.spl`: `examples/`, `scripts/`, `test/`, `fixtures/`, `repro/`) | written for the `LOG001` print lint; paths belong in config rows, not in the parser |

The in-flight lanes needed a switch in order to land. It is temporary and its
replacement is tracked.

Consequence for tests: under the default a spec file is `compiled`, so a
negative test can live in an ordinary fixture module, and the 618 explicit
`any` uses under `test/` are in scope for migration unless config marks a
directory `script`.

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
| T3 | private, call sites **disagree** | implicit generic, instances capped and deduplicated | fewer than 30 | one copy per distinct type vector (§6) |
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
says it may not be. This is an open owner decision (Q8). Before T2 is relied
on, either file privacy is enforced (a
use of a non-exported function from another file is an error), or the scope of
call-site collection is widened to the package, or a private function with no
same-file call sites is treated as T1. A private function with no call sites
at all whose body does not determine its types has nothing to infer from (Q3).

### 5.3 T3: implicit generic

If type variables remain after the body is solved and call sites supply
different closed types, the function is generalized over the remaining
variables and instantiated per distinct call-site type vector. The inferred
variables become ordinary type parameters and take the same path as an
explicit `<T>`. No real T3 case is verified yet: the census sample found 0 of
15 private functions with disagreeing call sites. Candidates to check when the
classifier first runs are unannotated helpers whose callers pass different
types, such as `curry2(f)` in `lib/common/functions.spl` (exported, so T1
today) and the tuple helpers `negate(z)` / `conjugate(z)` in
`lib/common/complex/arithmetic.spl`.

Uses of an inferred `T` inside a T3 body:

| Use | Rule |
|-----|------|
| passed along, stored, returned | fine |
| method call `x.len()` | a **method-presence constraint** checked at each instantiation; if exactly one trait declares the method, infer `T: Trait`; otherwise error "annotate" (S5) |
| tuple index `z.0` | infer a tuple of the arity fixed by use |
| indexing `xs[0]` | an **indexable constraint** (`T` is `[E]`, `text` or a dict), checked at each instantiation like a method; the result type is the element type of that instance |
| named field `p.name` | T2 only; in T3 an error. No row polymorphism. The seed's receiver-blind field search is the unsound shortcut this replaces |
| arithmetic / comparison | requires a numeric bound, else error: without a bound there is no operator to select for the instance. (Under today's erased model the same shape lowers to tagged-word arithmetic, a known wrong-code class) |

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

With full monomorphization (§6) each instance is a real copy of the body, so
the cap bounds code size directly. The cap applies to implicit generics only;
explicit `<T>` is governed by the budgets in §6.3.

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

## 6. Generics are monomorphized (decided 2026-11-27)

**Decision:** full monomorphization. Every generic function and type gets one
copy of code per distinct closed type-argument vector, everywhere: explicit
`<T>`, implicit generics (T3), generic types and their methods.

**This reverses the owner decision of 2026-10-31** ("one erased body per
generic function"), recorded in
`doc/03_plan/compiler/generics/generics_refactoring_formal_verification_plan_2026-10-31.md`
(§1A and the revision 1.1 notes) and
`doc/08_tracking/bug/monomorphization_deleted_2026-10-31.md`, and stated as a
rule in `.claude/rules/language.md` ("Generics are erased - there is no
monomorphization pass"). Under that decision `src/compiler/40.mono` was deleted
(commit `200a05f5bc8`) and the erased execution model was built in its place.
Those documents and that rule remain accurate descriptions of **the code as it
is today** until the lanes below land. Each is updated by the lane that makes
it false, not before.

### 6.1 What has to be built

Neither compiler monomorphizes today.

| Piece | State today | Work |
|-------|-------------|------|
| Self-hosted `40.mono` stage | deleted; older design in `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md` and `doc/05_design/compiler/generics/generic_instantiation_model.md` (marked partly superseded) | restore or rebuild: instance collection from the typed HIR, type substitution over bodies, instance naming, and a post-mono check that no type parameter, `Infer` or `Any` reaches MIR |
| Self-hosted erased path | `TypeParam` lowers to a tagged `i64` (`50.mir/_MirLowering/function_lowering.spl`); box and decode at `T` boundaries | removed for safe code once instances exist; kept only for `unsafe` and script values |
| Seed | a single uppercase letter type name resolves to `ANY` (`compiler/src/hir/lower/type_resolver.rs:320-322`); `PipelineStage::Monomorphize` is a label only; the JIT instantiator compile step is unimplemented | whether the seed monomorphizes at all is open (Q13, §11.2); if it does, a real pass for **explicit** generics only |
| Instance identity | none | canonical closed type vector as the key; one instance per key per program, shared across modules |
| Cross-module instances | none | an instance of a generic from module A requested by module B is emitted once. The body of an exported generic becomes something importers depend on, unlike a private function body |

### 6.2 Dedup and cap

- **Dedup.** Instances are keyed by `(generic, canonical type vector)`.
  Identical keys from any number of call sites or modules are one body.
- **Cap for implicit generics (T3).** A private unannotated function may have
  at most **N** distinct instances; beyond that it is T4 ("annotate"). N is
  proposed as 4 (Q2). The cap exists because the user never wrote `<T>` and
  should be told when a helper has quietly become widely polymorphic.
- **Explicit generics have no cap.** The user asked for genericity. They are
  governed by the budgets in §6.3 instead.
- The cap is a compiler constant, identical in both compilers.

### 6.3 Build-time and code-size budgets

Monomorphization trades build time and binary size for run-time speed. The
2026-10-31 decision was made on that trade; reversing it needs numbers, and
**none exist yet**. Baselines to record before the first mono lane lands, and
gates to hold afterwards:

| Measure | Baseline to capture | Gate |
|---------|--------------------|------|
| Instances emitted, per module and total | 0 (erased) | reported on every build; top generics by instance count listed |
| Compiler binary size (stage 2 and 3) | current erased build | growth budget set from the first measurement; a regression over budget fails |
| Bootstrap wall time, per stage | current | same |
| Compile time of the generic-heavy modules | current | same |
| Object cache hit rate after a private-body edit | current | must not fall: instance bodies are cached by key |

What is known today [census]: 1,208 explicit generic function declarations
exist in `src`, and fewer than 30 functions are expected to become implicit
generics. The instance count for the explicit ones is **unknown** until the
collector runs. That first measurement is its own lane and gates the rest; the
budget values themselves are an open owner decision (Q11).

If a budget is exceeded, in order of preference: share one body between
instances whose type arguments have the same representation and no
type-dependent operation (a compiler optimization, invisible to the language);
outline cold generic code; raise the budget with the measurement recorded.

### 6.4 Consequences

- "Safe code never produces `any`" holds for **generated code** too, not only
  for the type system: a scalar instance contains no tag operation.
- `FfiCodec<T>` monomorphized and inlined, and unboxed `Array<f64>`, are the
  **default** design, not an option (§7.5, §7.6).
- T2 and T3 produce the same kind of code; T3 only differs in having more
  than one copy.
- The 133 generic externs still leave the ABI (§7.2): an instance needs a
  monomorphic symbol to call.
- Erased-model work in flight (the stage-1 identity instantiation of lane
  d29-c, over one erased body) is a stepping stone and is superseded by real
  instances when the seed pass lands.

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
contract types are design-only (`doc/04_architecture/platform/sffi_v2_hardening.md`);
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
  and until monomorphization lands a user-level trait would be dispatched per
  call.
- The compiler already **has** this codec internally: `box_runtime_value` /
  `decode_runtime_value` in `50.mir/_MirLoweringExpr/expr_dispatch.spl`
  (83 call sites), inline for integers of 32 bits or fewer and a runtime call
  for `i64`/`u64`.

With full monomorphization decided (§6), `FfiCodec<T>` as a user-extensible,
monomorphized and inlined trait is the **default** design: each wrapper
instance calls the codec of its concrete `T`, and for scalars and handles that
inlines to nothing.

Sequencing only: before the mono stage exists, a wrapper can be written as
`fn get<T>(a: Handle<[T]>, i: i64) -> T` with the compiler inserting, at the
call site where `T` is statically known, the decode it already knows how to
emit. That gives the same API and safety early, and the wrapper bodies do not
change when the trait takes over.

### 7.6 Typed, unboxed collection storage

Default design, now that monomorphization is decided (§6): `Array<f64>` stores 8-byte floats, `Array<i64>` words, `Array<u8>`
bytes; element access is a typed load; `[any]` is the tagged-element array and
is `unsafe`/script only.

Today [read]: byte-packed and u64-packed arrays exist in both runtimes.
**There is no f64-packed array in either**; floats are heap-boxed per element.
Adding it follows the existing flag pattern in both runtimes and the
interpreter. All collection externs take the tagged word for container and
element, and compiled code boxes every `i64`/`u64` element through a runtime
call.

Adding an f64-packed layout touches four representations [read]: the Rust
runtime, the C core array, the legacy boxed C array (`SplArray` in
`src/runtime/runtime.h`) and the seed interpreter's array value, plus every
accessor.

Hot-path rule: `[T]` indexing, `len`, `push` and text concatenation stay
**compiler intrinsics**. Moving them into Simple library wrappers would add a
call per element unless wrappers inline. Generic Simple wrappers are for the
long tail: handles, tree maps, hash sets, threads, mutexes. Text is not at
risk: it crosses as a concrete `text` with no codec.

### 7.7 Wrappers are not free by default

[read] The seed's small-function inliner refuses a function with a field
access or an allocation, so a wrapper that reads a handle's field does not
qualify. The self-hosted inliner is cost-thresholded, skips its two larger
passes on the LLVM path, and skips **all** inlining under `SIMPLE_BOOTSTRAP=1`.
The interpreter never inlines. So bootstrap-built compilers and interpreted
runs pay a call per wrapper. Rules that follow: every SFFI wrapper is marked
`@always_inline` (already used 796 times in the tree), and a handle is a
newtype, not a class with a field.

## 8. Elements 3 and 4

The decision text says both already exist. The census corrects that for
element 4 and qualifies it for element 3.

### 8.1 Sum types: exist, need bug fixes

`enum` with typed payloads and exhaustive `match` needs no new language
feature. The largest single migration lands here: JSON/YAML/SDN helper APIs
that take `any` (about 510 uses, 47% of all explicit `any`) take `JsonValue` /
`SdnValue` instead.

Cost [read]: both compilers lower an enum match to a chain of pattern tests;
only dense integer matches become a switch. That is cheap for `JsonValue`
(7 variants) and `SdnValue` (8), and a cost for very large enums.

Open bugs under `doc/08_tracking/bug/` that such a migration will hit, and
which are therefore prerequisites, not follow-ups:

- `enum_payload_dict_copied_on_function_return_2026-07-28`: wrong result in
  the interpreter, rejected by the JIT. `JsonValue.Object` carries a dict.
- `enum_pattern_match_optional_value_silent_fallthrough_2026-07-20`: matching
  a `T?` against payload patterns silently never matches.
- Also relevant: `enum_associated_fn_never_called_on_jit_2026-07-28`,
  `enum_variant_resolved_globally_by_bare_name_httpmethod_collision_2026-09-06`,
  `codegen_large_match_dispatch_body_2026-07-27`,
  `backend_plugin_enum_equality_mir_2026_10_12`, and the seed/pure-Simple
  split on enum discriminants (hashed versus positional).

### 8.2 Trait objects: not available yet

`src/app/desugar/trait_static_dispatch.spl` is **not** trait-object support.
It is a line-at-a-time source rewriter that turns `fn f(x: Trait)` into
`fn f<__T0: Trait>(x: __T0)` (static dispatch); it skips `dyn` parameters,
`[Trait]` arrays and multi-line signatures, and it is not in the compiler
pipeline.

| | Parsed | Type-checked | Code generation |
|---|---|---|---|
| Seed interpreter | yes | n/a | trait-object value, dispatch by method name |
| Seed native | yes | no object-safety check | real vtables, pointer in the object header word; falls back to bare-name dispatch when no impl is found |
| Self-hosted | yes | yes, with an object-safety check | fat-pointer layout exists, but calls are devirtualized only: one implementor is a direct call, none is a trap, **several is a compile error** |

The two compilers also disagree on layout (header-word vtable versus fat
pointer), and real `dyn X` uses in `src` are essentially zero.

So element 4 needs language work in the self-hosted compiler
(multi-implementor dynamic dispatch, one layout shared with the seed) before
it can replace heterogeneous `any`. Until then no migration targets
`dyn Trait`; open-set cases stay on the baseline or use an enum.

### 8.3 Inference gap

Method calls on an inferred `T` (§5.3). Explicit bounds are rare in the tree
(116 `<T: Trait>`, 220 `where`, most in the seed std), so the trait-bound
machinery has little real-world exercise. This is the risky inference stage.

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
| Boxing remains until the mono stage lands | T2 already gets concrete types with no boxing once types are written back; generic code stays erased, at the cost it has now, until §6.1 is built |
| Collection access gets slower if moved to library wrappers | indexing, `len`, `push`, concat stay compiler intrinsics (§7.6) |
| Code size growth from per-type copies | dedup by canonical type vector; cap on implicit generics; measured budgets with a failing gate (§6.3). The instance count for the 1,208 explicit generics is unknown until measured |
| Instruction-cache and binary-size regressions hide a run-time loss | the budget lane records run-time benchmarks alongside size, not size alone |

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
| A negative test passes vacuously | fixtures are compiled-mode modules (§3.2); each has a must-pass twin |
| `unsafe` becomes the escape hatch | grants are counted by ratchet; a migration lane that moves more than a small share of its sites into `unsafe` stops and reports |
| The join fix types a join `ANY` in safe code | lane d29-c section A boxes a scalar arm and types the join `ANY` when the sibling is `ANY`. Correct today; under this design the `ANY` sibling is itself the defect, and the boxing path remains for `unsafe`/script only |

## 11. Seed and self-hosted parity

The rule set is defined once, in this document. **Decided 2026-11-27: the Rust
seed gets syntactic checks only. Full HM inference exists only in the
self-hosted compiler.** The seed is bootstrap-only: it has to compile
`src/compiler` plus the std prefixes it imports, and once those are annotated
(plan S8-A) it never needs to infer.

### 11.1 What each compiler implements

| Piece | Seed | Self-hosted |
|-------|------|-------------|
| Source-mode resolution, unsafe rule | yes (same predicate) | yes |
| Written `any` outside unsafe | yes, syntactic | yes |
| Unannotated parameter of an exported function in a compiled-mode unit | yes, syntactic | yes |
| Fixes for existing silent mis-typings (lambda `I64`, `[]` as `[I32]`, then-arm join) | yes; these are wrong regardless of this design | n/a |
| Fresh variable per unannotated parameter | **no** | yes (the `bind_mono` fix) |
| Call-site driven inference, tiers T2/T3/T4 | **no** | yes |
| Types written back to HIR | **no** | yes |
| Trait-bound inference | **no** | yes |
| Monomorphization | **open** (Q13) | yes |

The type crate of the seed already has a unifier, `generalize` and
`instantiate`; they stay uncalled. That is the meaning of "syntactic only".

### 11.2 Two seed items that go beyond syntactic checks

Both are listed as open owner questions (Q13) rather than assumed.

- **Lane d29-c (plan S2-A)** gives unannotated parameters type variables in
  the seed and instantiates the identity shape at call sites. That is
  inference, in the seed. It exists because it fixes a silent wrong-value bug.
  Either it is kept as a bounded bug fix (identity shape only, never extended),
  or it is reduced to the syntactic rule plus the value-join fix.
- **Seed monomorphization (plan S3-E, large).** Full monomorphization was
  decided for the language. Whether the **seed** must monomorphize is a
  separate question: the seed only builds the compiler, and a seed that keeps
  erased generics still produces a working stage 1 as long as the self-hosted
  compiler it builds monomorphizes from stage 2 on. The cost of not doing it is
  that seed-built and self-built binaries differ in generic code generation,
  which the stage-2/stage-3 comparison in the bootstrap must tolerate.

### 11.3 Consequences

`bin/simple` is currently the Rust seed and no full-CLI self-hosted binary is
deployed (`.claude/rules/commands.md`). Tiers T2 and T3, write-back and bound
inference therefore do not exist in the deployed compiler until a self-hosted
binary is deployed. Until then users of `bin/simple` get the syntactic
warnings, the mis-typing fixes and whatever Q13 keeps, and nothing more.

The direction of disagreement is safe: a program the self-hosted HM accepts is
always accepted by the more lenient seed. Under `SIMPLE_BOOTSTRAP=1` the seed
skips lint and several checks and forces lenient types [read]. The syntactic
warnings of the seed must therefore never be stricter than the self-hosted
rule: they cover written `any` and unannotated **exported** signatures, not
private functions that the self-hosted compiler would infer.

Parity that is required: same verdict from both compilers on the shared
fixture corpus for every check both implement; same message text and codes;
same source-mode resolution.

## 12. Rollout

Warn first, then error, the same pattern as the other staged rules in
`doc/07_guide/quick_reference/syntax_quick_reference.md` ("Staged warnings").

1. Source mode (§3.2) and the unsafe rule (§3.1) are implemented first; no
   other check is meaningful without them.
2. Diagnostics land as **warnings** in every profile, with baselines frozen so
   new sites fail review and old ones do not.
3. Migration (S8) drives the baselines to zero, bootstrap closure first.
4. A directory flips to **error** when its baseline is empty.

**Global flip, one trigger.** The quick reference says staged warnings become
errors once Windows, macOS and Linux all have a working self-hosted binary.
That and "the baselines are empty" are the same gate, not two: the full rules
exist only in the self-hosted compiler (§11), so the global flip needs **both**
an empty baseline for `src/` and a deployed self-hosted binary on the three
hosts. Per-directory flips before that are enforced by the ratchet in CI, not
by the deployed compiler.

**What the flip covers if trait objects are not built (Q9 answered no).** The
flip still covers all compiled-mode safe code. Open-set `any` sites that were
waiting for `dyn Trait` must be resolved before it: rewritten to an `enum`
where the set can be closed, otherwise moved behind a generic signature with
an `unsafe` body, each such move counted by the unsafe-`any` ratchet with a
stated reason. No site is exempted by leaving it on a baseline.

**Unresolved names** (lenient seed fallbacks that turn an unknown name, type or
import into `ANY`) warn first like everything else and go to error only as
part of the global flip, never earlier.

**What the first seed rejection showed.** Lane d29-c made the seed reject a
value of uninferable type reaching a typed use. On the library that newly
rejects **75 units (611 sites)**, in families including oauth, mqtt,
persistent collections, compression, dns and benchmark (lane d29-c finding).
That rule therefore ships as a **warning** first and follows the same
warn-to-error path, with one migration lane per family (plan S8-K).

**One exception to warn-first, for confirmation (Q12).** Disagreeing
`if`/`match` arms (lane d29-e) are an error from the start in the seed. The
argument is that the previous behaviour was a silent wrong value, and the
census found no such disagreement in existing source by grep. It is listed as
open because it is the only rule in this design that does not warn first.

## 13. Owner decisions

### 13.1 Decided

| # | Decision | Where |
|---|----------|-------|
| D1 | **Full monomorphization.** Per-type copies everywhere. Reverses the 2026-10-31 erased-body decision | §6 |
| D2 | **`any` is allowed in any `unsafe` block or function, and in script mode.** No separate `type_erasure` capability | §3.1 |
| D3 | **Source mode is set by file kind and config**, not by execution engine; the interpreter can run compiled-mode source | §3.2 |
| D4 | **Seed scope: syntactic checks only.** Full HM inference exists only in the self-hosted compiler | §11 |
| D5 | **Source-mode defaults and names.** `.shs` / `.sscript` are script by default, `.spl` is compiled. Precedence: file-header `@source_mode(...)`, then CLI `--source-mode`, then `simple.sdn` `[source_mode]`, then file kind | §3.2 |
| D6 | **Spec files (`*_spec.spl`) and examples are compiled mode.** The 618 explicit `any` uses under `test/` are in scope and migrate under plan S8-D | §3.2 |

### 13.2 Still open

- **Q8. File privacy.** 386 of 553 non-exported unannotated functions have no
  same-file caller (§5.2). Enforce file privacy, widen inference scope to the
  package, or treat those functions as must-annotate?
- **Q13. Seed items beyond syntactic checks** (§11.2): keep lane d29-c's
  type variables in the seed as a bounded bug fix, or reduce it; and must the
  seed monomorphize (plan S3-E), given it is bootstrap-only?
- **Q12. Errors from the start.** Confirm that disagreeing arms are an error
  in the seed without a warning phase (§12).
- **Q2.** Instance cap for implicit generics. Proposed 4.
- **Q3.** A private function with no call sites and an undetermined
  signature: error, or unused-code warning?
- **Q4.** `Option` joins: is a value arm with a `None` arm inferred as
  `Option<T>`?
- **Q9.** Trait objects (§8.2): commit to multi-implementor dynamic dispatch
  in the self-hosted compiler, and with which layout?
- **Q10.** Confirm the proposals listed at the end of §1 that go beyond the
  decision text.
- **Q11.** Build-time and code-size budget values for monomorphization
  (§6.3), once the first measurement exists.
