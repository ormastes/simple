# F1 — class/struct declaration-kind propagation: scoping + staged plan

Lane F1 of `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` (§2).
Scoping pass, 2026-08-09. **Outcome: plan only — no contained implementation
step exists that is verifiable under the current constraints.** Rationale below.

## 0. Contract (restated)

`struct` = value semantics; `class` = identity/reference semantics. Assigning a
class into a field copies the REFERENCE. `clone()` duplicates. Borrowed
exclusive access stays exclusive through aliases.

## 1. Where the kind is KNOWN, and where it is LOST

### 1a. Rust seed (`src/compiler_rust/**`) — kind known at the parser, dead from there on

| stage | file:line | state |
|---|---|---|
| AST field | `src/compiler_rust/parser/src/ast/nodes/definitions.rs:394` | `pub is_value_type: bool` — the kind slot exists |
| `struct` decl | `src/compiler_rust/parser/src/types_def/mod.rs:109` | `is_value_type: true` |
| `class` decl | `src/compiler_rust/parser/src/types_def/mod.rs:232` | `is_value_type: false` |
| HIR lowering | `src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:548` | **hardcodes `is_value_type: false`** — source value discarded |
| interpreter class table | `src/compiler_rust/compiler/src/interpreter/node_exec.rs:438` | **hardcodes `is_value_type: true`** for every struct-decl-derived `ClassDef` |
| newtype synth | `src/compiler_rust/compiler/src/interpreter/node_exec.rs:520` | hardcodes `false` |

**`is_value_type` has ZERO reads in the seed outside `parser/tests/` and
`type/tests/`.** It is written in four places and consulted nowhere. This is the
precise loss point: the parser knows, HIR/interp overwrite with a constant.

The mechanism that then produces the wrong behaviour:

- `src/compiler_rust/compiler/src/value.rs:1190-1193` —
  `Value::Object { class: String, fields: Arc<HashMap<String, Value>> }`.
  There is **no identity cell**; `Arc` is shared *until written*.
- `src/compiler_rust/compiler/src/interpreter/place.rs:132,177` —
  every field read-for-write and every field store goes through
  `Arc::make_mut(fields)`, i.e. **copy-on-write**. As soon as two holders exist
  (exactly the aliasing case the contract is about), the write clones and the
  alias is severed.

So the seed's "class-in-field is COPY" is not a missing branch — it is the
value representation. `Value::Object` has 210 non-vendor match/construct sites.

The earlier repo-wide finding (`ClassKind` / `StructKind` / `TypeKind::Struct` /
`TypeKind::Class` = 0 definitions) is confirmed and is the *downstream* half of
the same fact: since HIR carries no kind, MIR/codegen have no kind to branch on.

### 1b. Pure-Simple compiler (`src/compiler/**`) — kind known and carried end-to-end

| stage | file:line | state |
|---|---|---|
| parser | `10.frontend/core/_ParserDecls/fn_struct_decls.spl:839,1067-1068` | `parse_struct_decl(is_class)`; `class` ⇒ `decl_set_is_value_type(struct_d, 0)` |
| decl side-table | `10.frontend/core/_Ast/decl_nodes.spl:300,360,485-495` | `decl_is_value_type[]`, default `1` (struct) |
| flat-AST → HIR | `10.frontend/core/_Ast/module_state.spl:714`; `10.frontend/_FlatAstBridge/module_assembly.spl:140-148,359-360` | `is_value_type` reaches `CoreDecl` (`10.frontend/core/ast_types.spl:101`) and the HIR bridge splits class decls out |
| HIR | `70.backend/backend/interpreter.spl:217-251` | `ctx.module.structs` vs `ctx.module.classes` are **separate maps** |
| MIR | `50.mir/mir_lowering_types.spl:85` (`class_type_names: Dict<text, bool>`), populated `50.mir/_MirLowering/module_lowering.spl:220,1136-1140`, bootstrap path `50.mir/_MirLowering/bootstrap_globals.spl:567,592-594` | the kind is a first-class lowering input |
| MIR consumers | `50.mir/mir_lowering_stmts.spl:325` (nested field deep-copy skips classes), `:402` (`maybe_copy_struct_value` skips classes), `50.mir/_MirLowering/function_lowering.spl:319-320` (class param by-ref), `50.mir/_MirLoweringExpr/switch_operators_calls.spl:3135,4274` | **both halves already branch on the kind** |
| pure-Simple backend interp | `70.backend/backend/interpreter.spl:230,247-251` | class ⇒ `ctx.env.store.alloc(...)` + `Value.Object(handle)`; struct ⇒ inline `Value.Struct` — real reference semantics (Task #112) |
| pure-Simple frontend interp | `10.frontend/core/interpreter/eval_calls.spl:341-343,398-425` | `interp_struct_is_value_type` + `val_struct_deep_copy`, **applied at parameter binding only** |

**Answer to "can pure-Simple enforce the contract independently of the seed":
yes.** The kind survives parser → decl table → HIR → MIR → both backends, and
the class half is already enforced. Nothing in the pure-Simple pipeline depends
on the seed knowing the kind.

### 1c. The residual pure-Simple gap (mirror image of the seed's)

`val_struct_deep_copy` has exactly **one** call site
(`eval_calls.spl:343`, parameter binding). The frontend tree-walk interpreter
therefore never copies a struct on:

1. local binding from a place read — `val b = a` / `var b = a`
2. struct-literal field initialisation — `Outer(child: s)`
3. field store — `outer.child = s`
4. return of a place-read struct

Because it never copies, that engine gets **class right by accident** (identity
is preserved everywhere) and **struct wrong** in cases 1-4. The seed fails in the
opposite direction, and the pure-Simple MIR path already handles cases 1-3
correctly (`mir_lowering_stmts.spl:325,402`).

## 2. Staged plan

**S0 (done, this document).** Kind map for both pipelines, with the loss points
pinned to file:line.

**S1 — pure-Simple frontend interpreter: close the struct half.**
Extend the `interp_struct_is_value_type`-gated `val_struct_deep_copy` from the
one param-binding site to the four sites above (`eval_stmts.spl` binding + field
store, `eval_calls.spl` struct-literal construction and return).
This is **monotone**: the copy is gated on `is_value_type`, which is `false` for
every class decl and for every unregistered/builtin pseudo-struct, so adding
copies can only move struct behaviour toward the contract and **cannot** convert
the defect into the class-sibling. Smallest useful step in the whole lane.

**S2 — corpus reachability. DONE 2026-08-09 — see §6 for the driver, the proof
it is a different engine, and the measured baseline.** The corpus spec and probe
only reached the seed (`bin/simple run` = seed JIT;
`SIMPLE_EXECUTION_MODE=interpret` = seed tree-walk). The pure-Simple engine lane
is now a `run`-script driver over the frontend interpreter, as anticipated here.
S1 is unblocked.

**S3 — seed HIR carries the kind. DONE 2026-08-09 — see §7.** The loss point
named below was WRONG; §7a has the corrected one. Pure plumbing, no behaviour
change on its own — it only unblocks S4 and S5.

**S4 — seed value representation (the real cost).** Class instances need an
identity cell rather than `Arc<HashMap>` COW: either a store handle (mirroring
the pure-Simple backend's `env.store.alloc`, `interpreter.spl:247-251`) or a new
`Value::ClassRef` variant. Either touches the 210 `Value::Object` sites and the
COW writes at `place.rs:132,177`. **This is the deep blocker; nothing about it
is small.**

**S5 — seed JIT/native.** The JIT already gets class-in-field right and
struct-in-field wrong (aliases). With S3's kind in HIR, branch the aggregate
field-store lowering: copy for `is_value_type`, alias otherwise. Must land
*after* S3 and be gated by the corpus so it does not flip into the seed
interpreter's failure mode.

**S6 — SimpleOS / AOT parity**, then remove the workaround.

## 3. Why nothing was implemented in this pass

S1 is the only genuinely contained change, and under the current constraints it
is **not verifiable**: the engine it modifies cannot be reached by the existing
corpus without a rebuild/redeploy of `bin/simple` (explicitly forbidden here) or
a new `run`-script driver (that is S2, itself a non-trivial piece of work). A
change that cannot be sabotage-verified must not land — landing S1 blind would
put the tree in a worse state than the documented status quo. **S2 must precede
S1.**

Nothing in the seed is contained: the smallest seed change that moves any case
from wrong to right is S4, which rewrites the interpreter's value
representation.

## 4. What must be true to remove the `draw_ir_v3_native_writer` workaround

`src/lib/nogc_sync_mut/ui/draw_ir_v3_native_writer.spl:14-19` is load-bearing
until **both halves hold on the engine that writer actually executes on**:

1. class-in-field **aliases** (writes through an aliased class field are visible
   to every holder), and
2. struct-in-field **copies** (a struct stored into a field is a snapshot).

Today the writer runs on the seed. Under the seed interpreter half 1 fails
(COW severs the alias); under the seed JIT half 2 fails (structs alias). So
**both** the seed interpreter (S3+S4) and the seed JIT (S3+S5) must land, proven
by the corpus with A-E inverted and F-G still green on the same engine, before
the workaround can be deleted. Fixing only one engine is what converts the
defect into its sibling — that is the trap this lane exists to avoid.

## 5. Artifacts

- corpus: `test/01_unit/compiler/class_identity_corpus_spec.spl` (A-E pin the
  wrong copy behaviour with `TODO(class-identity-contract)`; F-G assert struct)
- probe: `test/fixtures/repro/compiler/class_identity/class_identity_corpus_probe.spl`
- repro: `test/fixtures/repro/compiler/class_identity/class_field_reference_semantics_repro.spl`
- bugs: `doc/08_tracking/bug/struct_field_aliases_under_jit_2026-08-08.md`,
  `doc/08_tracking/bug/class_field_reference_semantics_diverge_2026-08-06.md`

## 6. S2 result — pure-Simple engine lane (measured 2026-08-09)

### 6a. The driver, and its entry point

`scripts/check/class_identity_pure_simple_driver.spl`, run via
`scripts/check/check-class-identity-engine-matrix.shs`.

Entry point: **`core_jit_interpret(source, path, 999999)`**
(`10.frontend/core/interpreter/mod.spl:248`). It runs the pure-Simple pipeline
lex → parse → `eval_module` over the case source; the 999999 threshold means the
JIT never fires, so every answer comes from the pure-Simple **tree-walk**
evaluator (`eval_stmts.spl` / `eval_calls.spl` / `_EvalOps`). The seed still
hosts the driver process — it cannot not — but it does not decide the answers.

Two things had to be discovered empirically rather than assumed:

1. **The interpreter package's `__init__.spl` exports a hand-maintained SUBSET
   of its own symbols**, so a driver importing only the barrel dies with `E1002`
   on the first unexported internal (`jit_init_with_backend`, then
   `_core_run_pipeline`, then `eval_init`, then `mono_cache_init`, …). The fix
   is to import every module of `10.frontend/core/**` by path. The same trap is
   already documented in `__init__.spl` for `eval_int_method`.
2. **The entry file must live OUTSIDE the repo tree.** Byte-identical driver,
   same env, same binary: from `scripts/check/` it dies with
   `error: semantic: variable 'cache_initialized' not found` — a module-level
   `var` in `10.frontend/core/interpreter/value.spl`, i.e. the imported
   package's globals were never initialised — and from `/tmp` it runs all ten
   cases to completion. **The entry file's location decides whether imported
   modules' globals get initialised.** That is a real defect, not a quirk; the
   `.shs` copies the driver out as a workaround and says so.

### 6b. Proof it is NOT the seed (positive discriminator)

Case A (class in a trait-typed field) reads **REF** on this lane and
**COPY(n=100)** under `SIMPLE_EXECUTION_MODE=interpret` on the same fixture —
the seed interpreter's documented failure. Case B is *answered* (rc=-1, no
verdict) where the seed JIT *kills the process*. So the pure lane matches
neither seed column, and a silent fallback to either would be visible in the
output. `check-class-identity-engine-matrix.shs` fails with exit 1 if the pure
column ever equals the seed-interpreter column on every case.

### 6c. Measured baseline — three engines, one corpus

Fixtures: `test/fixtures/repro/compiler/class_identity/cases/*.spl`, one case per
file so a failure cannot hide the cases after it (the single-file probe stops at
the first error, which is how the earlier run mis-read case C).

| case | site | contract | seed JIT | seed interp | **pure-Simple frontend** |
|---|---|---|---|---|---|
| A class in trait field | field init | REF | REF | COPY(100) | **REF** ✅ |
| B class in optional field | field init | REF | *process dies* | COPY(110) | **rc=-1, silent** ⚠️ |
| C class in array elem[1] | array slot | REF | REF | COPY(130) | **REF** ✅ |
| D class param → field | field store | REF | REF | COPY(140) | **REF** ✅ |
| E class returned | return | REF | REF | COPY(90) | **REF** ✅ |
| F struct literal field init | S1 site 2 | VAL | ALIAS(151) | VAL | **ALIAS** ❌ |
| G struct local binding | S1 site 1 | VAL | ALIAS(11) | VAL | **ALIAS** ❌ |
| H struct field store | S1 site 3 | VAL | ALIAS(21) | VAL | **ALIAS** ❌ |
| I struct returned | S1 site 4 | VAL | ALIAS(31) | VAL | **ALIAS** ❌ |
| J struct param binding | *existing copy site* | VAL | ALIAS(99) | VAL | **VAL** ✅ |

### 6d. Reality vs the plan's prediction

**Matched, on every case §1c predicted.** Class semantics are correct on all
four measurable class cases (A, C, D, E); struct semantics are wrong on exactly
the four sites named in §1c (F, G, H, I); and J — the one site that already
calls `val_struct_deep_copy` (`eval_calls.spl:343`) — is correct, which is the
positive control proving the `is_value_type` gate is live rather than dead. The
mirror-image characterisation of the two pipelines is confirmed by measurement,
not just by reading.

Three things the prediction did not cover:

- **B fails silently on the pure-Simple engine.** `core_jit_interpret` returns
  -1 and no verdict and no error text is emitted, so an optional class field is
  neither answered nor diagnosed. Every engine now mishandles B in a different
  way (seed JIT: fatal; seed interp: wrong answer; pure-Simple: silent failure).
  B is therefore NOT covered by S1 and needs its own diagnosis.
- **Seed JIT gets J wrong too** — `ALIAS(99)`, i.e. even parameter binding
  aliases a struct there. S5 must cover parameter binding, not only field
  stores.
- **The ALIAS branch prints `ALIAS(n={got})` literally** on the pure-Simple
  engine: text interpolation is not expanded in that arm. Cosmetic here (the
  VAL/ALIAS verdict is still unambiguous) but it is a second interpreter defect
  found in passing, and it means output from this engine must not be parsed for
  interpolated values.

### 6e. What this does and does not license

S1 is now measurable: it must flip F, G, H, I from ALIAS to VAL on the
pure-Simple column while leaving A, C, D, E at REF and J at VAL. Nothing here
justifies touching a `TODO(class-identity-contract)` marker — those pin SEED
behaviour and no seed behaviour changed in this pass. This lane delivered a
measurement capability and a baseline; it changed no compiler semantics.

## 7. S3 result — the seed now carries the kind (measured 2026-08-09)

### 7a. §1a's loss point was wrong; here is the real one

§1a named `hir/lower/module_lowering/module_pass.rs:548` and
`interpreter/node_exec.rs:438` / `:520` as the places that "hardcode" the kind
and discard the parser's value. **All three are correct as written**, and
changing any of them would have introduced a defect rather than fixed one:

| site | what it actually is | correct value |
|---|---|---|
| `module_pass.rs:548` | synthesizes a `ClassDef` for an **`actor`** declaration | `false` — actors are message-passing identity types |
| `node_exec.rs:438` | AST-interpreter registering a `Node::Struct(StructDef)` | `true` — this arm only ever sees `struct` |
| `node_exec.rs:520` | AST-interpreter synthesizing a **newtype** wrapper | `false` |

`Node::Struct(StructDef)` and `Node::Class(ClassDef)` are separate AST variants
(`parser/src/ast/nodes/core.rs:18,20`), so nothing in the interpreter path ever
had to guess. The parser was already right at
`parser/src/types_def/mod.rs:109` (`struct … with Mixin` routed through
`ClassDef` but kept `is_value_type: true`) and `:232` (`class`).

**The actual loss point is `hir/lower/type_registration.rs`.** `register_class`
and `register_struct` BOTH end in `HirType::Struct { … }` — there is no
`HirType::Class` in the seed's HIR at all — and neither function recorded which
declaration it came from. That, not the interpreter, is where the kind died and
why MIR/codegen had nothing to branch on.

§1a's other claim also no longer holds: **`is_value_type` is no longer read
zero times.** `interpreter_call/core/arg_binding.rs:122,428` and
`interpreter_call/core/function_exec.rs:953` (`is_value_type_struct`) read it
today. That is the positive control explaining why the seed interpreter gets
case J (struct parameter binding) right while the seed JIT gets it wrong.

### 7b. What S3 landed

A side table carrying the declaration kind, deliberately NOT a change to
`HirType` (that would touch every `HirType::Struct` match site in the seed):

- `hir/types/module.rs` — `HirModule::type_value_kinds: HashMap<String, bool>`
  plus `type_is_value_kind(name) -> Option<bool>`.
- `hir/lower/type_registration.rs` — `register_struct` records `true` (before
  the `@packed` bitfield early return, so a packed struct is not left
  kindless); `register_class` records `c.is_value_type` (NOT a constant `false`
  — a `struct … with Mixin` arrives through this function as a value type).
- `mir/function.rs` — `MirModule::type_value_kinds` + `type_is_value_kind`.
- `mir/lower/lowering_core.rs` — copies the table HIR → MIR alongside
  `local_globals`.

**`None` means UNKNOWN, never "value type".** Builtins, imported-but-unlowered
aggregates and synthesized pseudo-structs get no entry, and every consumer must
make `None` a no-op. A `None`-defaults-to-true consumer would start copying
identity types and would convert the class defect into its struct sibling —
precisely the trap §4 exists to avoid.

Mirrors `class_type_names` in the pure-Simple lowering
(`src/compiler/50.mir/mir_lowering_types.spl:85`).

### 7c. Oracle and sabotage test

`src/compiler_rust/compiler/tests/class_identity_kind_propagation.rs`, 4 tests:
struct/class distinct in HIR, absent name reads `None`, kind survives MIR
lowering, actor is an identity type.

Sabotage cycle run in full (isolated worktree, `cargo test --profile
bootstrap`): **green 4/4 → replace `c.is_value_type` with a constant `true` in
`register_class` → 3/4 FAILED → restore → green 4/4.** The one test that stayed
green under sabotage is the `None`-means-unknown test, which does not depend on
that line. The oracle measures.

### 7d. A–K matrix: unchanged, as designed

S3 is pure plumbing, so the corpus MUST read identically before and after. It
does — 11/11 cases on both seed engines, before and after, via
`scripts/check/check-class-identity-seed-matrix.shs` (new; the seed-only fast
lane, since the three-engine matrix's pure-Simple column costs tens of minutes
per run and S3/S4/S5 change only the seed).

| case | seedJIT before → after | seedINTERP before → after |
|---|---|---|
| A class in trait field | REF → REF | COPY(100) → COPY(100) |
| B class in optional field | *SIGILL, then* `runtime error: field access on nil receiver` → same | COPY(110) → COPY(110) |
| C class in array elem | REF → REF | COPY(130) → COPY(130) |
| D class param → field | REF → REF | COPY(140) → COPY(140) |
| E class returned | REF → REF | COPY(90) → COPY(90) |
| F struct literal field init | ALIAS(151) → ALIAS(151) | VAL → VAL |
| G struct local binding | ALIAS(11) → ALIAS(11) | VAL → VAL |
| H struct field store | ALIAS(21) → ALIAS(21) | VAL → VAL |
| I struct returned | ALIAS(31) → ALIAS(31) | VAL → VAL |
| J struct param binding | ALIAS(99) → ALIAS(99) | VAL → VAL |
| K struct method returned | ALIAS(71) → ALIAS(71) | VAL → VAL |

Provenance: both columns come from a seed built in an isolated worktree at
`HEAD` + the four S3 files. The **deployed `bin/simple` is itself a Rust seed**
(it prints the bootstrap-seed banner), so this table is SEED-ONLY and makes no
seed-vs-self-hosted claim; the cross-engine claim lives in §6 and needs the
pure-Simple driver lane, not this one.

### 7e. S4 and S5 remain blocked — with sharper reasons

**S5 is bigger than §2 assumed.** §2 described S5 as "branch the aggregate
field-store lowering". There is nothing to branch: **the seed MIR has no
aggregate-copy operation at all.** A sweep of `src/compiler_rust/**` for
`struct_copy` / `copy_struct` / `deep_copy` / `StructCopy` finds only
`runtime/src/value/core.rs:426` `Value::deep_copy`, used by
`runtime/src/executor.rs` for parallel-executor data, and nothing anywhere in
`mir/` or `codegen/`. So S5 must FIRST introduce a copy primitive (a
`MirInst`, its `inst_effects`/`inst_helpers` arms, and a lowering in **both**
the cranelift and LLVM backends) and only then insert it at the six sites the
corpus names (F–K: literal field init, local binding, field store, free-function
return, parameter binding, method return). The kind S3 landed is the input that
work needs; it is no longer the missing piece.

**S4 is unchanged and still the deep blocker.** `Value::Object { class,
fields: Arc<HashMap<String, Value>> }` (`compiler/src/value.rs:1190-1193`) has
no identity cell, and every field read-for-write and store goes through
`Arc::make_mut` (`interpreter/place.rs:132,177`), i.e. copy-on-write. That COW
is what makes the seed interpreter's A–E read COPY, and it is also what makes
its F–K read VAL by accident. Giving classes an identity cell touches the 210
`Value::Object` sites. `Deref`-based tricks do not rescue it: a shared-mutable
backing (`RwLock`/`RefCell`) cannot hand out a plain `&HashMap` the way the
existing sites require.

**Order still matters.** Fixing one seed engine and not the other converts the
defect into its sibling, so the `draw_ir_v3_native_writer` workaround
(§4) stays load-bearing until S4 AND S5 both land.

### 7f. S4 scoping pass, measured 2026-08-09 — not attempted, here is why and what's next

This pass tried to determine whether S4 is bounded. It is not, but the "~210
sites" estimate from §7e was a grep count of `Value::Object` matches, not a
measured blast radius. Here is the measured version.

**What COW means here, precisely.** There is no existing copy-on-write
*mechanism* separate from the problem — `Arc::make_mut` on
`fields: Arc<HashMap<String, Value>>` IS the COW, and it is *correct by
accident* for structs and *wrong by the same accident* for classes:
`Arc::make_mut` mutates in place only when the `Arc`'s strong count is 1; if a
struct value was aliased by a `let b = a`, the alias holds a second strong
reference, so the first mutation through either name clones the `HashMap`
first — exactly value semantics, confirmed correct and pinned by a regression
test at `interpreter/node_exec.rs:1973` (`field_assignment_cow_protects_struct_local_alias`,
added for bug #187). For a class the same clone-on-shared-mutate is the
defect: two aliases of the same object are supposed to see each other's
writes, and COW severs that the instant either alias mutates.

**The runtime already knows which kind a value is, per-value.**
`Value::Object` carries `class: String` directly, and
`interpreter_call/core/function_exec.rs:953`
(`fn is_value_type_struct(v, classes) -> bool`) already resolves it against
`ClassDef::is_value_type` — used today at one call site (`:1065`, parameter
binding). So the *classification* is not the blocker; S3 (§7b) already solved
that at the HIR/MIR layer and it is trivially available to the interpreter at
runtime too. The blocker is that classification cannot fix mutation-through-
alias at the *call site*, because `Arc<HashMap>` provides no legal way to get a
`&mut HashMap` out of a shared (`strong_count > 1`) `Arc` without either
cloning (the current, wrong-for-classes behavior) or `unsafe` (not on the
table). Fixing it requires interior mutability in the storage itself
(`Arc<RefCell<HashMap>>` or `Arc<Mutex<HashMap>>`), which is a representation
change, not a call-site change.

**Measured blast radius of that representation change** (ripgrep over
`compiler/src`, 2026-08-09, `Value::Object` is defined once,
`compiler/src/value.rs:1190`):

| category | count | why it matters |
|---|---|---|
| `Value::Object` pattern matches (destructuring) | 190 (41 files) | every one is a candidate exhaustiveness point if a new variant is added |
| direct `fields.get(` / `.iter(` / `.contains_key(` / `.keys(` / `.values(` calls | 168 | these rely on `Arc<HashMap>`'s **transparent `Deref`**; `RefCell`/`Mutex` do not implement it, so each becomes `fields.borrow().get(...)` (or `.lock()`) — a mechanical but real per-site edit |
| genuine **write-through** sites (`Arc::make_mut(fields)` / `Arc::make_mut(&mut fields)` and the two `inner_fields`/`root_fields` variants) | **23** (7 files: `interpreter/place.rs`, `interpreter/node_exec.rs`, `interpreter/expr/calls.rs`, `interpreter_call/core/lambda.rs`, `interpreter_call/core/function_exec.rs`, `interpreter_call/bdd.rs`, `interpreter_helpers/patterns.rs`) | this subset is small and already correct for structs — it is not the wall |

The wall is the 168+190 (overlapping, not summed) **read** sites, not the 23
write sites. And critically: **the struct/class split does not shrink this
set.** `Value::Object` is one representation for both kinds — the same
`to_text`, equality, pattern-match-binding, JSON/BDD helper, and generic
field-lookup code paths execute for a struct instance and a class instance
identically, because nothing before this pass ever needed them to differ. So
"how many of the 210 are struct-only vs class-only" has a real answer: **zero
are staticaly scoped to one kind** — every read site is reachable from both,
and the per-value `class: String` + `is_value_type_struct` check only tells
you which kind you're holding at runtime, it does not let you skip touching
the site when converting the storage type.

**Why this pass did not attempt it anyway.** A `RefCell`/`Mutex` swap is not
just mechanical churn — it introduces a genuinely new runtime hazard the
current code cannot have: reentrant `borrow_mut()` panics (e.g. a class
method that reads `self.field` while a caller already holds a `borrow_mut()`
on the same object further up the call stack — routine in OOP code with
nested method calls). Landing that across ~200 sites in one pass, sight
unseen per site, is exactly the "broad, risky change" this task was told not
to attempt in one pass.

**Smallest safe next step (not this pass).** Do not convert
`Value::Object`'s existing `fields` field type in place — that forces the
struct path (200 already-correct read sites) to eat 100% of the risk for a
fix that only classes need. Instead, add a **new, additive** variant used only
for newly-constructed class instances, so struct code paths are untouched:

1. `Value::ClassInstance { class: String, fields: Arc<RefCell<HashMap<String, Value>>>, id: u64 }`
   in `value.rs`, next to `Object` — `id` is a monotonic counter for identity
   comparison/debug, not load-bearing for the COW fix itself.
2. Route construction through `is_value_type_struct`'s existing classification
   at every `Value::Object` *construction* site (literal eval, constructor
   call) — the S3-landed `type_value_kinds`/`ClassDef::is_value_type` gate
   already exists for exactly this branch; grep-count the construction sites
   first (expected: a handful, in `node_exec.rs` and `interpreter_call/`, not
   200 — construction is far rarer than read).
3. Add `Value::ClassInstance` arms only where the corpus (A–E, `test/fixtures/repro/compiler/class_identity/cases/*.spl`)
   actually exercises them: `place.rs` (`step_mut`/`store_last`, 2 sites, using
   `.borrow_mut()` instead of `Arc::make_mut`), the `FieldAccess` read path,
   method-call receiver resolution, and `to_text`/equality/debug formatting.
   Every OTHER site either doesn't need a new arm (generic array/dict/pattern
   machinery that never inspects `Value::Object`'s internals) or the Rust
   compiler's non-exhaustive-match error names it for you — that error list
   IS the real, code-verified blast radius, superior to any grep estimate,
   and should be captured as the artifact of step 1-2 before doing step 3 for
   real.
4. Run `scripts/check/check-class-identity-seed-matrix.shs` after step 3;
   expect A, C, D, E to flip `COPY(n)` → `REF` on seedINTERP while F–K and the
   seedJIT column stay byte-identical to §7d's table (no struct regression, no
   change on the JIT engine at all — S4 only touches the interpreter).

This additive-variant approach was not implemented in this pass (only
investigated) because step 3's exact site list is only known after step 2 is
built and the compiler's own exhaustiveness errors enumerate it — that is
follow-on work, not a same-pass extension of this scoping.

## 8. S6 result — the fourth copy site (parameter binding, measured 2026-08-09)

S5 landed three of the four sites the corpus needs (struct-literal field init,
local binding, field store — plus return/method-return as a side effect of the
local-binding gate) but left case J (`j_struct_param_binding`) unchanged: an
incoming struct-typed parameter is caller-owned storage, and nothing copied it
before the callee's body ran.

**The fix.** `MirLowerer::copy_param_if_value_type` (new,
`mir/lower/lowering_core.rs`), called once per parameter at the top of
`lower_function` — after `begin_function` (needs an active block) and before
the body is lowered (every in-body read of the parameter must see the copy).
It gates on the exact same `type_value_kinds` check `copy_if_value_type` uses
(`Some(true)` only), then reads the parameter's own local slot
(`lower_local_expr`), copies it via the S5 `AggregateCopy` primitive, and
stores the copy back into that same slot — so every subsequent `LocalAddr`
read of the parameter inside the function body sees the private copy, not the
caller's original. Reuses `copy_if_value_type` rather than duplicating its
field-list / byte-size checks.

**Oracle.** Three new tests in
`compiler/tests/class_identity_kind_propagation.rs`
(`struct_parameter_binding_emits_aggregate_copy`,
`class_parameter_binding_never_emits_aggregate_copy`,
`struct_and_class_parameter_binding_diverge_in_emitted_mir`), mirroring S5's
pattern for the other three sites. Sabotage-verified: short-circuiting
`copy_param_if_value_type` to an unconditional `return Ok(())` takes the suite
from 11/11 to 9/11 — exactly the two gate-dependent parameter tests fail, with
an explicit assertion message, not silence. Restoring the real gate returns
11/11.

**Seed-only A–K matrix** (`scripts/check/check-class-identity-seed-matrix.shs`),
before → after, on a from-source-rebuilt seed (binary provenance printed by the
script itself — this is NOT the deployed `bin/simple`):

```
case                          seedJIT (before → after)        seedINTERP (before → after)
a_class_trait_field           REF → REF                       COPY(n=100) → COPY(n=100)
b_class_optional_field        (nil-field runtime error, unchanged, both engines)
c_class_array_element         REF → REF                       COPY(n=130) → COPY(n=130)
d_class_param_to_field        REF → REF                       COPY(n=140) → COPY(n=140)
e_class_returned               REF → REF                       COPY(n=90)  → COPY(n=90)
f_struct_literal_field_init    VAL → VAL                       VAL → VAL
g_struct_local_binding         VAL → VAL                       VAL → VAL
h_struct_field_store           VAL → VAL                       VAL → VAL
i_struct_returned              VAL → VAL                       VAL → VAL
j_struct_param_binding         ALIAS(n=99) → VAL                VAL → VAL   (unchanged)
k_struct_method_returned       VAL → VAL                       VAL → VAL
```

Only `j_struct_param_binding`'s seedJIT cell moved, and it moved the direction
S6 targets (ALIAS→VAL). Every class case (A/C/D/E) and every seedINTERP
reading is byte-for-byte identical before and after — the gate did not convert
the class defect into its struct sibling, matching the invariant S3 and S5
established.

**Status after S6.** All six corpus sites S5's plan named for the JIT
(literal field init, local binding, field store, free-function return,
parameter binding, method return) are now closed on the seed JIT. S4 (the
seed interpreter's class-identity gap, `Arc<HashMap>` COW) remains the
deep blocker described in §7e and is untouched by this change — S6 is scoped
to the JIT-side parameter-binding gap S5's commit message called out, nothing
more.
