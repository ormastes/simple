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

**S3 — seed HIR carries the kind.** Stop hardcoding at
`module_pass.rs:548` and `node_exec.rs:438`; propagate
`StructDef/ClassDef::is_value_type` from `types_def/mod.rs:109/232`. Pure
plumbing, no behaviour change on its own — it only unblocks S4.

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
