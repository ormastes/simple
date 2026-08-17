# Stage-3 self-host blocked by nil-receiver SIGILL in the caller of `lower_expr`

Date: 2026-08-05
Status: **STILL UNVERIFIED (2026-08-09, SIXTH campaign)** — a full bootstrap at
`origin/main` `94b861249c5` reproduces **blocker 15 bit-identically** (Stage 2
809/809 green, Stage 3 SIGSEGV exit 139, 0-byte log, `s.bytes()` bound to
`PointerSize.bytes`, si_addr `0x10`). The upstream typed HIR/MIR repair did NOT
close it — the hijack is in the suffix scan, ahead of any last-resort routing.
Probes again read `[mir-stmt-caller]` = 0, `[mir-garbage-expr]` = 0, nil-receiver
= 0, SIGILL/exit 132 = 0. See the "SIXTH campaign" section at the BOTTOM.
Prior status (FIFTH campaign): blockers 13 and 14
are now BOTH CLOSED. Stage 2 links clean from a pinned `origin/main`
`8ddd09f6d92` (809/809, 0 undefined refs, 0 call-to-zero sites) and Stage 3
reached execution for the first time. It dies of **blocker 15**: a wrong-callee
miscompile in the DRIVER'S SOURCE-LOADING phase (`bytes` suffix-matched to
`PointerSize.bytes`), root-caused in
`stage3_selfhost_segv_bare_leaf_bytes_hijacked_to_pointersize_bytes_2026-08-09.md`.
That is still BEFORE MIR: instrumented with both probes, `[mir-stmt-caller]` = 0,
`[mir-garbage-expr]` = 0, no SIGILL, no exit 132. **This fault site has still
never executed.** Prior status: **STILL UNVERIFIED (2026-08-09, FIFTH campaign)** — but the chain moved
substantially. Blocker 12 (the dead Stage-2 lexer) is now **fixed and verified
end-to-end**; Stage 3 lexes and parses its own entry file and reaches phase-1
module assembly, where it dies of a **SIGSEGV (exit 139)** in
`FlatAstBridge.flat_ast_to_module` — the **first Stage-3 fault site ever named
by a backtrace**, filed as
`stage3_selfhost_segv_in_flat_ast_to_module_2026-08-09.md`. That is blocker 14.
Blocker 13 sits in front of it: pristine `origin/main` cannot even **link**
Stage 2 (`stage2_native_build_link_undefined_method_symbols_2026-08-09.md`).
This SIGILL fault site has **still never executed** — `[mir-stmt-caller]` = 0,
`[mir-garbage-expr]` = 0, `field access on nil receiver` = 0, SIGILL/exit 132 =
0 across the whole campaign, because execution never reaches MIR. See the
"2026-08-09 (fifth campaign)" section at the BOTTOM. Prior status follows.

Prior status (2026-08-09, THIRD campaign) — blockers 9/10/11 are
all confirmed genuinely fixed on `origin/main` and the run got further than ever
before (Rust seed clean in 4m23s, **Stage 2 806/806 green**, Stage 3 launched),
but a **new blocker 12** stopped it before lexing even finished: the Stage-2
binary reads EVERY source file as empty and the parser loops forever. See the
"2026-08-09 (third campaign)" section at the BOTTOM. Prior status line follows.

Prior status (2026-08-09, second campaign): see the
"2026-08-09 (second campaign)" section at the BOTTOM of this file for the most
recent run. Short version: three more blockers (10, 11, and a **recurrence of
blocker 9**) were found and root-caused; Stage 2 went GREEN and Stage 3 ran to a
verdict, but again failed **closed** in phase 3 (HIR lowering) with **no SIGILL,
no nil-receiver fault, no exit 132 anywhere in the run**. The fault site has
STILL never executed.

Prior status line (2026-08-09, first campaign): not resolved, and not disproven
either. Rank 2 fix + Rank 4 probe remain landed-but-unexercised. A dedicated
instrumented full-bootstrap campaign on 2026-08-09 (three runs) got **closer
than any previous attempt** — Stage 2 now builds cleanly, 803/803 files, and
Stage 3 self-host ran to a **verdict for the first time** and failed closed at
phase 3 on a *different*, newly-identified blocker (blocker 9: implicit lambda
placeholders `_`/`_1` unsupported in pure-Simple HIR lowering) with **no SIGILL,
no `field access on nil receiver`, no exit 132 anywhere in the run**. That is
weak evidence this bug may already be gone, but not proof: phase 3 aborts before
the MIR lowering where this crash lives, so **the fault site has still never
executed** and the Rank-1..5 shortlist is neither confirmed nor refuted. See the
2026-08-09 section below.
Area: bootstrap / stage-3 self-host / 50.mir lowering

## 2026-08-09 (run 4, FOURTH campaign) — STILL UNVERIFIED; blocker 12 NOT cleared

A full instrumented bootstrap was run at `bfd9284618a` — the commit that claimed
to fix blocker 12 (the dead Stage-2 lexer) — specifically to clear it and finally
reach this fault site. **It did not.** Stage 2 rebuilt clean (**808 compiled, 0
cached, 0 failed**, 126,202 KB) and was admitted by the sanity gate, but Stage 3
died on its own entry file with the *same* dead-lexer signature. Blocker 12 is
**REOPENED, not fixed**:

```
[lexer_fatal] dead lexer: next_token() produced kind 0 (never a valid token kind)
for path 'src/app/cli/bootstrap_main.spl' at line 1 col 1; source length 21918.
```

Both probes were enabled (`SIMPLE_MIR_STMT_CALLER_DEBUG=1`,
`SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1`) and across the entire run produced
**`[mir-stmt-caller]` = 0, `garbage-expr` = 0, `field access on nil receiver` =
0, `SIGILL`/exit 132 = 0** — because Stage 3 never reached HIR or MIR lowering.

This run therefore adds **no** evidence for or against this bug. The earlier
"weak evidence it may already be gone" is neither strengthened nor weakened, the
fault site has **still never executed**, and Rank 1-5 remain unconfirmed and
unrefuted. Note this is now the fourth campaign to be stopped short of the fault
site by a *different* blocker.

Detail, including the revised root-cause hypothesis (a native-codegen
struct-in-module-array read, not a lexer defect) and a newly-found third defect
(the Stage-2 admission gate is **still fail-open**, because it invokes the
candidate with `--entry`, which delegates to the Rust runtime and never exercises
the candidate's own frontend):
`doc/08_tracking/bug/stage2_binary_lexer_reads_every_source_as_empty_infinite_parser_loop_2026-08-09.md`

## 2026-08-09 — closest approach yet; Stage 2 clean, Stage 3 reached, verdict still open

Assigned action: one clean, instrumented full bootstrap
(`SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
--output=<outside repo> --progress`) to find out whether Stage 3 clears the six
blockers fixed on 2026-08-08 and finally reaches this SIGILL. Three runs were
needed; the first two were stopped by new, unrelated obstacles.

### Blocker 7 (run 1) — three more unqualified enum-variant match arms

Run 1 cleared the Rust seed and reached Stage 2, which failed on 3 files:

- `src/compiler/30.types/type_infer/inference_expr.spl` — `case Str:`
- `src/compiler/70.backend/backend/cuda/ptx_builder.spl` — `case Bool:`
- `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl` — `case Struct:`

each `hir: Unsupported feature: 'case X:' is not a variant of the matched enum,
so it is an irrefutable BINDING ... makes every later arm unreachable`.

Same **family** as the "unqualified enum-variant match arms ×2" fixed on 08-08 —
that sweep did not enumerate its family, exactly the failure mode
`.claude/rules` warns about. Fixed by a *concurrent* session at `a6f0814f38d`
(confirmed ancestor of `origin/main`) while run 1 was still executing, so no fix
was needed from this session.

### Blocker 8 (run 2) — shared working copy contaminated by an in-flight untracked Rust file

Run 2 died even earlier, inside the Rust seed build:

```
error[E0308]: mismatched types
  --> compiler/src/interpreter_extern/counterpart.rs:94:28
     return Value::from(String::new());
                        ^^^^^^^^^^^^^ expected `Value`, found `String`
... error: could not compile `simple-compiler` (lib) due to 3 previous errors
```

`counterpart.rs` is **untracked** (`git status` → `??`) and absent from
`origin/main`: a new, not-yet-compiling file another concurrent session was
mid-flight on. Not a repo defect and not this session's to touch — but it means
*any* bootstrap launched from the shared `/home/ormastes/dev/pub/simple` working
copy measures that session's in-progress edits, not `origin/main`.

### Run 3 — clean checkout, Stage 2 GREEN, Stage 3 reached

Relaunched from a clean `origin/main` checkout
(`/home/ormastes/dev/simple-s3bisect`, verified clean apart from CRLF noise in
four `.cmd` files). Result:

```
Stage 2: seed → bootstrap_main.spl
  Build complete: 803 compiled, 0 cached, 0 failed
  Binary: .../stage2/x86_64-unknown-linux-gnu/simple (125204 KB)
  Time: 376.8s compile + 132.9s link = 509.7s total
  Stage 2: running bootstrap compiler sanity
Stage 3: stage2 → bootstrap_main.spl (self-host)
```

**Stage 2 is now fully green** — 803/803, zero failures, a 125 MB binary — and
Stage 3 self-host started and was progressing, its log carrying only benign
`[hir-field-type]` probe lines:

```
[hir-field-type] struct=CompiledUnit field=entry_point actual=2589120870 ...
[hir-field-type] struct=BackendError field=span  actual=2589120870 ...
```

### Blocker 9 (run 3, Stage 3) — implicit lambda placeholders `_` / `_1` unsupported in pure-Simple HIR lowering

Run 3's Stage 3 ran to a **verdict**, and it is **not this bug**. It failed
closed at phase 3 with a clean diagnosis, no crash:

```
[collect-all] 0.0 module(s) poisoned, 8 error(s) collected across 562 source(s) in phase 3 (HIR lowering).
[collect-all]   poisoned: src/compiler/70.backend/backend/lean_backend.spl
[collect-all]   poisoned: src/compiler/70.backend/backend/cuda_type_mapper.spl
[ERROR] phase 3 FAILED
error: in-process native-build: HIR lowering error in .../lean_backend.spl: unresolved name: _
error: in-process native-build: HIR lowering error in .../cuda_type_mapper.spl: unresolved name: _1
```

**Critically: no `runtime error: field access on nil receiver`, no SIGILL, no
exit 132 — anywhere in the run.** Stage 3 processed all 562 sources and stopped
on a diagnosed feature gap, exit 1.

The offending construct is the **implicit lambda-parameter shorthand**:

| file:line | expression |
|---|---|
| `cuda_type_mapper.spl:159` | `elements.enumerate().map("{self.map_type(_1.1)} _{_1.0}")` |
| `cuda_type_mapper.spl:177`, `:187` | `params.enumerate().map("{self.map_type(_1.1)} p{_1.0}")` |
| `lean_backend.spl:136` | `params.map("({_.0} : {_.1})")` |
| `lean_backend.spl:205` | `params.map(_.0)` |
| `lean_backend.spl:390` | `params.map(_.1)` |

`_` / `_1` as implicit lambda parameters are accepted by the **Rust seed** —
which is why Stage 2 (seed-compiled) builds all 803 files green — but the
**pure-Simple HIR lowering** in `src/compiler/20.hir` does not bind them, so it
reports `unresolved name: _`. This is a genuine seed-vs-pure-Simple feature gap,
not a miscompile, and it is the current Stage-3 blocker. It needs either
implicit-placeholder support in pure-Simple HIR lowering or explicit lambda
parameters at these 6 sites; it was **not** fixed here because it is a language
feature gap rather than a one-line defect, and blind-patching the call sites
would hide the gap rather than close it. It deserves its own bug entry.

#### Blocker 9 — RESOLVED 2026-08-09

Diagnosed and fixed. It was **not** "placeholders unsupported in pure-Simple":
the desugar pass `src/compiler/10.frontend/desugar/placeholder_lambda.spl` has
existed and been wired in since 2026-02-25. The real defect was a narrow
ordering edge case — placeholders inside a **string-template** argument were
invisible to the transform, because interpolation regions are sub-parsed only
*after* the module parse. `params.map(_.0)` always worked; only
`params.map("({_.0} : {_.1})")` leaked. Fixed with a second pass,
`transform_interpolated_placeholder_args()`, run from `core_frontend_parse()`
right after `expand_string_interpolations()`. Regression:
`test/01_unit/compiler/frontend/placeholder_lambda_interpolated_arg_spec.spl`
(4 RED → 0 RED). Full write-up:
`placeholder_lambda_missed_in_interpolated_string_call_arg_2026-08-09.md`.

Stage 3 has **not** yet been re-run past this point, so this SIGILL bug remains
UNVERIFIED; the next run is now unblocked from phase 3.

### Consequence for THIS bug

Nine blockers have now been logged in front of this SIGILL, and the fault site
has **still** never executed. The run that gets furthest — run 3 — shows Stage 3
failing *closed and cleanly*, with no nil-receiver fault of any kind. That is
weak evidence that this bug may already be gone (the Rank 2 fix did land), but
it is **not proof**: phase 3 aborts before the MIR lowering where this crash
lives, so the code path is still unexecuted. Status stays **UNVERIFIED**.

### What the next session should do (short and concrete)

Clear blocker 9 first, then re-run run 3's recipe from a **clean `origin/main`
checkout** and read the verdict:

- Stage 3 completes → **this bug is RESOLVED**; record log size + exit code.
- Stage 3 dies with `field access on nil receiver` / exit 132 → this bug is
  **finally reproduced**, and the Rank-1..5 shortlist below becomes actionable
  for the first time. Keep `SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1` set: this
  document's "REFUTED lead" section notes the `0x1800000007` decode was never
  measured with that probe enabled, so this is the run that would settle it.

### Standing recommendation

**Bootstrap verification of this bug must run from a pinned clean checkout of
`origin/main`, never from the shared working copy.** On a host carrying 6+
concurrent sessions the shared tree is not a definable revision; three of the
eight blockers logged against this bug turned out to be contamination or
already-fixed-elsewhere rather than real Stage-3 defects.

Related, now closed out: the sibling
`stage3_vacuous_binary_is_enum_discriminant_garbage_not_a_link_failure_2026-08-08.md`
reached a **RESOLVED** verdict on 2026-08-09 — its `[wildcard-arm]`/vacuous-binary
symptom was a real defect in a *stale pinned* stage2 binary, already fixed in the
current compiler, and was never the "scale artifact" it had been recorded as.
Run 3's 803/803 green Stage 2 independently confirms that. It is no longer an
obstacle to reaching this SIGILL.

## Symptom

Stage-3 build (`stage2-admitted/simple native-build ... src/app/cli/bootstrap_main.spl`)
dies with:

```
runtime error: field access on nil receiver
```

followed by `ud2` — **SIGILL, exit 132**, core dumped.

Signature of the run:

- Log is 32,534 lines / 1.5 MB, exit 132.
- **Last two lines of the log:**
  ```
  [mir-method-call] unresolved-owner-done method=push
  [mir-lower-expr] span-builder-written method=push id=7
  ```
- **Zero** enum-payload conflicts reported.
- **No** `phase 4 FAILED` line — the failure is not a diagnosed compile error, it is a
  hard fault inside the running stage-2 compiler.
- Provenance clean.

Blame assignment (keep this straight): stage 2 is compiled by the **Rust seed**
(`SIMPLE_NATIVE_BUILD_RUST=1` -> `native_build_rust_override`,
`src/compiler_rust/driver/src/main.rs:160`). `src/compiler/50.mir/**` is stage 2's
**payload**, not its compiler. The fault is in the *running stage-2 binary*, i.e. in
`.spl` compiler code **as compiled by the seed**, while it lowers the stage-3 sources.

## Established fact: the fault is in the CALLER of `lower_expr`

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1791` is a **bare `span_result`
return** — there is NO further code in `lower_expr` after the last probe line.

The full resolved probe chain before the fault:

- `expr_dispatch.spl:2913` `case MethodCall(receiver, method, args, resolution):`
  -> probe `method-dispatch-before` (`:2914`)
- `_MirLoweringExpr/method_calls_literals.spl:892` `lower_method_call` -> Unresolved arm
  -> `:2398 unresolved-receiver local=7`, `:2400 unresolved-owner-get`,
  `:2453 unresolved-owner-done`
- `:2457-2460` `if method == "push" and args.len() == 1: return
  self.lower_unresolved_array_push(...)` (defined at `method_calls_literals.spl:874`;
  emits `rt_array_push`, returns `push_recv`)
- back in `expr_dispatch.spl:1761..1791` (the `lower_expr` span wrapper):
  `:1781 impl-return`, `:1784 span-builder-read`, `:1787 span-restored-local`,
  `:1790 span-builder-written`
- `:1791` — bare `span_result` return, nothing after it.

**Therefore the nil deref is in whatever CONSUMED the last push's result, not in the
push lowering itself.** Every "it's the push path" reading of this log is wrong.

## Failing-region shape (measured from the log)

- The last **24 method calls are all `push argc=1`, consecutive, with nothing between
  them** — no `int:` literal probes, no nested `method-dispatch-before`. Each argument is
  a simple Var/text literal, not a call.
- `unresolved-receiver ... local=7` and `impl-return ... id=7` for **all 24** — a single
  receiver local reused. Source shape is `x = x.push(<simple>)` x24 with `x` = local 7.
- Method stream immediately before the 24: `... replace replace rfind substring split len
  trim starts_with starts_with starts_with push len trim` — a text/path-manipulation
  region.
- Receiver is `Unresolved` with `disc=1851930204` on every one of the 24.

## REFUTED lead — the `0x1800000007` garbage decode is NOT evidenced by this log

`grep -c garbage-expr-kind` = **0** and `grep -c disc-table` = **0** in the 32,534-line
log. Those probes are gated on `mir_lower_garbage_debug_enabled()`
(`expr_dispatch.spl:1726-1736`, `:1808`), which was **OFF** for this run.

The `0x1800000007` / "24 garbage children" decode therefore came from a **different
run/config** and must be **re-measured with `SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1`** before it
is used as evidence. (The coincidence of "24" is suggestive — the log tail is exactly 24
consecutive `push` lowerings — but it is NOT established here.)

## MEET TEST — `struct Block` vs `case Block(...)`: encodings meet, but ARTIFACT

Declarations of the terminal name `Block`, all in the stage-3 closure and all visible in
one scope (any 50.mir file does `use compiler.hir.hir_types.*` +
`use compiler.hir.hir_definitions.*`; `parser_types_expr` reaches 50.mir via the
`compiler.mir.mir_lowering_expr.*` wildcard surface):

| decl | file:line | shape |
|---|---|---|
| `struct Block` | `src/compiler/10.frontend/parser_types_expr.spl:587` | 2 fields (`stmts`, `span`) |
| `ExprKind.Block(Block)` | `src/compiler/10.frontend/parser_types_expr.spl:354` | arity 1 |
| `HirExprKind.Block(block)` | `src/compiler/20.hir/hir_definitions.spl:473` | arity 1 |
| `HirStmtKind.Block(block)` | `src/compiler/20.hir/hir_definitions.spl:699` | arity 1 |
| `ScopeKind.Block` | `src/compiler/20.hir/hir_types.spl:188` | arity 0 |

22 bare `case Block(x):` sites in the closure (incl.
`50.mir/_MirLoweringExpr/switch_operators_calls.spl:3240,3298,3506,3554,3582,3627,3643`,
`50.mir/mir_lowering_stmts.spl:890`,
`50.mir/synthetic_driver_registration.spl:148,171`).

**VERDICT: the encodings DO meet — and the hazard is still an ARTIFACT for THIS crash.**

1. **Arity.** Every enum `Block` variant is arity 0 or 1. A struct-positional reinterpret
   of a bare `case Block(x)` binds **field index 0 only**. It cannot produce the reported
   *index-1* object-header read. Index 1 is unreachable for this name.
2. **Both guards are live and symmetric.** Seed:
   `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:1241-1243`
   `struct_reinterpret_ok = enum_name=="_" && !subject_is_known_enum &&
   (subject_is_known_struct || !variant_of_some_enum())`.
   `.spl`: `src/compiler/20.hir/hir_lowering/expressions.spl:1210`
   `if enum_ == "" and rt_dict_contains(self.struct_field_order_by_name, variant) and not
   rt_dict_contains(self.enum_variant_names, variant)`.
   The `.spl` registries are populated symmetrically per module
   (`_Items/module_lowering.spl:1774-1779` enums vs `:1839-1852` structs/classes) and reset
   together in `hir_lowering/types.spl:265-267` via `begin_module` (called from
   `80.driver/driver_hir_pipeline_lowering.spl:126`). A module that declares neither gets
   neither, so the gate cannot fire asymmetrically for `Block`.

Residual, NOT closed: `try_register_local_struct_type`
(`src/compiler/20.hir/hir_lowering/statements.spl:60`) MERGES construction-site inference
into `struct_field_order_by_name` **without** a matching write to `enum_variant_names`.
That is the one asymmetric writer, and the only way the `.spl` gate can open for an
imported enum variant. See rank 3 below.

## Object-header-read hypothesis — full closure census

Closure: 684 files. **32 terminal names are declared BOTH as a struct/class AND as an enum
variant.** Cross-referenced against bare `case NAME(...)` patterns and their arity:

- Only **one** name has a **bare arity-2 `case`** pattern, which is what an *index-1*
  FieldAccess requires: **`Binding`**.
- `Template` (`70.backend/linker/obj_taker.spl:70`, struct/5 fields vs
  `ObjTakeResult.Template/2`, same file) is the only other arity-2 collision, and has **no**
  bare `case Template(a, b)` site.
- Everything else is arity 0 or 1 -> index 0 only.

There is **no `struct FieldAccess`** anywhere in `src/compiler`; the only `FieldAccess` is
`ObligationCause.FieldAccess(HirSymbol, text)` at `25.traits/trait_solver.spl:80`. The
lead's phrase "struct FieldAccess field at index 1" must be read as *the seed's HIR
`FieldAccess(subject, 1)` positional binding*, not a struct named `FieldAccess`.

## RANKED shortlist (nothing here is fixed; work is POSTPONED)

### Rank 1 — `Binding` struct/variant collision, arity 2, 10 sites in 50.mir (HIGH)

- struct: `src/compiler/00.common/di.spl:43`
  `struct Binding: factory: any; profile: CompilerProfile?; tags: [text]` (3 fields;
  closure entry #10, i.e. registered very early)
- variants: `src/compiler/10.frontend/parser_types_expr.spl:529` `PatternKind.Binding/2`;
  `src/compiler/20.hir/hir_definitions.spl:671` `HirPatternKind.Binding/2`
- bare uses, in the layer executing at crash time:
  `50.mir/_MirLoweringExpr/switch_operators_calls.spl:265, 298, 319, 1741, 1838, 1863,
  2042, 2056` and `50.mir/_MirLoweringExpr/expr_dispatch.spl:3472, 3585` — all of the form
  `case Binding(sym, _):`
- **Mechanism** A bare `case Binding(sym, _)` over a `HirPatternKind` subject that is
  reinterpreted as a struct-positional pattern binds `sym` = FieldAccess(subject, 0) and
  slot 1 = FieldAccess(subject, 1) = byte offset 8 of the object. On an `RtCoreEnum` that
  is bytes 8..15 = `(discriminant, enum_id)` = exactly `0x1800000007` (disc 24, enum_id 7).
  `sym` then holds a garbage `SymbolId`; `self.symbols.get_symbol_raw(sym.id)` answers nil
  and the next `.name`/`.kind` traps `field access on nil receiver` + `ud2` = exit 132.
  This is the ONLY name in the 684-file closure that can yield an index-1 header read.
- **Why it was ranked 1** only arity-2 bare-pattern collision out of the 32 struct/variant
  collisions; 10 bare `case Binding(sym, _)` sites inside 50.mir.
- **Cheapest experiment** Rename `di.spl:43` `struct Binding` -> `struct DiBinding`.
  Note: the "7 refs, all local to `di.spl`" claim in the working notes is **WRONG** — the
  name is re-exported twice, at `src/compiler/di.spl:9,16` (`pub use Binding`) and
  `src/compiler/00.common/__init__.spl:43`
  (`export use compiler.common.di.{DiContainer, Binding, ...}`), so the struct name is in
  scope far more widely than assumed. A rename is 9 sites, not 7. Non-invasive pre-check
  first: run the same repro with `SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1` and grep for
  `0x1800000007` / `bits=103079215111`.
- **Counter-evidence found while preparing the experiment (NOT yet run):** the seed's
  `variant_of_some_enum()` closure at `stmt_lowering.rs:1235-1240` scans
  `global_enum_defs` (populated for the native-project path at
  `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:689-690` via
  `set_global_enum_defs` + `register_global_enums`). `switch_operators_calls.spl` line 16
  does `use compiler.hir.hir_definitions.*`, so `HirPatternKind.Binding` IS in its import
  enum-defs -> `variant_of_some_enum()` is TRUE for `Binding` -> `struct_reinterpret_ok` is
  FALSE. **On that reading, the `Binding` collision does NOT open the gate, and the rename
  is predicted to be a no-op for this crash** — refuted by the SAME argument that made
  `Block` an artifact, with the arity distinction irrelevant because the gate never opens.
  This is a code reading, **UNVERIFIED by any build** — the rename experiment was prepared
  but not compiled (harness contended), so rank 1 stays open pending measurement.

### Rank 2 — cross-enum qualification inside one `match`, in the crashing layer (MEDIUM-HIGH)

- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1739` (also `:1836,
  :1861, :2044, :2053`)
- **Mechanism** `me emit_deep_subpattern(... pat: HirPattern ...)` does `match pat.kind:`
  — subject type `HirPatternKind` — but its arms are written `case PatternKind.Wildcard:`
  (the **parser** enum, `parser_types_expr.spl`) mixed with bare
  `case Binding(bind_sym, _)`, `case Literal(...)`, `case Enum(...)`. A qualified arm
  naming a *different* enum than the subject either never matches (arm silently dead, so
  the following bare `Binding` arm swallows a Wildcard) or resolves the owner to the wrong
  enum registry. `PatternKind` and `HirPatternKind` have different enum_ids.
- **Variant-set correspondence, checked:** all five sites use only `Wildcard`.
  `PatternKind` = Wildcard, Literal, Binding, Tuple, Array, Struct, Enum, Or, Guard, As,
  Range, Error. `HirPatternKind` = Wildcard, Literal, Binding, Tuple, Array, Struct, Enum,
  Or, Range, Error. Ordinals 0..7 coincide exactly; they DIVERGE from index 8 on
  (`PatternKind` has `Guard`/`As`, `HirPatternKind` does not). `Wildcard` is ordinal 0 in
  both — so if the lowering compares by ordinal only, the wrong-enum arm still matches by
  coincidence, and this is a **latent** hazard rather than the active fault. If it compares
  enum_id, the arm is dead. Which of the two happens is **UNVERIFIED**.
- **Cheapest experiment** Qualify every arm in those five `match` blocks as
  `HirPatternKind.*`. Purely local, no semantic change if the current code is correct — if
  it fixes the crash, the current code was not.

### Rank 3 — asymmetric writer into `struct_field_order_by_name` (MEDIUM)

- `src/compiler/20.hir/hir_lowering/statements.spl:60` (`try_register_local_struct_type`)
  vs the gate at `src/compiler/20.hir/hir_lowering/expressions.spl:1210`
- **Mechanism** Construction-site inference merges names into
  `struct_field_order_by_name` with **no** corresponding write to `enum_variant_names`.
  Every other writer pair is symmetric per module
  (`_Items/module_lowering.spl:1774-1779` vs `:1839-1852`, reset together at
  `hir_lowering/types.spl:265-267`). If a `Binding(...)`/`Block(...)`-shaped construction
  expression is lowered in a module that imports the enum but does not declare it, the gate
  at `:1210` opens and every bare `case <Name>(...)` in that module becomes a
  struct-positional pattern.
- Note both prescan passes read **module-local** maps only (`module.enums.keys()` /
  `module.structs.keys()`), so a 50.mir module that declares neither gets neither — which
  makes this construction-site writer the ONLY asymmetric path.
- **Cheapest experiment** One level-gated `eprint` when the `:1210` branch is TAKEN (name +
  module), re-run the existing repro. Zero risk, converts a scan-hypothesis into a measured
  yes/no. If the branch never fires, rank 3 and the whole struct-reinterpret family are
  artifacts.

### Rank 4 — the caller of `lower_expr`, not the push (MEDIUM, and always true)

- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1791`
- **Mechanism** `lower_expr` completed cleanly (`:1790` printed `id=7`). The nil deref is
  in whatever consumed the 24th push's result — a statement loop tail, a block value read
  (`HirBlock.has`/`.value` desugared-optional pair out of sync, the exact failure class
  already documented at `50.mir/synthetic_driver_registration.spl:60-72`), or the next
  sibling statement's `expr.span` push at `expr_dispatch.spl:1743-1745` / `:1754`.
- **Cheapest experiment** A level-gated probe (default OFF, env flag in the style of the
  existing `SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1`) bracketing `lower_stmt_impl` inside
  `lower_stmt` (`50.mir/mir_lowering_stmts.spl:396`), printing the statement discriminant
  (`mir_hir_stmt_kind_disc`) plus `stmt.span.file:line:col`. Two lines, and it names the
  crashing construct outright — which no current probe does.

### Rank 5 — `struct Block` / `case Block(...)` (LOW — reported as ARTIFACT)

- `src/compiler/10.frontend/parser_types_expr.spl:587`. Refuted for this crash by arity and
  by both live guards being symmetric (see the MEET TEST above). Still a real "one name,
  two terminal identities" instance worth a separate cleanup lane; it just cannot produce
  an index-1 header read.

## Instrumentation gap — file this regardless

MIR lowering emits **no module or function identity**. 32,534 probe lines and the failing
function still cannot be named: a best-window subsequence match of the last 130 method-name
tokens against all 684 closure files scored a **maximum of 14/130** (the lowering stream is
not a straight per-file walk). A single `eprint` of `module:function` at the top of
`lower_function` in 50.mir would have turned this into a five-minute localization.

## Status of the work

**POSTPONED by user decision on 2026-08-05.** No fix applied. The rank-1 rename, the
rank-2 arm qualification, and the rank-4 probe were prepared and then **reverted** — the
tree carries none of them. Nothing was compiled: the harness was contended (a
`bootstrap-from-scratch.sh` run reading `src/` from the LIVE working tree plus two sibling
lanes' native-builds), and no stage-2 rebuild was performed, so **no md5 change was
observed and nothing here is build-verified**. `bin/simple bug-add` was unavailable while
filing this (the deployed `bin/simple` is currently the Rust seed and reports
`error: file not found: bug-add`), so this entry follows the existing
`doc/08_tracking/bug/*.md` convention directly.

Working notes for this investigation lived in a session-local scratchpad
(`blocker10_findings.md`) which will not survive; the substance is reproduced above.

## 2026-08-08 update — Rank 2 fix + Rank 4 probe landed, still UNVERIFIED by a real repro

**What was done this session:**

1. **Rank 2 fix applied** (cross-enum qualification): all five
   `case PatternKind.Wildcard:` arms inside `emit_deep_subpattern` and
   `emit_enum_payload_deep` in
   `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (lines
   1750, 1847, 1872, 2069, 2078 at time of fix) are now qualified as
   `case HirPatternKind.Wildcard:`, matching the actual static type of the
   `match` subject (`pat.kind` / `pats[i].kind`, both `HirPatternKind`). This
   is a real correctness fix independent of whether it is THE cause of this
   crash: a bare/qualified-wrong-enum arm inside a `match` over a different
   enum is either dead (if the lowering compares by enum_id) or matches only
   by ordinal coincidence (if it compares by ordinal) — both are latent
   hazards per the doc's own Rank 2 analysis above.
2. **Rank 4 diagnostic probe landed**: `src/compiler/50.mir/mir_lowering_stmts.spl`
   gained `mir_stmt_caller_debug_enabled()` / `mir_stmt_caller_probe()`,
   gated on `SIMPLE_MIR_STMT_CALLER_DEBUG=1` (default OFF, mirrors the
   existing `SIMPLE_MIR_GARBAGE_EXPR_DEBUG` pattern), bracketing
   `lower_stmt_impl` inside `lower_stmt` and printing
   `[mir-stmt-caller] before/after disc=<N> file=<F> line=<L> col=<C>` for
   every statement. This is exactly the "Instrumentation gap" the doc calls
   out: no existing probe names the statement/module being lowered, so a
   32K-line log could not be localized.
3. **Regression spec added**: `test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl`
   gained two source-assertion `it` blocks — one asserting no
   `PatternKind.Wildcard` text remains in `switch_operators_calls.spl` and
   `HirPatternKind.Wildcard` does, one asserting the probe function/gate/
   call-sites exist. Both were RED before the fix (verified by reverting the
   two source files to their pre-fix content and re-running:
   `10 examples, 8 failures` including both new tests) and GREEN after
   (`10 examples, 6 failures`, the remaining 6 failures pre-existing and
   unrelated — see below).

**What could NOT be done, and why — be honest about this:**

- **No local Rust seed exists** (`src/compiler_rust/target/bootstrap/simple`
  is absent) and no in-progress `stage3` bootstrap output directory was found
  under `build/`. Reproducing the actual SIGILL requires a full
  `--full-bootstrap` run (cargo build the seed, build stage2, build stage3),
  which is multi-hour and — per `.claude/rules/bootstrap.md`'s current KNOWN
  BLOCKER note — stage3 was *already* failing earlier, at an unrelated
  `unresolved type: ByteOrder` error, before ever reaching the MIR-lowering
  region this bug is about. That earlier blocker is explicitly assigned to a
  different parallel agent per this task's scope constraints, so a from-
  scratch repro here would either (a) never reach this bug's failure site, or
  (b) collide with that agent's concurrent edits to the same bootstrap
  pipeline.
- **Consequently the Rank 2 fix and Rank 4 probe are landed but UNVERIFIED
  against the actual SIGILL.** The rename experiment's own "counter-evidence"
  section above (Rank 1) already showed that plausible-sounding fixes in this
  file can be no-ops once actually measured — the same caution applies here.
  This entry explicitly does NOT claim the SIGILL is fixed.
- **Shared-working-copy clobber during this session**: partway through, a
  concurrent session's reconcile silently reverted both source edits in the
  live working copy (and removed `.jj` entirely — `jj status` started
  reporting "There is no jj repo in \".\""). Edits were reapplied from a
  local backup and committed via `git` directly instead of `jj` because the
  jj working-copy state was gone. This is the same class of hazard already
  catalogued in `.claude/memory/ref_*` shared-WC entries; flagging it here
  since it means any interrupted lane in this file should re-diff against the
  committed blob, not trust an in-progress edit.

**Next step for whoever picks this up:** once a stage3 build can actually
reach the crashing region again (after the ByteOrder/Effect-facade blockers
ahead of it are cleared), re-run with
`SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1` and read the
`[mir-stmt-caller]` lines immediately preceding the fault — that names the
exact statement/file/line for the first time in this investigation.

**Status: NOT RESOLVED.** Two concrete, low-risk changes landed (one
correctness fix, one instrumentation gap closed) with a passing regression
spec, but the SIGILL itself remains unreproduced and unverified this session.
Treat prior POSTPONED status as superseded by this more specific one, not as
"fixed."

## 2026-08-08 update (later same day) — verification attempt run; outcome (c), unrelated NEW blocker, now earlier than Stage 3

**What was verified first (do not re-check):** the `ByteOrder` blocker
described as the thing standing in front of this bug is genuinely fixed at
`origin/main`. `git log --all --oneline | grep -i byteorder` finds
`9ad6aea9d34 test(compiler): add regression spec for ByteOrder
lazy-import-registration fix` and `9bb8727cbc3 fix(compiler): Stage3
self-host blockers - missing ByteOrder import + Effect facade collision`,
both ancestors of `origin/main` HEAD `663fce69eb3` (`git fetch origin main`
run first). Disk checked before the build: `df -h /` reported 119G free /
97% used on `/` — tight but sufficient; no `git prune`/`git gc` run, per
T11.

**Command run** (full env + command, per `.claude/rules/bootstrap.md` and
the task's Step 5), output redirected outside the repo tree per T12:

```
SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --output=/home/ormastes/dev/pub/simple-build-out/stage3-nilrecv-20260808 --progress
```

Started 13:59:30 UTC, finished 14:15:41 UTC (~16 minutes total — a real
`cargo` seed rebuild, `Finished \`bootstrap\` profile [optimized] target(s)
in 5m 53s`, so this was not a truncated/killed run; it ran to a real,
attributed compile-error termination, not a timeout or a signal).

**Outcome: (c) — an unrelated, NEW blocker, and it now fires at Stage 2, one
stage EARLIER than the previously-recorded Stage 3 ByteOrder/SIGILL chain.**
Stage 2 (`seed -> bootstrap_main.spl`) itself failed to native-build with 4
files rejected on the SAME diagnosis, none of them consistent with either
the ByteOrder import defect or the nil-receiver SIGILL this doc tracks:

```
FAILED FILES (4):
  - src/compiler/30.types/type_infer/inference_expr.spl : hir: Unsupported
    feature: `case Str:` is not a variant of the matched enum, so it is an
    irrefutable BINDING that matches every remaining value and makes every
    later arm (including `case _:`) unreachable. Use a qualified variant
    (`case Enum.Str:`), or a lowercase name if a binding was really
    intended.
  - src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl : same
    diagnosis, `case Str:`
  - src/compiler/70.backend/backend/cuda/ptx_builder.spl : same diagnosis,
    `case Bool:`
  - src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl : same
    diagnosis, `case Struct:`

Build failed: native-build aborted: 4 file(s) failed to compile
```

Full text: `stage2-native-build.log` under
`/home/ormastes/dev/pub/simple-build-out/stage3-nilrecv-20260808/logs/x86_64-unknown-linux-gnu/`
(build output, gitignored, not committed). The wrapper then correctly
refused Stage 3 and the seed-fallback CLI build:

```
warning: stage2 native-build failed (exit 1); Stage 3/full CLI unavailable
Stage 3: stage2 -> bootstrap_main.spl (self-host)
  warning: stage3 self-host failed (exit 1); Stage 4 unavailable
  warning: Stage 2 native-build capability failed; using seed for stage 4
warning: stage2 binary was not produced; Stage 3/full CLI unavailable
Stage 3 unavailable — no provenance-verified compiler for Stage 4
error: full CLI build requires a verified pure-Simple stage2/stage3 compiler; refusing seed fallback
```

**This run did NOT reach the MIR-lowering region this bug is about at
all** — it failed in the self-hosted HIR/type-checker's exhaustiveness
diagnostic during Stage 2, before Stage 3 (where the nil-receiver SIGILL
previously occurred) ever started for real. `SIMPLE_MIR_STMT_CALLER_DEBUG=1`
and `SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1` produced **zero** matching probe
lines in the 30-line captured log — there is no `[mir-stmt-caller]` or
`garbage-expr-kind` output to read, because MIR lowering of the stage-3
source tree was never reached. Do not misattribute this to Rank 2/Rank 4 of
this doc; it is a different failure mode (self-hosted exhaustiveness check
on a bare lowercase-looking `case Str:`/`case Bool:`/`case Struct:` arm
being treated as an irrefutable binding, not a variant match) in different
files, three of which (`30.types/type_infer/inference_expr.spl`,
`70.backend/backend/cuda/ptx_builder.spl`,
`70.backend/backend/vhdl/vhdl_design_catalog.spl`) are entirely outside this
task's `src/compiler/50.mir/**` scope, so no fix was attempted here. Only
`50.mir/_MirLoweringExpr/method_calls_literals.spl` is in-scope by path, but
fixing one of four co-failing files would not unblock the build (the other
three are out of scope), so no partial fix was applied either — a partial
fix here would be a wasted/misleading edit against a still-red Stage 2.

This is consequently also a **regression relative to the 2026-08-06 record**
in the ByteOrder doc, which reported Stage 2 passing cleanly before Stage 3
hit the ByteOrder error; Stage 2 no longer passes as of this run, on
`origin/main` `663fce69eb3` plus local worktree state at time of this run.
Whether this is a genuine new regression in `origin/main` or an artifact of
this specific working tree was not established here — that determination,
and the fix itself, is out of scope for this bug (which is specifically
about the Stage 3 nil-receiver SIGILL) and should be filed/tracked
separately if not already covered by an existing `case <Ident>:`
irrefutable-binding bug doc.

**Status: STILL NOT RESOLVED, and NOT RE-VERIFIABLE right now.** The Rank 2
fix and Rank 4 probe from the prior update remain landed and unreverted (not
re-diffed this pass, no reason to suspect otherwise), but this bug's actual
claim — whether the nil-receiver SIGILL still reproduces past the
now-fixed ByteOrder blocker — is **blocked by a different, earlier,
newly-observed Stage 2 failure** and was not exercised at all this run.
Next lane must clear the `case Str:`/`case Bool:`/`case Struct:`
irrefutable-binding Stage 2 failures (or confirm they're a working-tree
artifact and not present on a clean `origin/main` checkout) before this
bug's own verification can proceed.

## 2026-08-08 update (later still) — Stage-2 `case Str:`/`case Bool:`/`case Struct:`
family confirmed fixed at `origin/main` a6f0814f38dd90fa90a4f1f22dacc874cb9c43ac
(and the ByteOrder blocker at 9ad6aea9d349438e65a46edc9d6dc70e621f2f66), both
verified ancestors of `origin/main` via `git merge-base --is-ancestor` before
this run, plus their qualified forms (`HirTypeKind.Str`, `MirTypeKind.Bool`,
`SymbolKind.Struct | SymbolKind.Enum`) grepped directly out of
`git show origin/main:<path>` for all 4 previously-failing files. `df -h /`
showed 111G free / 98% used; no gc/prune run.

**Run 1** (`SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
--output=.../stage3-nilrecv-verify-20260808 --progress`, ~31 min, real cargo
rebuild since Rust seed sources had changed) still failed Stage 2, but with a
**new single-file** diagnosis, one sibling instance of the exact same
irrefutable-binding class the prior lane fixed in this same file:

```
src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl : hir:
Unsupported feature: `case Variable:` is not a variant of the matched enum...
```

Two bare `case Variable:` sites at lines 381 and 644 of
`src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl` (matching over
`symbol.kind` / `hir_symbol.kind`, both `SymbolKind`) — same shape as the
already-qualified `case SymbolKind.Struct | SymbolKind.Enum:` arms a few
lines above each site in the same two functions
(`vhdl_catalog_static_identity`, and the loop in
`vhdl_build_design_catalog_with_metadata`). This is a trivial, obvious,
same-family qualified-enum-variant fix, in the spirit of the task's
in-scope-fix allowance, so it was landed directly: both sites now read
`case SymbolKind.Variable:`.

**Run 2** (identical command, new `--output`, Rust seed unchanged so no
cargo rebuild, ~31 min) got **past** the `case Variable:` diagnosis — Stage 2
HIR/type-check now clears all 4+1 previously-known irrefutable-binding sites
— and progressed further than either prior lane today, into **codegen/link**,
where it hit a **new, different, unrelated blocker**:

```
Link failed. Objects kept at: .../stage3-nilrecv-verify-20260808-r2/stage3/
  x86_64-unknown-linux-gnu/native-objects-BWeUtY
Build failed: link failed: /usr/bin/ld:
  .../native-objects-BWeUtY/mod_518.o: in function
  `compiler__driver__driver__CompilerDriver.process_sdn':
  compiler__driver__driver:(.text.simple.1+0xd3): undefined reference to `run_fn'
clang++: error: linker command failed with exit code 1
```

This is a **linker-level missing-symbol defect** (`run_fn` referenced by
`CompilerDriver.process_sdn` in `compiler__driver__driver` but not emitted/
linked into the native-object set for Stage 2), not a `case`-arm exhaustiveness
diagnostic and not the MIR-lowering nil-receiver SIGILL this bug tracks. It is
**earlier in the pipeline than Stage 3** (it is Stage 2's own native-build
that fails to link), so the nil-receiver SIGILL region was again **not
reached** — `SIMPLE_MIR_STMT_CALLER_DEBUG=1`/`SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1`
produced no matching probe output because MIR lowering of the stage-3 source
tree never started. Per this task's scope, this is documented here as a
clearly-separate, out-of-scope blocker and NOT fixed — `run_fn` is a
driver/codegen linkage question, not a one-line qualified-variant typo, and
deserves its own investigation/bug entry rather than a guess fix under this
one.

**What changed in this session, concretely:**
- `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl`: two bare
  `case Variable:` arms qualified to `case SymbolKind.Variable:` (lines 381,
  644). Landed, verified by re-running the full bootstrap and observing the
  diagnosis disappear.
- This bug file, with this update.

**Status: STILL NOT RESOLVED.** The nil-receiver SIGILL claim remains
**unexercised** — three full-bootstrap attempts today (this session's two
plus the earlier one) have each been stopped by a different blocker strictly
before Stage 3's MIR-lowering region: ByteOrder (fixed), the
`case Str:`/`case Bool:`/`case Struct:` family (fixed) plus its
`case Variable:` sibling (fixed this pass), and now a Stage-2 link-time
undefined-reference to `run_fn`. Next lane must resolve (or file separately
and hand off) the `run_fn` link failure before this bug's actual claim can be
tested at all.

## 2026-08-09 (second campaign) — blockers 10, 11 and a RECURRENCE of blocker 9; SIGILL still unexercised

Assigned action: `git fetch origin main`, then ONE clean instrumented full
bootstrap, and determine the outcome. Four runs were needed. **Outcome: (3) — a
different, NEW blocker**, three of them in fact.

### Setup (per this file's own standing recommendation)

Run from a **clean pinned checkout**, never the shared working copy:
`/home/ormastes/dev/simple-s3bisect`, hard-reset to `origin/main`
`63ee79be7eee49f4fe59975b8d1e72426f7bcb59`, `git clean -xfd` (only CRLF noise in
2 `.bat` files remained). `git merge-base --is-ancestor 144fecf4280 origin/main`
-> YES, so the blocker-9 fix WAS present. `df -h /` 293G free before, 256G after;
no `git gc`/`prune` was run.

Command (all four runs), output outside any repo tree:

```
SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --output=/home/ormastes/dev/simple-build-out/stage3-nilrecv-20260809<N> --progress
```

### Runs

| run | result | exit |
|---|---|---|
| a | Rust seed E0308, `env_process.rs:1223` | 101 |
| b | seed link: 18 undefined `rt_counterpart_*` / `rt_packed_span_v1_*` | 101 |
| c | added `counterpart_worker_runtime.c` -> missing header; reverted that one file | 101 |
| d | seed OK, **Stage 2 GREEN**, Stage 3 started, then SIGTERM'd externally (exit 143, empty stage3 log) — harness interruption, not a product fault | 2 |
| e | relaunched fully detached (`setsid`), seed cached, **Stage 2 GREEN**, **Stage 3 ran to a verdict** | 2 |

Run e: START 07:53:22Z, END 08:15:52Z. Stage 3 process (pid 2617599) ran ~14 min
at ~98% CPU, RSS peaked around **53 GB**.

### Blockers 10 & 11 — the Rust seed does not build at `origin/main`

Both reproduce from a pristine `origin/main` checkout, so they block every full
bootstrap on `main`. Filed separately with full detail and fixes:
`rust_seed_build_broken_on_origin_main_2026-08-09.md`. Fixed locally in the
pinned checkout only (one `&`, and two C files added to the seed's
`build.rs` list) — deliberately NOT pushed, since they belong to two other
lanes.

### Blocker 9 RECURS — the fix was wired into only one of two parse paths

Stage 3 ran to a verdict and failed **closed**, with the byte-identical
diagnosis blocker 9 was supposed to have fixed:

```
[collect-all] 0.0 module(s) poisoned, 8 error(s) collected across 565 source(s) in phase 3 (HIR lowering).
[collect-all]   poisoned: src/compiler/70.backend/backend/lean_backend.spl
[collect-all]   poisoned: src/compiler/70.backend/backend/cuda_type_mapper.spl
[ERROR] phase 3 FAILED
error: ... HIR lowering error in .../lean_backend.spl: unresolved name: _        (x2)
error: ... HIR lowering error in .../cuda_type_mapper.spl: unresolved name: _1   (x6)
```

Root-caused this session: `transform_interpolated_placeholder_args()` is real,
present, and correctly wired — but only into `core_frontend_parse()`
(interpreter / core-compiler path). The driver/native-build path that Stage 3
actually uses goes `parse_full_frontend()` ->
`parse_and_build_module_scoped()`, which never calls
`expand_string_interpolations()` at all (that function has exactly ONE non-doc
call site in the tree). Full analysis, a 6-line seconds-to-run reproducer, the
suggested fix and its module-cycle constraint:
`placeholder_lambda_fix_missed_driver_native_build_parse_path_2026-08-09.md`.

### Consequence for THIS bug — unchanged, and be precise about it

Stage 3 aborts at **phase 3 (HIR lowering)**. This bug lives in **phase 4+ MIR
lowering**. Measured over run e's Stage 3 log:

- `field access on nil receiver` — **0 occurrences**
- `SIGILL` / `Illegal instruction` / exit 132 — **0**
- `[mir-stmt-caller]` probe lines — **0**
- `garbage-expr` probe lines — **0**

Both probes were enabled and both produced nothing, because MIR lowering of the
stage-3 sources was never reached. Eleven blockers have now been logged in front
of this SIGILL and **the fault site has still never executed**. The Rank-1..5
shortlist remains neither confirmed nor refuted, and the `0x1800000007` decode
still has not been re-measured with `SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1` against a
live fault.

**Status: STILL UNVERIFIED.** Not resolved, not disproven. Next lane: land the
driver-path placeholder fix (blocker 9's real fix), then re-run this exact
recipe. Note that blockers 10 and 11 must also be resolved upstream or
re-applied locally, or the seed will not build at all.

## 2026-08-09 (third campaign) — blockers 9/10/11 all CLEARED; new blocker 12 stops it at LEXING

Assigned action: re-run the instrumented full bootstrap now that host contention
had cleared, and reach a real verdict. **Outcome: (3) — a different, NEW
blocker.** The SIGILL fault site again never executed.

### Setup and host conditions (verified before committing to the run)

`git fetch origin main` → `f026cfcf510d12758048c1bad585ccd59d9764fa`.
Host at launch: **load 8.2** (down from 61.2 in the prior attempt), **1.4 T free**
on `/`, **108 G RAM available** (Stage 3's known ~53 G peak fits). Host stayed
healthy throughout — this run was **not** defeated by contention or disk.

Checkout used the lightweight recipe the previous lane staged but never ran:
`git archive <sha> | tar -x` into a fresh dir, then `git init` +
`.git/objects/info/alternates` → main repo's object store + `git update-ref HEAD
<sha>` + `git read-tree HEAD`. **It works and it is fast**: 112,095 files
extracted and a clean-status tree with real git metadata **in seconds**, versus
the stalls/1.5-files-per-second degradation that `git clone --shared` and
`git worktree add` hit under load. `git status` showed only the 10 pre-existing
CRLF-noise `.cmd`/`.bat` entries. Recommended for future bootstrap lanes.

### Blockers 9, 10, 11 — all confirmed genuinely fixed on origin/main

- **Blocker 10/11 (Rust seed):** seed + runtime built clean,
  `Finished \`bootstrap\` profile [optimized] target(s) in 4m 23s`. No E0308, no
  undefined `rt_counterpart_*`. No local patching was needed this time.
- **Blocker 9 (placeholder lambdas on the driver path):** the real fix is landed
  AND correctly wired. `expand_interpolated_placeholder_call_args()` exists at
  `src/compiler/10.frontend/core/string_interpolation_expand.spl:108` and is
  called from the flat-AST bridge at
  `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:942` — i.e. on
  `parse_full_frontend()` → `parse_and_build_module_scoped()`, the path Stage 3
  actually uses. `b9ed8aa45f2` and `144fecf4280` both verified ancestors of
  `origin/main`. **Stage 2 went 806/806 green**, and no `unresolved name: _` /
  `_1` diagnosis appeared anywhere in this run.

### Blocker 12 — Stage-2 binary lexes every file as empty; parser loops forever

Stage 2 reported `Build complete: 806 compiled, 0 cached, 0 failed`, linked a
126 MB binary, and **passed the `Stage 2: running bootstrap compiler sanity`
gate**. The binary it produced cannot lex anything:

```
$ printf 'fn main():\n    print("hi")\n' > probe_tiny.spl
$ .../stage2-admitted/simple native-build ... probe_tiny.spl
[parser_error] line 1:1: unexpected token in expression: Unknown(0) ''
[parser_error_ctx] path probe_tiny.spl kind 0 text ''
... forever
```

Stage 3's log after 11 minutes: **444,103,752 bytes / 6,299,344 lines**, and
`sort -u` over the whole file yields **2 distinct lines** — the pair above.
Process at 100% CPU with **32.4 GB RSS**, still climbing; killed deliberately
rather than allowed to ENOSPC/OOM the host.

Ruled out as a checkout artifact: entry file is 21,918 bytes with real content
and `git diff HEAD` on it is empty; the failing process's `/proc/<pid>/cwd` is
the checkout root and the file is readable at exactly the relative path passed;
and the Rust seed read those same 806 files fine while building Stage 2.

Filed with full evidence, the two stacked defects (dead lexer + parser error
recovery with no forward-progress guarantee), and the fail-open sanity gate:
`stage2_binary_lexer_reads_every_source_as_empty_infinite_parser_loop_2026-08-09.md`.

### Consequence for THIS bug — measured, not inferred

Stage 3 died during **lexing of its entry file**, which is upstream of phase 3
(HIR) and far upstream of phase 4+ (MIR) where this crash lives. Measured over
the full 444 MB Stage-3 log:

- `field access on nil receiver` — **0**
- `SIGILL` / `Illegal instruction` / exit 132 — **0**
- `[mir-stmt-caller]` probe lines — **0**
- `garbage-expr` probe lines — **0**

Both probes were enabled; both produced nothing, because MIR lowering was never
reached. **Twelve blockers have now been logged in front of this SIGILL and the
fault site has still never executed.** The Rank-1..5 shortlist remains neither
confirmed nor refuted, and the `0x1800000007` decode still has not been
re-measured against a live fault.

**Status: STILL UNVERIFIED.** Not resolved, not disproven. Next lane: fix
blocker 12 (the lexer, and independently the unbounded parser loop), then re-run
this exact recipe using the `git archive` + alternates checkout above.

## 2026-08-09 (fifth campaign) — closest approach yet; two blockers behind, fault site still not executed

One genuine complete bootstrap-from-scratch was run at `51115402161`
(`origin/main`, contains the lexer fix `d37b5e578b4`), from a clean
`git archive` + alternates checkout, both MIR probes enabled, with a
PID-tree-scoped watchdog sampling log growth and RSS every 15 s.

**Verdict for this bug: STILL UNVERIFIED.** Across the entire campaign —
run A, run B, and a standalone repro — the counts are:

| probe / signal | count |
|---|---|
| `[mir-stmt-caller]` | **0** |
| `[mir-garbage-expr]` | **0** |
| `field access on nil receiver` | **0** |
| SIGILL / exit 132 | **0** |

The reason is unchanged in kind but different in location: execution now stops
in **phase 1 (frontend module assembly)**, which is upstream of HIR and far
upstream of the `50.mir` lowering where this SIGILL lives. Rank 1-5 remain
neither confirmed nor refuted; the Rank 2 fix and Rank 4 probe remain landed but
unexercised.

### What actually happened (two new blockers, both characterised)

**Blocker 13 — pristine `origin/main` cannot link Stage 2.** Run A failed at the
link step in ~3 min, exit 1, with 9 undefined symbols, six of which are Simple
`text` methods emitted as *unmangled* bare external calls. Causally isolated by
a single-variable revert to `36673b6b6a3` ("guard imported method dispatch and
arrays"), which rewrote the LLVM backend's call-target selection. Filed:
`stage2_native_build_link_undefined_method_symbols_2026-08-09.md`. Until this is
fixed, **no Stage 3 result on a pristine tree is obtainable at all.**

**Blocker 14 — Stage 3 SIGSEGVs in `flat_ast_to_module`.** With `36673b6b6a3`
reverted, Stage 2 linked clean (809 compiled, 0 failed, 126,002 KB) and passed
both sanity and capability gates, and Stage 3 ran — then segfaulted, exit 139,
with a **0-byte** stage3 log. A core dump finally gave a real backtrace:

```
#0  compiler__frontend___FlatAstBridge__module_assembly__flat_ast_to_module ()
#1  ...__parse_and_build_module_scoped ()
#2  compiler.frontend.frontend.parse_full_frontend_with_scope ()
#3  ...CompilerDriver.parse_all_impl ()
#4  ...CompilerDriver.compile ()
#5  app.cli.bootstrap_main.run_native_build_bootstrap ()
```

Filed: `stage3_selfhost_segv_in_flat_ast_to_module_2026-08-09.md`. It reproduces
in a single command in under a second, which makes it far more tractable than
anything in front of it so far.

### Genuine progress, stated precisely

Blocker 12 is **gone**, and this is the first campaign that can prove it rather
than assume it: `flat_ast_to_module` is only reachable after the lexer and
parser have built a flat AST for `bootstrap_main.spl`, and `lexer_fatal` count
is 0 everywhere. Five campaigns have now been stopped short of this SIGILL by
five *different* blockers — but the stopping point has moved from "cannot lex
the first byte" to "parsed the whole entry file, died assembling the module",
which is materially closer to MIR.

### Note on the sanity gate

The gate reported `Stage 2: running bootstrap compiler sanity` and
`Stage 2 native-build capability passed` for a binary that segfaults on the very
next step. The documented `--entry` fail-open weakness was therefore treated as
real and the gate's verdict was **not** relied on; Stage 3's own behaviour was
observed directly, and the crash was independently reproduced outside the
wrapper. That decision is what produced the backtrace.

## 2026-08-09 (SIXTH campaign) — blocker 15 RECURS unchanged on current `origin/main`; fault site still never executed

One genuine complete `--full-bootstrap --deploy` was run from a pinned clean
`git archive` + alternates checkout of `origin/main`
`94b861249c5718dd3a58881f924ccb4b94036661` (`/home/ormastes/dev/s3camp6`,
output `/home/ormastes/dev/s3camp6-out`), both MIR probes enabled, with a
15-second watchdog on output size, free disk and >2 GB RSS. Host at launch:
load 8.7, 1.1 T free, 92 G RAM available. No safety trip; no log explosion.

**Outcome: (4) — blocker 15 recurs, bit-identically.**

| stage | result |
|---|---|
| Rust seed / runtime / backfill | clean, no local patching needed |
| **Stage 2** | **809 compiled, 0 cached, 0 failed**, 126,022 KB, 268.1 s |
| Stage-2 sanity + capability gate | "passed" — fail-open again, verdict not relied on |
| **Stage 3** | **SIGSEGV, exit 139**, `stage3-native-build.log` = **0 bytes** |

The admitted Stage-2 binary is md5-identical to the built one
(`ff6cf832d4d03d50b73362724fc2dedf`).

### Verdict for THIS bug — unchanged, and measured not inferred

| probe / signal | count across the whole run |
|---|---|
| `[mir-stmt-caller]` | **0** |
| `[mir-garbage-expr]` | **0** |
| `field access on nil receiver` | **0** |
| SIGILL / exit 132 | **0** |

Both probes were enabled and both produced nothing: Stage 3 dies in the
driver's **source-loading** phase, upstream of the frontend, of HIR, and far
upstream of the `50.mir` lowering where this SIGILL lives. **Fifteen blockers
have now been logged in front of this bug and the fault site has still never
executed.** Rank 1-5 remain neither confirmed nor refuted; the `0x1800000007`
decode still has not been re-measured against a live fault.

### The blocker, with a verified backtrace

Reproduced standalone from the recorded `stage3-command.transcript` in under a
second, and symbolized under gdb (binary retains `.symtab`, faulting
instruction disassembled and consistent with the fault address — no
nearest-symbol misattribution):

```
0x4d9617 in compiler.frontend.core.interpreter.hashmap.hm_hash_text ()
 #1 ..._driver_text_bucket_set_has  #2 CompilerDriver.load_sources_impl
 #3 CompilerDriver.compile          #4 run_native_build_bootstrap  #5 main
rax 0x8  rbx 0x8  si_addr 0x10
0x4d9609: call 0x800d80 <lib__common__target__PointerSize.bytes>
=> 0x4d9617: mov 0x8(%rax),%r15
```

`s.bytes()` on a `text` receiver is bound to `PointerSize.bytes`, which returns
the constant 8; `8 & ~7 = 8`, and the `.len()` field load reads `0x10`. 14 such
hijacked call sites in the binary; `check-no-call-zero.shs` PASSes (0 sites), so
this is a wrong-callee miscompile, not a call-to-zero.

**Important new fact:** this run's tree does **not** contain `8ddd09f6d92`'s
untyped last-resort routing — `origin/main` reverted it in favour of a typed
HIR/MIR repair. The hijack reproduces anyway, confirming this doc's prediction
that the defect lives in the **suffix scan**
(`src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2675-2746`), which
runs *before* any last-resort routing and is untouched by either the original
fix or its revert. Full re-measurement appended to
`stage3_selfhost_segv_bare_leaf_bytes_hijacked_to_pointersize_bytes_2026-08-09.md`.

No fix was attempted here: the defect is in the **Rust seed's LLVM backend**,
not in `.spl`, and any `.spl`-side avoidance of `text.bytes()` would be a
cover-up of a miscompile rather than a fix.

**Status: STILL UNVERIFIED.** Not resolved, not disproven. Next lane: land the
bare-leaf resolution fix in `functions.rs` (make the well-known-method table at
`:2497` reachable for dotless leaves, and/or make the suffix scan reject a
single *incompatible* candidate instead of accepting it), then re-run this exact
recipe.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: UNKNOWN — unverifiable by grep in principle, and still UNVERIFIED at runtime.**

This doc claims no fix, and records that the fault site has never executed
(`[mir-stmt-caller]` probe count 0, zero SIGILL/exit-132 observations). Its
blockers are upstream of MIR (a bare `bytes` suffix hijack in the driver's source
loader), so there is no fix pattern to grep for in
`_MirLoweringExpr/expr_dispatch.spl`. Reaching MIR at all needs stage3, which
per the governing fact was not available. Status left STILL UNVERIFIED.

## 2026-08-17 (W6) — 169 call-to-zero sites measured in the shipped self-hosted binaries

Directly relevant to this row's FIFTH-campaign line "Stage 2 links clean ...
0 undefined refs, **0 call-to-zero sites**". That claim does not hold for the
self-hosted binaries present in this checkout:

    objdump -d bootstrap/stage3/simple | grep -cE '\scall\s+0 <'   -> 169
    objdump -d bootstrap/stage2/simple | grep -cE '\scall\s+0 <'   -> 169

(both 3464072 bytes, mtime 2026-08-11 22:10; stripped; **not** the Rust seed.)
Each is a `call rel32` whose target is encoded as address 0 — a function that
was referenced but never emitted. Any one of them segfaults with `RIP = 0` the
moment control reaches it, producing exit 139 with no diagnostic and no
meaningful backtrace, which is exactly the signature this row and the three
`*_exit139_2026-08-14` / `*_sigsegv_2026_08_14` rows keep re-encountering under
different names. One is confirmed live and reproducible in under five minutes —
see the family write-up appended to
`doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md` (fixture, GDB
transcript, and the `objdump` of the faulting site at `0x66b0e7`).

Implication for this row specifically: exit 139 observed at a Stage-3 frontier
is **not** evidence that the frontier's function is defective. It is evidence
that some earlier compile emitted a call to a function it failed to lower. The
`lower_expr` nil-receiver SIGILL this row is named for remains, as the doc
already states across six campaigns, a fault site that has **never executed** —
no SIGILL, no exit 132, `[mir-stmt-caller]` = 0. Nothing in
`src/compiler/30.types/type_infer/inference_expr.spl` (this row's nominal owner
and a file W6 owns) was found defective, and no in-scope RED exists to quote, so
no spec and no source change were made here.

Status unchanged: **STILL UNVERIFIED**, and it should stay open. The
actionable lead is the 169 call-to-zero sites, not this fault site.
