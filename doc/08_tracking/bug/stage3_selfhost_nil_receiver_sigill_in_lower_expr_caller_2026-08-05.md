# Stage-3 self-host blocked by nil-receiver SIGILL in the caller of `lower_expr`

Date: 2026-08-05
Status: PARTIALLY ADDRESSED — Rank 2 fix landed + Rank 4 diagnostic probe landed,
NOT YET VERIFIED against a real stage3 SIGILL repro (see 2026-08-08 update at
bottom). Full-bootstrap re-run against the crashing input is still required to
close this out.
Area: bootstrap / stage-3 self-host / 50.mir lowering

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
