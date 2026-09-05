# backend/interpreter.spl `unresolved type: Symbol` at stage4 native-build (2026-08-11)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Symptom

Full bootstrap attempt (`/mnt/data/simple-option-config-f64-candidate/build/st4-final-fa1a`)
failed deterministically in phase4 (`stage4-native-build.log`, timestamp
`[2026-08-11T13:12:49Z]`):

```
error: focused native-build: HIR lowering error in src/compiler/backend/backend/interpreter.spl: unresolved type: Symbol
```

The same two-line error appears twice in the 8.5MB log (once per retry); no
further file:line detail is emitted by `focused native-build` (see
`src/app/cli/bootstrap_focused_native_build.spl:114`, `print "error: focused
native-build: {err}"` — it prints only `err`, which for an HIR lowering error
is rendered by `driver_hir_pipeline_lowering.spl:42-44` as `"HIR lowering
error in {name}: {err.message}"`, i.e. no span, because the no-span branch is
what's hit here). This happened AFTER phase3 (`hir_typecheck`) succeeded,
i.e. the module type-checks but a later HIR-lowering/monomorphize pass over
`interpreter.spl` cannot resolve a type literally named `Symbol`.

## Investigation

1. **Log still present** at the given path; extracted the two occurrences
   with `grep -n "unresolved type: Symbol"` (no additional context — the
   surrounding lines are `[hir-lower]` trace spam from `lower_expr:kind`).

2. **`interpreter.spl` itself has no bare `Symbol` type annotation** in the
   current tree (`grep -n ": *Symbol\b\|<Symbol>\|Symbol(" src/compiler/backend/backend/interpreter.spl`
   returns nothing). It imports `HirSymbol` explicitly
   (`use compiler.hir.hir_types.{HirSymbol, Effect}`, line 9) and uses that
   name everywhere, not `Symbol`. So the bare `Symbol` reference must come in
   transitively (via a type alias chain reachable from something
   `interpreter.spl` uses), which matches this failure mode exactly.

3. **This exact failure class is already extensively documented and fixed in
   the current tree**, in
   `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`:
   - Lines 792-849 (**TAL3**, dated 2026-08-04): fixes imported `type X = Y`
     aliases never being entered into the importing module's symbol table.
     The comment at lines 812-817 explicitly names this exact bug:
     > "Stage-3 hit this as `unresolved type: Symbol` in
     > `backend/interpreter.spl`, which imports `type Symbol = HirSymbol`
     > from `compiler.hir.hir_types`."
   - Lines 2473-2493 (**TAL2**, dated 2026-08-01): fixes the symmetric case
     where a module's OWN `type X = Y` alias is never registered in its own
     symbol table, again citing the `Symbol` failures by name (lines
     2479-2482): `type Symbol = HirSymbol` in `20.hir/hir_types.spl` and
     `type Symbol = text` in several `30.types/*` files.
   - Lines 177-204 (`hir_module_item_terminal_kind`, undated follow-up):
     fixes a related "phantom conflict" where `Symbol` got two different
     terminal-kind identities (`type_alias` vs the alias target's real kind,
     `struct`) and Stage 3 died comparing the entity against itself.

   `grep -rn "type Symbol" src/compiler/` confirms `Symbol` is indeed
   declared as an alias in multiple places: `20.hir/hir_types.spl` (`type
   Symbol = HirSymbol`, referenced by comment though not found by direct
   grep in current file listing — may have been renamed/refactored since;
   confirmed instead in) `25.traits/trait_method_resolution.spl:9`,
   `00.common/effects.spl:29`, and six files under `30.types/*` all declaring
   `type Symbol = text`.

4. **Monomorphizer / type-resolution table**: `grep -rln "monomorphiz"
   src/compiler/` locates the monomorphizer at
   `src/compiler/40.mono/monomorphize/{cache,tracker}.spl` and the frontend
   erasure/monomorphize helpers at
   `src/compiler/10.frontend/core/{monomorphize,type_erasure}.spl`. However,
   the actual `"unresolved type: {name}"` error text is emitted earlier, in
   the HIR-lowering type resolver at
   `src/compiler/20.hir/hir_lowering/types.spl:852` (recovered) and
   `types.spl:854` (hard error) — **not** in the monomorphizer itself. The
   monomorphizer never runs on this path; the failure is HIR-lowering-time
   name/type resolution failing to find `Symbol` in the module's symbol
   table, which is precisely what TAL2/TAL3 above fix (a symbol-table
   registration gap for locally-declared or imported type aliases), not a
   missing built-in-type match arm.

5. **Bug tracking docs**: `grep -rn "Symbol" doc/08_tracking/bug/` and
   `grep -rn "unresolved type" doc/08_tracking/bug/` return many hits, but
   none for this specific `backend/interpreter.spl` + monomorphize
   combination; the closest relevant history is embedded as in-code comments
   (TAL2/TAL3) rather than a standalone bug doc, which this file now
   supplies.

## Root cause (as far as determined)

This is very likely the same `Symbol` type-alias symbol-table registration
bug that TAL2/TAL3 already fixed (committed 2026-08-01 / 2026-08-04, both
well before the 2026-08-11 13:12 log timestamp). Current HEAD:

- Has TAL2 + TAL3 + the `hir_module_item_terminal_kind` fix in place.
- Has no direct bare `Symbol` type reference left in `interpreter.spl`.

The most consistent explanation for the log still showing this failure
**after** the fix landed in source is that stage4's native-build compiles
the source **using the stage3 compiler binary**, which was built earlier in
the bootstrap pipeline from a source snapshot that may predate these fixes
being baked into that binary. I.e. this looks like a **stale-stage-binary**
symptom, not a live bug in current HEAD's `.spl` sources — but this is a
hypothesis, not confirmed, since I did not (and was told not to) run a full
bootstrap to verify.

## Fix applied

**None.** No code change was made. The relevant `.spl` mechanism
(`module_lowering.spl` TAL2/TAL3/terminal-kind fixes) already exists in
current HEAD and appears to correctly cover the `type Symbol = HirSymbol` /
`type Symbol = text` alias cases described in the log. Making a further
change without being able to reproduce the failure against current HEAD
risks being speculative/over-engineered, which conflicts with the "minimal,
non-over-engineered fix" instruction. If a full bootstrap re-run (with a
freshly rebuilt stage3 from current HEAD) still reproduces `unresolved type:
Symbol` in `interpreter.spl`, that would falsify the stale-binary hypothesis
and point back at a real gap in TAL2/TAL3 (e.g. an alias chain longer than
one hop, or a third `type Symbol = ...` declaration not covered by the
single-target-non-alias predicate at `module_lowering.spl:843` /
`module_lowering.spl:199`).

## Minimal repro

Not created as a working repro. `focused native-build` triggers this HIR
lowering path via `src/app/cli/bootstrap_focused_native_build.spl`, which
requires an `--entry`/`--output`/`--source` invocation of the bootstrap
native-build path (not a plain `bin/simple run`/`compile` on a loose file).
Constructing and validating a standalone repro that reaches this exact
`focused native-build` code path was not attempted, in line with the
instruction not to fabricate a fix or spend bootstrap-scale machine time;
the in-tree TAL2/TAL3 comments already contain the authors' own minimal
repros for the underlying alias-registration mechanism (module_lowering.spl
lines 812-817 "Repro (probe m4)" and lines 2483-2484 "Minimal repro (probe
case D)").

## Verification tier

- Static/source-level investigation only (grep + read of
  `module_lowering.spl`, `interpreter.spl`, `types.spl`,
  `bootstrap_focused_native_build.spl`, `driver_hir_pipeline_lowering.spl`).
- **Full end-to-end bootstrap verification is NOT done and is still owed.**
  Specifically: rebuild stage3 from current HEAD, then re-run stage4
  `focused native-build` against `src/compiler/backend/backend/interpreter.spl`
  and confirm `unresolved type: Symbol` no longer appears. This was
  explicitly out of scope for this investigation (hours of machine time).

## Re-verification 2026-08-17 (fleet lane C, by CONTENT)

NOT REPRODUCED here, and the docs premise is partly stale.

- `grep "^type Symbol|^struct Symbol|^enum Symbol" src/compiler/20.hir/` is EMPTY —
  the alias the doc says should resolve `Symbol` is genuinely absent. That half stands.
- However `src/compiler/backend/backend/interpreter.spl` (528 lines) does NOT reference a
  bare `Symbol` type. Its import is `use compiler.hir.hir_types.{HirSymbol, Effect}` (line 9)
  and every other occurrence is `SymbolId` or `HirSymbol`. So the specific unresolved
  reference the title names is no longer present in this file.
- The failure was observed only at a **stage4 native-build**, which cannot be re-run in this
  session (a stage-3 bootstrap is holding the host at ~98% CPU and the lane is forbidden to
  touch `build/bootstrap/**`).

UNPROVEN: whether stage4 still fails. The in-file evidence suggests the cited symbol is gone,
but that is not the same as proving the build is green. Re-verify at the next full bootstrap.
