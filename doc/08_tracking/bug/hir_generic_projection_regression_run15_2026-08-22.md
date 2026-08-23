# Stage-1 HIR regression: generic-projection lanes take fatals 48 -> 3716 (run15)

- **Status:** REVERTED on main; underlying defect REFILED (below), not fixed.
- **Filed:** 2026-08-22
- **Reverted commits:** `d481f15e1ac` (generic-argument projection), `86787968989` (generic-callable signature projection + `Function` arm)
- **Kept:** `4a40c00c8e5`, `9f11967564b` (array-of-tuple / pointer / union), `22a0424891a` (payload-origin miss memo)

## Measurement

All counts on the `[hir-fatal]` basis, from full stage-1 builds.

| tree | fatals | poisoned modules |
|---|---|---|
| run14 `75a66d615bd` | 258 | 56 |
| post19 (array-of-tuple only, §27 row for `4a40c00c8e5`) | **48** | **9** |
| run15 `b99deb6ae58` | **3716** | **437** |

Non-fatal recovered `unresolved type` occurrences went the OTHER way, 234,210 ->
7,231, which is why the lanes looked like progress on a raw grep. Recorded so
the next reader is not misled: the two numbers move in opposite directions and
only the fatal count gates the build.

## What is new in run15, and what is not

Every one of the 3716 fatal names is a user-declared type. `Option`, `Result`
and `Dict` are **not** among them — they resolve; their ARGUMENTS do not.

| name | fatals | shape in the owner |
|---|---|---|
| HirContractBlock | 501 | `verification_contract: HirContractBlock?` — `50.mir/mir_instruction_graph.spl:208` |
| SymbolId | 444 | `owner_symbol: SymbolId?` — `module_callable_types.spl:88` |
| MirFunction | 171 | field/optional positions in the same graph module |
| ModuleSurfaceExportOrigin | 159 | optional/dict positions |
| HirType | 144 | `hir_types.{SymbolId, HirType}` import at graph:3 |
| Span | 141 | `span: Span?` — `mir_instruction_graph.spl:14` |
| LayoutPhase | 84 | `layout_phase: LayoutPhase?` — `mir_instruction_graph.spl:177` |

`mir_instruction_graph.spl` **imports** all four of Span, HirType,
HirContractBlock and LayoutPhase (lines 3-5) and declares none of them. The
victim, `50.mir/hwir/bit_vector_constant.spl`, has **no `use` line at all** and
reports exactly those four names.

## Mechanism (static, from the diffs and the tree)

`imported_surface_projected_named_args` now recurses into each generic
ARGUMENT and calls
`self.symbols.lookup_qualified_type_raw(imported_module_name, arg_name)`.
`imported_module_name` is the module the importer NAMED — here a package facade
reached by sibling auto-import / glob re-export — not the module that DECLARES
the argument type. The lookup misses; `imported_surface_type` then falls through
to `self.lower_type`, which resolves in the **importer's** scope and emits a
hard, non-recovered `unresolved type: X` against a module that never names X.

The profile line for the victim shows the miss rate directly:
`qtype=4725/3781 miss` — 80% of qualified type lookups miss.

`86787968989` compounds it: removing the `callable.type_params.len() > 0` bail
plus adding the `Function` arm feeds the whole generated visitor/codec
population through the same broken lookup.

**Widening projection did not create the resolution gap. It made an existing
one fatal at scale.** The gap is the same owner-scope/re-export-hop resolution
already filed as `hir_unresolved_type_owner_missing_import_2026-08-22.md`.

## Why revert rather than fix forward

The correct fix is owner-scope resolution that follows the re-export hop to the
DECLARING module — NOT restoring the drop, which is the original silent defect
(`d481f15e1ac` proved the drop silently erased `Dict<text,MirType>` to
`Dict<any,any>`). That is a resolver change whose only oracle is a ~5 h stage-1
build, so it could not be landed and validated in this window. 437 poisoned
modules must not sit on main overnight, so the lanes are reverted and the defect
stays open.

## Honest limits of this investigation

- **No unit fixture reproduces it.** `test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl` was written for this record and is GREEN on both sides. A four-module `export use` facade hop is not sufficient; the real trigger involves package-sibling auto-import and `use ...*` globs. Kept as a non-vacuous guard, labelled as not-a-reproducer in its own docstring.
- **Per-commit attribution is static, not measured.** Two targeted `native-build --entry-closure` probes were attempted; neither reached the HIR phase for the victim module (rc=1 in 178 s, 0 `[hir-fatal]`). The split above rests on the diffs plus the shape of the failing names (all `X?`/generic-argument positions), not on a differential build.
- **Pre-existing red, stepped over and recorded:** `imported_surface_callable_projection_spec.spl` is 2 of 3 RED at pristine `c05e7052843` AND byte-identical after the revert. Not caused by this change.

## Next lane

Fix `lookup_qualified_type_raw` (or its caller) to resolve a projected argument
in the module that DECLARES it, following the owner's import table and
re-export hops, then re-land `d481f15e1ac` and `86787968989` behind a measured
stage-1 census. Do not re-land either without that census.

## Corroboration from the generic-callable lane (2026-08-22, post-revert)

The `86787968989` lane owner independently produced attribution evidence that
**agrees with the mechanism above and shifts weight off their own commit**:

1. **Full `test/01_unit/compiler/hir` sweep, A/B, same seed.** origin/main
   76 PASS / 48 FAIL; origin/main minus `86787968989` 75 PASS / 48 FAIL. The
   FAIL sets are **byte-identical** — 0 newly red, 0 newly green. (Logs
   `/mnt/fast/gc1/hirsweep.log`, `/mnt/fast/gc1b/hirsweep_baseline.log`.)
2. **Construct census of run15's new names.** Occurrences in a GENERIC callable
   signature / as a generic ARGUMENT / as `T?`:
   HirContractBlock 0 / 0 / 6; Span 0 / 0 / 58;
   ModuleSurfaceExportOrigin 0 / 2 / 0; SymbolId 0 / 94 / 61;
   MirFunction 2 / 27 / 12; HirType 1 / 53 / 100.
   The three names with **zero** generic-callable exposure include the largest
   population. HirContractBlock's only cross-module signature use is
   NON-generic: `lean_backend.spl:528`
   `fn function_contract_from_hir(name: text, contract: HirContractBlock?, param_aliases: [(text, text)]) -> Result<FunctionContract, CompileError>`
   — Optional + array-of-tuple + `Result<..>` args, no type params at all.
3. A synthetic A/B on that exact shape (plus bare `T?`, `Result<A,B>`,
   `Dict<text,T>`, control) produced 0 errors at origin/main — the shape alone
   does not reproduce without real-module context.

This is the same conclusion this record reached statically from the opposite
direction: the fatal population is the **generic-ARGUMENT / Optional** surface
(`d481f15e1ac`), not the generic-callable surface. Their honest limit stands and
is repeated here: no harness reproduced the regression, so this is "no exposure
and no spec-level effect", **not** an exoneration.

**Both stay reverted regardless.** `86787968989`'s `Function` arm and
`bound_type_params` threading are entangled with `d481f15e1ac`'s argument
recursion (they share the parameter and the recursion sites), so the pair could
not be separated cleanly in a revert, and neither can be re-landed on evidence
from unit specs — the failing population is invisible to them by construction
(48 of 124 hir specs are red on BOTH sides). Re-land condition is unchanged and
applies to each commit independently: a measured stage-1 `[hir-fatal]` census at
or below post19's 48 / 9.

## RE-LANDED (2026-08-22): the generic-callable half, alone — was held, now at origin

**Status changed.** This section first recorded the change as prepared-and-held.
It has since been re-landed ALONE, at origin/main `b7e474b6cd8` (code commit
`8f08930460d`, docs `b7e474b6cd8`), superseding the held branch
`reland-generic-callable` / `8e70a394659`. The generic-ARGUMENT half
(`d481f15e1ac`) is UNTOUCHED by that push and remains reverted, so it is still
free to be re-landed and measured on its own afterwards.

Re-verified at ORIGIN after the push, not from anyone's working copy
(`git show origin/main:<file>`):

| check | result |
|---|---|
| `bound_type_params` in `module_callable_types.spl` | 17 |
| `imported_surface_projected_named_args` (the sibling's symbol) | **0** |
| `imported_generic_argument_projection_spec.spl` | absent |
| `check-type-walk-constructor-parity.shs` | absent |
| `imported_generic_callable_signature_projection_spec.spl` | present |

So whatever the next stage-1 run measures is attributable to the
generic-CALLABLE half alone — which is the entire reason for splitting the pair.

Precision note on the guard, since the re-land reported it as "reduced to
`if not callable.has_return_type:` — 1": that is true of
`declared_imported_surface_callable_type` (line 373), the path that matters
here. A `type_params.len() > 0` bail still stands at line 143, in the SIBLING
function `declared_surface_callable_type`, which handles the module's OWN
callables rather than imported ones. Not a contradiction, but the two must not
be conflated by a future grep.

The original held-branch verification, kept for history:

- branch `reland-generic-callable` in `/mnt/data/worktrees/generic-callable-1`,
  tip `89d772f90b5`, code commit `8e70a394659`.

Isolation verified here rather than taken on assertion, at `8e70a394659`:

| claim | check | result |
|---|---|---|
| based on current origin/main | `git merge-base --is-ancestor a50b92999d2 89d772f90b5` | YES, merge-base is `a50b92999d2` exactly |
| does not drag in `d481f15e1ac` | `git grep -c imported_surface_projected_named_args 8e70a394659 -- src/` | **0 occurrences** |
| sibling spec / parity gate not restored | `git ls-tree -r --name-only` for `check-type-walk-constructor-parity` and `imported_generic_argument_projection_spec` | **0** |
| touches only its own surface | `--stat` | 5 files: `parser_types_expr.spl`, `module_callable_types.spl`, `module_import_registration.spl`, its own spec, this record |

This is the direction that untangles the entanglement recorded above: the
generic-callable half applies alone on the post-revert tree, so if a later run
regresses it can be reverted with per-commit evidence instead of as a pair.

**The re-land condition is unchanged and is a census, not a review:** a measured
stage-1 `[hir-fatal]` count at or below post19's 48 / 9. Unit specs do not
qualify — 48 of 124 hir specs are red on both sides of the regression, and a
purpose-built facade-hop fixture is green on both.

`/mnt/fast/gc1-baseline` has been deleted by its owner; it was stale after the
revert. Rebuild any future baseline from `ec13c319250` or later.

## run16 — the revert worked, and what run16 does NOT establish

run16 (both halves reverted, i.e. the tree this record's revert produced)
measured **15 HIR fatals / 21 poisoned modules**, honest basis 16 distinct error
lines, rc=1 at 4326 s. run15's `Option` 1547 / `Result` 962 / `Dict` 889 flood
is fully undone and `MirType` stays gone (was 180 at run14). Against run15's
3716 / 437 that is the revert doing exactly what it was landed to do.

**Two caveats, stated before anyone quotes these numbers:**

1. **Counting basis.** run16's 21 poisoned against post19's 9 may be a
   counting-basis difference rather than a real delta; post19 must be
   re-derived on run16's basis before that gap is called a regression.
   Comparing two censuses computed different ways is precisely what produced
   the false MirType clearance prediction in follow-up (b) of
   `hir_unresolved_type_owner_missing_import_2026-08-22.md`.
2. **run16 does not attribute run15.** It removed both halves at once, so it
   cannot say which one caused the regression. The run AFTER the isolated
   generic-callable re-land is the decider. If fatals go materially above
   run16's 15 / 21, the generic-callable half owns it.

## RESOLVED 2026-08-23 — the generic-ARGUMENT half, re-landed with the missing materialization half

**Status:** the defect this record kept open is fixed at `350dd6bff2b` (spec `9f2719af402`). `d481f15e1ac`'s mechanism
is re-landed, but only alongside the change without which it could never have
worked.

### What the previous analysis got wrong

This record's "Next lane" said: *fix `lookup_qualified_type_raw` (or its caller)
to resolve a projected argument in the module that DECLARES it, following the
owner's import table and re-export hops.* That framing assumed the argument WAS
bound somewhere and projection was merely looking in the wrong place. It was not
bound anywhere.

`materialize_imported_callable_type_dependencies_inner` dispatches on the
pre-captured scalar head name. For `Dict<text, HirModule>` that head is `Dict`, a
builtin, so the branch materialized nothing and returned **without ever walking
the arguments** — `parser_type_named_dependencies`, which does recurse
`Named -> args` correctly, is only called in the `else` that a captured scalar
head skips. So no re-export hop needed following: there was no binding at either
end of it.

That fully explains the 50x. `d481f15e1ac` made projection recurse into arguments
that materialization had bound nothing for, so **every** argument missed the
owner-scope lookup and fell through to `lower_type` in the importer's scope.
3716 fatals is what "every generic argument in the tree misses" looks like — the
number was not a mystery, it was arithmetic.

### Reproduced at unit scale, which this record said was impossible

This record's honest-limits section states *"No unit fixture reproduces it"* and
the re-land condition was *"a measured stage-1 `[hir-fatal]` census"*, on the
grounds that the only oracle was a ~5 h build. That is now superseded:
`test/01_unit/compiler/hir/imported_generic_head_argument_owner_scope_spec.spl`
reproduces the flood in seconds. Applying only the projection half to a
three-module fixture yields `unresolved type: Payload` — the exact shape — at
2 of 6 passing.

Why the earlier fixtures missed it, stated so the lesson survives: they asserted
on ERROR COUNTS. The `imported_surface_type_projected` miss path drops generic
arguments **silently**, so an error-count fixture is green pre-fix. The
discriminating assertion is argument IDENTITY — pristine projects
`Dict<text, Payload>` as `Dict<any, any>`, and the spec asserts the value
argument is still `Named`.

The stage-1 census was run anyway, as a differential A/B (both sides built from
the same base with the same seed) rather than against a historical number — which
also answers caveat 1 of the run16 section, since both sides are computed on an
identical basis by construction.
