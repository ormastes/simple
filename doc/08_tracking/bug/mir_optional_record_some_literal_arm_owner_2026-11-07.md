# Optional record owner is lost when an if/match arm is `Some(<record literal>)`

Status: Some-literal half FIXED (see "Fix" below); match-arm `case None: None`
half OPEN (see "Second cause"). Related to
`mir_optional_record_nil_join_2026_10_18` (nil arm half fixed in
`622b92cae46`); this is the remaining untracked non-nil arm case.

## Symptom (bootstrap run 15, Stage 2 row `compiler_cli_build`)

`Optional record has no unique provider layout snapshot` at
`src/lib/skia/feature/shaper/ot_layout_apply.spl:747:26` and
`src/lib/skia/feature/shaper/shaper.spl:667:31, 684:39, 687:38`.

`ot_layout_apply.spl` merges `_context1_match(..)` | `_context2_match(..)` |
`Some(_ContextMatch(...))` | `_chain3_match(..)` | `_chain12_match(..)` | `None`
in one value-position `if`, then `match matched`.

## Root cause (localised by a Stage 2 discriminator)

Owners enter `optional_record_owners` only from direct calls
(`remember_optional_record_owner`, `switch_operators_calls.spl` ~1478, keyed by
`bootstrap_fn_ret_opt_shape_lookup`). A `Some(<record literal>)` arm records
no owner, so `join_optional_record_owners`
(`src/compiler/50.mir/_MirLoweringExpr/optional_record_owner.spl:31`) treats
it as an unknown non-nil arm (deliberately fail-closed, pinned by
`test/01_unit/compiler/optional_record_nil_join_spec.spl` "does not treat
untracked nonnil arms as neutral") and clears the owner.
`checked_optional_record_type` (same file, line 47) then rejects the match.

Reproducers (single file, run-15 Stage 2 binary,
`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 <stage2>/simple native-build main.spl`):

- arms `m1(n)` | `m2(n)` | `None`: MIR passes.
- arms `m1(n)` | `Some(M(..))` | `m2(n)` | `None`: fails with the exact
  message above.

Both pass the seed-interpreted `HirLowering`+`MirLowering` spec harness: the
owner table is only fed on the native-build bootstrap-shape path, so there is
no seed-side red test yet.

## Intended fix

When `Some(payload)` is built for `Option` and the payload is a record of a
known single layout, record that exact owner on the tagged result (same key
form as `remember_optional_record_owner`). Do not make untracked arms neutral.
Needs a lowering-driven spec that populates the bootstrap fn-return shape
registry like native-build, plus negatives (conflicting owners, foreign
same-shaped record).

## Fix (2026-11-07, work/optional-record-some-literal-owner-20261107)

`remember_some_record_payload_owner` (`_MirLoweringExpr/optional_record_owner.spl`)
keeps the payload's exact declaration for `Some(<record>)` in a separate
join-only witness table, `optional_record_literal_owners`, under the key form
the callable-return registrar uses (`mir_class_identity_raw` for a class,
`composite_layout_key` for a struct, both folded through
`declared_struct_layout_key`). It is called from `lower_enum_construct_named`
(`switch_operators_calls.spl`, Option `Some` witness branch) only for a
`Named` payload with no supplied type arguments whose symbol exists in the
current table. `join_optional_record_owners` consults the witness only when a
tracked (call) arm already established an owner: a same-owner literal agrees,
a different-record literal clears the owner (still rejected). The witness never
establishes an owner by itself, so a literal-only or literal+untracked local
keeps its previous match route (review finding: storing it directly in
`optional_record_owners` would have newly rejected those). Reassignment
(`copy_optional_record_owner`) and `invalidate_optional_record_owner` blank a
stale witness. Untracked arms stay fail-closed.

Evidence:
- Spec `test/01_unit/compiler/optional_record_some_literal_owner_spec.spl`
  (seed-interpreted): red 0/6 on origin (helper missing), green 7/7 after
  (class + struct keys equal the registrar's; literal alone never
  establishes an owner; same-owner join in either order resolves the provider;
  Twin-vs-Seed join rejected with the unique-layout diagnostic; untracked third
  arm still clears; generic/scalar/unknown record nothing; stale witness dropped
  on reassignment/invalidation). Neighbours
  `optional_record_nil_join_spec` 10/10 and
  `optional_record_qualified_dependency_spec` 7/7 green.
- Native: see "Native red/green" below.

## Second cause: `case None: None` arm in an enum match (OPEN)

The `shaper.spl:667/684/687` errors (3 of the 4) contain no Some literal:
`val canonical: Option<CanonicalLayoutRun> = match ot_font: case Some(parsed):
<call or if(call|None)> case None: None`. Discriminators, all on the frozen
run-15 Stage 2 (`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 <stage2> native-build`):

| arms of `match font` (`Option<Font>`) | MIR |
|---|---|
| `case Some(p): resolve(p, n)` / `case None: None` | FAILS (unique provider layout) |
| same, `case None:` body replaced by a `resolve(..)` call | passes |
| same, pattern `case _: None` | passes |
| same, pattern `case nil: None` | passes |
| `if ok: resolve(n) else: None` (no match), annotated or not | passes |

So only the bare `None` *pattern* makes its arm's `None` body non-neutral.
Unconfirmed hypothesis: the pattern lowers as a `Binding` named `None`,
`bind_catch_all_arm` aliases it to the scrutinee, and the body's `None`
resolves to that local (expr_dispatch.spl named-var path yields to a
same-named local), so the arm value is the `Option<Font>` scrutinee whose owner
(`Font`) conflicts with `Run`. Runtime would still be right (the scrutinee is
None there), which is why it was never seen. Next step: print the arm's
`HirPatternKind` for that 5-line module in the seed spec harness.

## Native red/green

Fixture `red2` (arms `m1(n)` | `Some(M(..))` | `m2(n)` | `None`, plus a
Some-literal-only `lit_only`), helpers written `if c: None else: Some(..)` to
avoid the separate CONST-TYPE defect:
- frozen run-15 Stage 2: `Optional record has no unique provider layout
  snapshot at main.spl:24:22` (red).
- Mismatch fixture `lit2` (`m1(n)` -> `Option<M>` vs `Some(N(..))`): red on the
  frozen binary and must stay red.
- Stage 2 built from this branch (Rust seed `stage2-runtime-authority/simple`
  with the run-15 Stage 2 argv, `--threads 2`, 8G scope; 1616 compiled, 0
  failed, at `d590731f95d`, i.e. before the stale-witness blanking, which only
  narrows): `red2` builds and runs, printing `5 12 10 -1 6 61` (expected
  values). `lit2` (M vs N) is still rejected with the same diagnostic. The
  original `red` fixture now passes MIR and stops only at the separate
  CONST-TYPE defect (`native_const_type_void_checked_join_host_facade_2026-11-07`).
  `vd` (second cause) is still red, as expected.
