# Optional record owner is lost when an if/match arm is `Some(<record literal>)`

Status: OPEN (compiler, MIR). Not fixed; handed off. Related to
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
