# Stage 3 MIR: `HirStmtKind.Let` payload 1 refused in statements.spl — a lost unwrap (2026-11-14)

**Status:** source FIXED at `83634778a5f` (already on `release/1.0.0`, after the run-31 pin);
diagnostic and regression pin added by this record's change; two compiler gaps OPEN (below).
**Area:** `src/compiler/20.hir/hir_lowering/statements.spl`,
`src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl`
**Related:** `p3_census_mir_classes_2026-11-13.md` (class 3, first occurrence),
`unguarded_optional_record_to_plain_param_accepted_2026_11_14.md` (same family, call path).

## Symptom

Bootstrap run 31, Phase 3 (Stage 2 compiling the pinned `5fc681dfd66` tree), MIR, three times:

```
enum construction 'compiler.hir.hir_definitions.HirStmtKind.Let': payload type mismatch at 1;
function=lower_hir_stmt module=compiler.hir.hir_lowering.statements
payload_at=src/compiler/20.hir/hir_lowering/statements.spl:1112:61   (also :1237:41, :1279:41)
```

## Cause

The source was wrong; the MIR check was right.

```
val vr_hir_type = if vr_has_annotation: self.lower_type(..) else: nil          # HirType?
val vr_binding_type: HirType = if vr_has_annotation: vr_hir_type else: ..      # annotated
HirStmtKind.Let(vr_symbol, vr_binding_type, vr_hir_init)                       # slot 1: HirType
```

- An if-join of a `T?` arm and a `T` arm is remembered as `T?`, in either arm order (measured on
  the frozen Stage 2 with both orders), so the initializer local is `HirType?`.
- An annotated `val x: T = init` copies the initializer's remembered type unless that type is
  uninformative (`let_declared_type_override_v1`: Infer / Error / erased handle / Result). A
  `T?` is informative, so `x` stays `T?`. The annotation does not win, and must not: the value
  really can be nil.
- `enum_payload_local_compatible` then refuses `T?` for the non-optional slot. Trace on the
  frozen run-31 Stage 2: `expected='named#1' remembered='named#1?' source='named#1?'`.

History of the three sites: fixed by `a7c07361cbc` (`if val annotated_type = hir_type:`),
silently reverted by `04922c108b3` (a rebase-casualty repair that restored the pre-fix
lines), fixed again by `83634778a5f` (lower the annotation once into a plain `HirType`
binding, derive the nullable separately). Run 31 was pinned at `5fc681dfd66`, which has the
revert and not the second fix. Nothing in the tree could see the regression short of a
Stage 2 MIR pass.

## What changed here

1. **Diagnostic** (`enum_payload_mismatch_message`): when the refused argument is a binding
   whose remembered type is `T?` and the slot is the non-optional `T`, the message now reads
   `payload type mismatch at N: optional 'T?' value into non-optional payload slot (declared
   'T'); unwrap it first (`if val`)`. The stem is unchanged, nothing new is accepted or
   rejected, and the nil-literal and plain-mismatch wordings are untouched.
2. **Regression pin** (`test/01_unit/compiler/mir/let_annotated_optional_join_spec.spl`):
   drives the real pure-Simple HIR + MIR lowering on the seed (about 30 s), so the class is
   red/green without a Stage 2 binary, and counts nullable-merge arms joined into an annotated
   `: HirType = if` binding in `statements.spl` (3 on the pinned tree, 0 at tip).

Rule stated: an unguarded `T?` never fills a non-optional enum payload slot, whether it
arrives directly, through an un-annotated join, or through an annotated `val x: T`; the
annotation does not launder it. The fix is at the source (`if val`, or bind the plain value
once).

## Evidence

| What | Measured on | Result |
|---|---|---|
| pinned shape, annotated join | frozen run-31 Stage 2, `native-build` probe | red, `payload type mismatch at 1` |
| un-annotated join / optional passed directly / annotated copy | same | red (3 more) |
| tip shape (`83634778a5f`) and `if val` shape | same | green; binary prints `101 7` for both |
| same join with the arms swapped (annotated and not) | same | red (2) |
| annotated join into a struct field / a plain parameter | same | **accepted silently** (gap 2) |
| structural copy of the two changed compiler functions | same | builds, links, 8 cases correct |
| spec before the message change | seed, pure-Simple HIR+MIR | 14 run, 10 passed, 4 failed (the four wording cases) |
| spec after | seed | 14 run, 14 passed |
| source pin on the pinned `5fc681dfd66` `statements.spl` / on tip | seed | 3 / 0 |

Line coverage of `enum_constructor_payload.spl` (seed, `spl-coverage module`): 30.0% (69/230)
from the new spec alone, 48.6% (112/230) with the six neighbouring enum-payload specs. The
module is below the 90% bar; closing that means testing its unrelated array / dict / numeric
payload paths. Of the added code, lines 492-494, 498-499, 501, 503-504 and 508 are recorded
hit. Seven
neighbouring cases (6 in `contextual_enum_payload_spec`, 1 in
`nil_singleton_type_pipeline_spec`) and the load of `generic_self_method_result_ctor_spec`
fail identically with and without this change.

The message change itself cannot be shown on the frozen Stage 2 (it is that binary's own
compiler); the copy above shows the new code lowers there.

## Sweep (src/compiler, src/app, src/lib; 2026-11-14 tip `a91ccdb5f38`)

Method: an awk pass, function-scoped, marking locals bound from a nil/None-armed `if`/`match`
merge, annotated `T?`, or a `T?` parameter; then reporting (a) such a local as a bare arm of
an annotated non-optional `val`, (b) an annotated copy of one, (c) either of those, or the
local itself, as an argument of an `Enum.Variant(..)` whose declared slot is non-optional.
Positive control: on the pinned tree it reports exactly 1112 / 1237 / 1279.

- (a) joins: **0** at tip.
- (c) non-optional enum slots: 17 candidates, none a blocker — 12 in
  `20.hir/generated/hir_codec.spl` (`val f = if raw == "N": nil else: parse_i64(raw)` into an
  `i64` slot after a reject guard; the scalar join carries no optional type and lowers, shown
  on the seed harness), 3 generic `Poll.Ready(v)` with `T = text?`, 2 false positives
  (pattern-bound shadow in `expression_core.spl:1673`).
- (b) copies: 6, all after an explicit `!= None` guard and none reaching an enum payload
  (`native_trait_conversion.spl:299,632`, `switch_operators_calls.spl:9640`,
  `rt_criticality_validation.spl:1088,1096`, `hir_frontend_diagnostics.spl:676`).

Not covered: optionals that arrive from a call result or a field read, multi-line
signatures, and flows into struct fields or call arguments (accepted by MIR today, so they
cannot block a bootstrap, but see gap 2).

## Open

1. **No diagnostic at the `val`.** `val x: T = <T?>` is accepted by HIR and by the MIR Let;
   the refusal appears only if `x` later reaches an enum payload. Rejecting at the Let is the
   owner rule (never widen nil) but was not switched on blind: the compiler's own source
   binds nullable values under non-optional annotations (the 6 guarded copies above; the Let
   `type_` slot is declared `HirType` and read with `!= None`), the sweep cannot see optionals
   that arrive from calls or fields, and each new refusal costs a bootstrap run. Needs a
   census on a built compiler first.
2. **Struct fields and plain parameters accept the same unguarded `T?`** (Stage 2 probes
   above). Same family as `unguarded_optional_record_to_plain_param_accepted_2026_11_14.md`.
