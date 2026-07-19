# native-build: ANY struct crashes with `method \`has\` not found on type \`nil\`` (P0, fixed)

**Severity:** P0 (native-build of any program containing a struct was broken on `main`)
**Found:** 2026-07-18, bugfix campaign lane SF
**Status:** fixed
**Backend:** native-build (`--entry` / single-file), both the `--entry-closure`
and non-closure driver paths

## Symptom

Native-build of any program that declares and uses a struct crashed with:

```
error: semantic: method `has` not found on type `nil` (receiver value: nil)
```

No source location was carried by the diagnostic. Reproduced with the
smoke-matrix `struct_field` case (case 6, "struct construct + field read"):

```
SIMPLE_BINARY=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  SIMPLE_NO_STUB_FALLBACK=1 NATIVE_SMOKE_CASES=struct_field \
  sh scripts/check/native-smoke-matrix.shs
```

Confirmed regression window: PASS (rc=71) at `a79a52ba817`, FAIL at
`origin/main` (`a618b8d62c0`).

## Bisect

`git bisect` (`a79a52ba817` good .. `a618b8d62c0` bad, 22 commits, generous
400s per-case timeout, signature-matched on the exact
"method \`has\` not found on type \`nil\`" string to avoid misclassifying
unrelated build failures as this bug) converged cleanly to:

```
cd68cb9af439bf5a107e1e2473addcc2787cda87 fix(native): canonicalize Option ABI boundaries
```

## Root cause

Commit `cd68cb9a` added two new non-optional `Dict`-typed fields to the
`MirLowering` struct (`src/compiler/50.mir/mir_lowering_types.spl`):

- `struct_field_hir_type: Dict<text, [HirType]>`
- `option_value_locals: Dict<i64, bool>`

It correctly added `{}`-initialization for both fields at the canonical
constructor (`MirLowering.new_for_target`,
`src/compiler/50.mir/_MirLowering/module_lowering.spl:60-98`), and at the
per-function reset in `function_lowering.spl`.

However, `src/compiler/80.driver/driver_pipeline.spl` has **two additional
brace-literal `MirLowering(...)` constructions** (lines ~444 and ~536, the
`--entry-closure` path and the plain/no-sources path respectively) that build
a `MirLowering` value directly instead of calling `new_for_target`. Both
literals were not updated and omitted `struct_field_hir_type`,
`option_value_locals`, and (pre-existing but never noticed until now)
`runtime_value_locals` and `nil_locals`. Per the Simple seed's declared-order
nil-fill semantics for brace/positional struct-literal initialization (see
`6b59a8c4bf7`), every field omitted from a named struct literal is silently
filled with `nil` rather than erroring — so these `MirLowering` instances end
up with `self.struct_field_hir_type == nil`.

Both driver paths call `direct_lowering`/`lowering.prescan_module_struct_names(...)`
before lowering any function body (a crossmodule struct-layout prepass). That
prepass calls `register_composite_field_metadata`
(`src/compiler/50.mir/_MirLowering/module_lowering.spl:355`, pre-fix):

```
if overwrite or not self.struct_field_hir_type.has(name):
    self.struct_field_hir_type[name] = field_hir_types
```

`self.struct_field_hir_type` is `nil` on the driver-constructed instance, so
`.has(name)` fails with exactly the observed diagnostic. Confirmed by
temporary `print`-based instrumentation (stdout only — native-build worker
stderr is swallowed, see `.claude/memory/ref_native_build_eprint_lost.md`)
before each `.has()` call in `register_composite_field_metadata`: the build
log showed `pre struct_field_hir_type name=Point` as the LAST line printed
before the crash, with no subsequent `pre struct_field_array_element_type_name`
line — pinpointing the exact call.

Note: the coordinator's earlier hypothesis (that the crash was at
`expr_dispatch.spl`'s two `struct_field_repr_name.has(...)` call sites,
~L807/~L2236) was disproven — those sites already had nil guards and guarding
them further did not fix the bug, because `struct_field_repr_name` is
correctly initialized everywhere; the actually-nil field was the newer
`struct_field_hir_type`.

## Fix

Added the four missing fields (`struct_field_hir_type`, `runtime_value_locals`,
`option_value_locals`, `nil_locals`) to both `MirLowering(...)` brace literals
in `src/compiler/80.driver/driver_pipeline.spl`, initialized to `{}`/empty
dict, matching the canonical `new_for_target` constructor.

## Verification

- `NATIVE_SMOKE_CASES=struct_field` native-smoke-matrix: FAIL (build-failed,
  `method \`has\` not found on type \`nil\``) before fix -> PASS (rc got=71
  want=71) after fix.
- Full `native-smoke-matrix.shs` (19 cases, no case filter): 18 pass, 1
  pre-existing unrelated failure (`option_nil_check`, rc got=84 want=7 — this
  is the already-tracked, still-open
  `native_try_op_on_option_silent_wrong_2026-07-14.md` uniform-tagged-Option-ABI
  gap; reproduced identically with this fix reverted, confirming it is not a
  new regression introduced here).

## Files changed

- `src/compiler/80.driver/driver_pipeline.spl` — added the 4 missing
  `{}`-initialized fields to both `MirLowering(...)` literals (~L444-492 and
  ~L536-584).
