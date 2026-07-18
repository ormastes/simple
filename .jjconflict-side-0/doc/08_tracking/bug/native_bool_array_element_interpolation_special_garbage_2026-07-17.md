# BUG: native backend bool array element via string interpolation prints `<special:N>` garbage

- **Date:** 2026-07-17
- **Status:** FIXED at 2026-07-17 (fix lane s16, worktree wt_s9; landed as commit a0c03cb07ba, cherry-picked onto tip 9b6f34f9b75 after two independent, overlapping fixes — 71a4d0f21e4 "preserve bool array element types" and dd848072025 "preserve class array field metadata" — landed in between; see "2026-07-17 root cause + fix" below for what stayed vs. what those commits already covered). Verified under `bin/simple native-build`. Re-tested this doc's EXACT minimal repro verbatim (`var flags: [bool] = [true, false, true]; var x = flags[0]; print x; print "{x}"`, no type annotation on `x`, matching the doc precisely): BEFORE any of these three fixes it printed `11` (BOTH the bare `print x` and the interpolated `print "{x}"` were wrong — not only interpolation as originally described; `x`'s Bool-ness was lost the moment it was rebound to an untyped `val`/`var`, so every later read of `x` decoded the raw i64 tag bit instead of `true`/`false`). AFTER, it correctly prints `truetrue`. The defect additionally (and more visibly) affects bool/text elements read from a CLASS or STRUCT array FIELD (`f.bits[i]`, `c.names[i]`) — verified fixed for both a `class` and a plain value-type `struct`.
- **Area:** compiler native codegen (array element read + bool/text string interpolation): both a plain untyped `val`/`var` rebinding of an array-read bool, and any class/struct array FIELD read
- **Severity:** medium (silent wrong output; no crash)

## Symptom

Reading a `bool` value from an array and interpolating it into a string via
`"{x}"` syntax produces garbage output like `<special:N>` instead of the
expected `true` or `false`.

Direct `print x` of the same bool value works correctly (prints `true` or
`false`). The defect is specific to string interpolation of array-read bools.

This affects compiled native-build output; the interpreter does not show
this behavior.

## Minimal repro

```simple
fn main() -> i32:
    var flags: [bool] = [true, false, true]
    var x = flags[0]
    print x                   # Correct: prints "true"
    print "{x}"               # WRONG: prints "<special:0>" or similar garbage
    0
```

Probe: `probe06_debug_bool.spl` (from repro session)

Expected output: `true`
Actual output: `<special:0>` (or `<special:N>` for other indices)

**2026-07-17 re-verification note:** re-running this exact repro under
`bin/simple native-build` (not the interpreter/oracle path the original repro
session may have used) showed BOTH `print x` and `print "{x}"` printing the
raw digit `1` (concatenated as `11`, no `<special:N>` string) before the fix
below — i.e. the direct `print x` was not actually correct pre-fix on this
path either, contrary to this section's original claim. The underlying cause
(the untyped `var x = flags[0]` rebind losing its Bool MIR type) affects
every later read of `x` equally; see "2026-07-17 root cause + fix" below.

## Impact

Any code using bool arrays and then interpolating element values into text
(logging, error messages, formatted output) will silently produce unreadable
garbage instead of `true`/`false`.

## Workaround

Avoid direct string interpolation of array-read bools:
```simple
var x = flags[0]
var text = if x: "true" else: "false"
print text                    # Correct workaround
```

## Source fix and regression coverage

Two MIR fixes preserve the bool type through the complete failing path:

1. Index lowering retains the array's known element type and applies the
   bootstrap text fallback only when no element type was recovered.
2. Both Let-lowering paths preserve a bool initializer's MIR type when a
   `val` or `var` binding creates a fresh local.

`scripts/check/check-native-seed-parity.shs` adds the strict dual-backend
`bool_array_element_interp` case. It checks direct interpolation of
`flags[0]`/`flags[1]`, bare and interpolated output after `val`/`var` bindings,
and primitive array fields on a struct and class, with fixed output on LLVM and
Cranelift. Linux runs it in the full gate; macOS arm64/x64, Windows x64, and
FreeBSD select it explicitly. First staged platform-matrix execution is pending.

## Cross-reference

Distinct from `native_class_array_field_mutation_segfault_2026-07-17` (that
bug causes crashes on mutation; this causes silent output corruption on read
+ interpolation). Both suggest array-element handling in native codegen has
type/representation issues. (2026-07-17 update: the mutation-segfault doc
turned out NOT to reproduce under native-build at all — it's a bootstrap
Rust-seed-JIT-only defect; THIS doc's real/fixed defect is native-build-side
and class/struct-field-specific.)

## 2026-07-17 root cause + fix (fix lane s16, worktree wt_s9)

**Root cause:** a class/struct FIELD access (`c.items`, `self.bits`) has no
HIR expression-type-inference result on the native-build `--entry` path, so
the existing Field-access lowering (`expr_dispatch.spl`, two call sites) had
no way to know the field's declared ARRAY ELEMENT type. It defaulted the
loaded field's MIR type such that a later `[idx]` read/`.len()`/`for` loop on
that field decoded elements generically instead of as the field's real
declared element type — a bool element printed its raw tag/int instead of
`true`/`false`; a text element printed its raw heap-handle number instead of
the string. Confirmed via targeted `print`-based tracing (`SIMPLE_DUMP_MIR`-
adjacent, in-source debug prints, removed before the final patch) that:
1. The field's declared array element type IS available at MIR-lowering
   time, straight from the class/struct DEFINITION (parsed field type,
   independent of expression inference) — just never threaded through.
2. Even after threading it onto the field-read result's MIR type, a
   SEPARATE, pre-existing gap in `Let`-statement lowering
   (`mir_lowering_stmts.spl`) defaulted an UNTYPED `val x = <bool expr>` (no
   `: bool` annotation) back to a generic i64-typed binding, discarding the
   just-recovered Bool-ness for any code that reads `x` later (a direct
   `"{c.bits[0]}"` with no intermediate binding was unaffected).

**Fix (pure-Simple, `src/compiler/**.spl` only):**
- `src/compiler/50.mir/mir_lowering_types.spl`: new `MirLowering` field
  `struct_field_array_elem_type: Dict<text, [HirType]>` (struct/class NAME ->
  per-field declared array element HirType, `HirTypeKind.Error` sentinel for
  non-array fields), mirroring the existing `struct_field_type_name` map's
  role for nested struct names.
- `src/compiler/50.mir/_MirLowering/module_lowering.spl`: populate the new
  map in `prescan_module_struct_names` from each field's declared HIR type
  (`Array(elem, _)`/`Slice(elem)`); init the field to `{}` in the
  `MirLowering` constructor.
- `src/compiler/80.driver/driver_pipeline.spl`: init the same new field to
  `{}` at its two OTHER direct `MirLowering(...)` struct-literal construction
  sites (the ones actually used by `--entry` native-build) — omitting it left
  the field `nil`, causing a `method 'has' not found on type 'nil'` compile
  error the first time it was exercised.
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`:
  propagate the new map into the lambda-lift child `MirLowering` instance,
  alongside the existing `struct_field_type_name` propagation.
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (both Field-access
  lowering sites — the disc-guarded fast path and the fallback dispatch,
  which the file's own Bug #166 comments already document as "kept in
  sync"): look up the field's element type via the new map BEFORE computing
  `field_type`/calling `emit_get_field`, and when found, use it to build the
  field-read result's MIR type as a real `Array(elem)` (not the previous i64
  default) — this is what makes the existing, already-correct
  `local_hir_types`-consultation in the `Index` case (fixed for
  `.split()`-result arrays by commit 4539b364955) also work for class/struct
  array fields. Also registers `local_hir_types`/`runtime_array_locals` on
  the field-read result for defense in depth.
- `src/compiler/50.mir/mir_lowering_stmts.spl`: new `local_is_bool` helper
  (mirrors the existing `local_is_float`), wired into BOTH `Let`-lowering
  `effective_type` computations so an untyped `val`/`var x = <bool expr>`
  inherits the initializer's real Bool MIR type instead of defaulting to i64.

**Verification (native-build, tip 985885cb314; pre-patch state re-checked via
`git stash` on the 6 source files, doc edits kept staged throughout):**
- `val flags = [true, false]; print "{flags[0]} {flags[1]}"` (inline index,
  no intermediate binding) -> `true false` both before and after the patch
  (unaffected control — never took the buggy Let-binding path)
- `var x: bool = flags[0]; print x; print "{x}"` (explicit `: bool`
  annotation) -> `truetrue` both before and after (unaffected control — the
  annotation carries the type directly, bypassing the buggy defaulting)
- **This doc's EXACT repro, re-run verbatim** (`var flags: [bool] = [true,
  false, true]; var x = flags[0]; print x; print "{x}"`, NO type annotation
  on `x`): BEFORE this patch -> `11` (both prints wrong, not only the
  interpolated one as originally described); AFTER this patch -> `truetrue`
  (correct). This is the actual doc-defined defect and it is fixed.
- New class-field probe (`class Flags: var bits: [bool]`, `val x =
  f.bits[0]; print "x={x}"; print "interp={x}"; print "direct={f.bits[1]}"`)
  -> BEFORE fix: `x=1interp=1direct=2` (garbage); AFTER fix: `x=true
  interp=true direct=false` (correct)
- Same probe reshaped as a plain value-type `struct` instead of a `class`
  (`struct Flags: bits: [bool]`, constructed via `Flags(bits: [...])`) ->
  BEFORE fix: `x=1interp=1direct=2`; AFTER fix: `x=true interp=true
  direct=false` (correct) — confirms the fix covers the "bool-in-struct-array"
  shape, not only classes.
- New class-field probe with a `[text]` field alongside an `[i64]` field
  (push+index-assign+push, then read all elements back) -> BEFORE fix:
  `names0`/`names1` printed raw heap-handle numbers; AFTER fix: `names0=a
  names1=b` (correct); the pre-existing-correct `[i64]` field reads
  (`items_len=3 items0=99 items2=42`) are unchanged.
- Regression gate `sh scripts/check/native-smoke-matrix.shs`, run both before
  finalizing and again after the stash round-trip:
  `total=15 pass=15 fail=0 xfail=0 xpass=0 codegen_fallback_hits=0`.
