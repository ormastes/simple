# Cross-module `Class.new` static calls fail once two classes share the leaf name `new` (MIR owner hint never computed)

Date: 2026-09-01. Status: FIXED (MIR-layer recovery), with one filed residual (see companion record
`static_method_owner_misbind_on_class_name_collision_2026-09-01.md`).

## Symptom (measured on the MCP native build, 133 errors total, 14 in this class)

Every failing site is a `Class.new(...)` STATIC call (`store_core.spl:45,154,194,215`,
`store_operations.spl:451,475,497` -- the reported locations `store_core.spl:41:36` /
`store_operations.spl:44:11` are wrong, as usual for this lane), producing the pair:

    MIR lowering error: undefined variable AssistantStore
    MIR lowering error: unresolved method call: new

`src/std/common/encoding/utf8.spl:14` (`Utf8Provider`) has the identical shape, so the fix
clears more than the 14.

## This is NOT registration ordering

Classes ARE registered. The mechanism, established by A/B repro:

- `expr_dispatch.spl:3572` passes an EMPTY owner hint (`"", -1`) for every MethodCall.
- So `static_receiver_name` stays `""` at `method_calls_literals.spl:1199`, and the
  owner-qualified recoveries in the Unresolved arm (struct_method_syms key at :2886,
  name-derived owner at :2937) never fire.
- Resolution then rests entirely on `lookup_unique_static_method`
  (`hir_symbol_table_methods.spl:362`), which fail-closes the moment TWO types anywhere in
  the compilation closure expose the same static leaf. `new` collides first, always.
- The receiver falls through to value lowering: "undefined variable {Class}".
- The cascade crosses files because the collision is CLOSURE-wide, not module-local; and
  `struct_method_syms` is reset per module (`_MirLowering/module_lowering.spl:1081`), so
  same-module registration cannot rescue importers.

This is a MIR-layer recovery for the structural gap filed as
`resolve_methods_never_runs_on_real_compile_path_2026-09-01.md` -- HIR leaves these calls
`Unresolved`; it does not resolve that record.

## Minimal repro (verified A/B, native_build_worker, seed interpret mode)

    # single.spl
    class Single:
        x: i64
    impl Single:
        static fn new(x: i64) -> Single:
            Single(x: x)

    # single4.spl -- same shape, class Store4, also `static fn new`
    # single3.spl -- same shape, class Store3, but `static fn create`

    # main9.spl (FAILED before fix, rc=1; passes after, binary runs correctly)
    use app.zz.single.{Single}
    use app.zz.single4.{Store4}
    fn main():
        val a = Single.new(1)
        val s = Store4.new("a")

    # main8.spl (always passed): Single.new + Store3.create -- unique leafs.

One `static fn new` in the closure: passes (unique-leaf fallback). Two: both break, exactly
the MCP shape.

## Fix

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (~:1200): when the hint is
empty and the receiver is a `NamedVar` that is not a lowerable local, and its ATTACHED
symbol id names a Class/Struct, adopt that name+id as the static owner
(`static_receiver_owner_id`), which routes the Unresolved arm through the exact
`lookup_method_in_type` path instead of the unique-leaf fallback.

A name-keyed fallback (`lookup_or_invalid(name)`) was tried and REMOVED: it misbound under
class-name collisions (measured `dup tag=B`, expected `A`). Only the attached id is used.

## Measured

- main9: rc=1 -> rc=0; produced binary prints correct values (`ok 1 a`).
- main8/main4/main_dup builds green; main2/5/6/7 control repros unaffected.
- Real MCP build: before = 133 errors (121 `MIR error` lines; measured on the
  2026-09-01 pre-12:36 seed). After the fix the MIR stage reports 0 errors, but the run
  now dies EARLIER at `semantic: undefined field 'symbols': cannot access field on value
  of type 'bool'` -- a seed-interpreter regression from a sibling lane (uncommitted edits
  to `src/compiler_rust/compiler/src/interpreter_*` in the shared tree). The A/B rerun of
  the UNFIXED compiler on the same seed also dies there with 0 MIR errors, so the clean
  14-error delta on the full MCP build could not be measured today; re-measure after the
  seed lane settles.
