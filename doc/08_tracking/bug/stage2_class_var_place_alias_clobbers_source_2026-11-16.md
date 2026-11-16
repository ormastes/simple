# Stage 2: class-typed `var t = a` aliases `a`'s local, `t = b` rebinds `a` (2026-11-16)

Status: fixed in MIR source on `work/class-var-place-alias-20261116`. It takes
effect natively only after Stage 2 is rebuilt. Stage 3 source has a tagged
workaround at the one site that blocked the build.

## Symptom (Stage 3 r16 self-build)

HIR lowering failed in every module that imports `LlvmTypeMapper`. The first
was `driver_bootstrap.spl`, and 303 modules cascaded from it:

    stale surface index [impls]: module=compiler.backend.common.type_mapper
    surface_key=1 802 4 owner=LlvmTypeMapper position=3 live_len=0

The smallest repro is a 4-line entry, `use compiler.backend.llvm_type_mapper.LlvmTypeMapper`.
`simple-r16 compile` of it fails the same way (228-file closure, 4m11s, 1.8 GB RSS).

## Root cause

In `register_imported_type_methods_inner`
(`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`,
s3wa2 tip `03b340fbbfe`, lines 1786/1802), the code does:

    var trait_module = imported_mod                          # :1786
    ...
    trait_module = self.module_surfaces.surfaces[idx]        # :1802

`LlvmTypeMapper` (`llvm_type_mapper.spl`: 2 top-level `impl` blocks, but the
surface's impls array has 4 rows, per the `... 4` in the surface key) implements
`TypeMapper`. That trait lives in `common.type_mapper`, which has 0 impls. The
reassignment overwrote `imported_mod` itself. The next impl row (position 3)
then read `type_mapper`'s empty impls. The surface key had been computed before
the clobber, so it still said `4`. The memo was not stale, and transient
reclamation was not involved.

The miscompile is in the MIR early-Let arm
(`src/compiler/50.mir/mir_lowering_stmts.spl` ~1839, the same on release/1.0.0
and on the integ2 pin `8453e87c8767`):

    elif (bf_sym != None or struct_sym != None) and not initializer_is_short:
        self.bind_local(symbol_value_id, init_local)

`maybe_copy_struct_value` returns nil for a class, which keeps reference
semantics. So a class place read fell through to an alias of the SOURCE local.
Sharing the object is correct; sharing the binding slot is not. The dead twin
arm (~2198) had the same shape.

Native fixture `test/fixtures/compiler/native_class_var_place_alias/main.spl`,
built by the integ2 Stage 2 (typed path, llvm):

    param a=tm t=tm      (expected a=llvm)
    typed a=tm t=tm      (annotation does not help)
    local a=tm t=tm
    loop a=llvm,tm,tm len=4   (expected llvm,llvm,llvm len=12)
    reverse a=tm t=tm    (val t = a; a = b also moves t)
    struct a=1 t=9       (structs are copied; unaffected)

An `if`-expression initializer does not alias, and neither do `i64`, `text`, or struct values.

## Fix

Alias only a fresh aggregate (`not mir_expr_kind_is_place(...)`). A place read
gets a new local and an `emit_copy` of the handle. The record
(`struct_value_syms`) and bitfield owner are carried onto it. Spec:
`test/01_unit/compiler/mir/class_var_place_alias_spec.spl` (red 2/4, green 4/4
on the seed).

Native proof (2026-11-16). The fix was compiled into a Stage 3: the integ2
Stage 2 compiled `mir_lowering_stmts.spl`, which was relinked into `simple-r17m`.
Both binaries ran `native-build --backend=llvm` on the fixture:

    r16  (unfixed): param a=tm t=tm   loop a=llvm,tm,tm len=4      reverse a=tm t=tm
    r17m (fixed):   param a=llvm t=tm loop a=llvm,llvm,llvm len=12 reverse a=tm t=llvm

`diaglink/s3i2/gate.sh` passes on r17m (j4/sc/hello, compile + native-build).

### Review follow-up (c5f4495d3a6)

- **The predicate is no longer syntactic.** A record initializer is now copied
  when it is a place read OR its local is already bound to a symbol
  (`MirLowering.local_is_symbol_bound`). The case this adds is a `do:` block
  whose tail is `a`: `lower_block` returns `a`'s own local, so the old place
  check let it alias. Fixture `do_block.spl` (the seed has no `do:`, so its
  expected output comes from the language semantics):
  r16 `block a=tm t=tm`, r17m `block a=tm t=tm`, r17n (this fix) `block a=llvm t=tm`.
- **The generic owner is carried.** `generic_instance_field_types` and
  `_struct_names` are now copied onto the new local, the same way
  `copy_struct_value_recursive` does. This is for parity only: there is no
  native red. r17m already prints `generic ... t=beta len=4` and
  `generic-struct a=4 before=4 t=8`.
- **A bitfield-only word still aliases (known divergence, unchanged from r16).**
  The interpreter prints `f=3,0 g=3,5` for `var g = f; g.hi = 5`. The results
  for `bitfield_alias.spl` (top level and a fn) and for main.spl + v_bitfield:

  | binary | `bitfield_alias.spl` | main.spl + v_bitfield |
  |---|---|---|
  | r16 | `f=3,5` | `f=3,5` |
  | r17m (6e2e04a2956, copies) | `f=3,0` | SIGSEGV at address 0x3 |
  | r17n (c5f4495d3a6, aliases) | `f=3,5` | `f=3,5` |

  The copy is correct on its own but crashes in a module that also has classes
  and generics, so this change keeps the r16 alias. Open: bitfield value
  semantics, and the cause of that crash.
- **A separate open divergence: a match initializer loses the class value.**
  It reproduces on both r16 and r17m and is not fixed here:

      fn v_block(a: Surf, all: [Surf], k: i64) -> text:
          var t = match k:
              case _: a
          t = all[1]
          "block a={a.name} t={t.name}"

  The interpreter prints `block a=llvm t=tm`; native r16 and r17m print
  `block a=llvm t=` (empty `t.name` after the reassign). It was moved out of
  the fixture so the fixture keeps the "interpreter and fixed native agree"
  contract.
- **Sibling sites are not fixed and are recorded here.** They come from the review and have not been reproduced natively. These bind a pattern
  name straight to the scrutinee's local, so `match a: case t: a = b; t.name`
  sees the new `a`:
  - `_MirLoweringExpr/switch_operators_calls.spl:3942`, the match catch-all;
  - `:4066` `bind_catch_all_arm`;
  - the if-val binding near `:4436`;
  - the same shape at `:1850`, `:1994`, `:4195` and `:4352`.

  The fix needs a "fresh local + copy + per-local metadata copy" helper. That
  metadata is about 15 maps (record, generic, array, dict, enum, option,
  presence...). That is larger than this fix, so it is left open.


Native proof, r17n (sha256 78f71a3902de6982...). It is r16 plus both MIR
objects (stmts and types) compiled by integ2 Stage 2, plus
reexport_mat_fix.o. main.spl prints every interpreter line, do_block prints
`block a=llvm t=tm`, and `gate.sh` passes. Cost: a typed `compile` of
`aggregate_intrinsics.spl` ran in parallel took r17m 24:03 / 6.13 GB and
r17n 24:01 / 6.15 GB, with an identical error set. The linear
`local_is_symbol_bound` scan does not measurably cost anything.

## Workaround (Stage 3 source)

`@workaround bug=stage2_class_var_place_alias_clobbers_source_2026-11-16` in
`module_reexport_materialization.spl`. It selects the trait owner by index and
binds it once with `val`.

An awk census looked for `var X = Y` / `val X = Y`, with `Y` class-typed and
either name reassigned later. It found no other site in the HIR/MIR/driver path.
It is a heuristic: `Y`'s type is inferred only from a parameter or `val`/`var`
annotation, or from a `ClassName(...)` initializer. An unannotated class local
can still hide this shape. Library hits (`ByteBuffer` writers, `Engine2D`, ...)
are outside the Stage 3 closure, or they never read the source again.

## Note on earlier guards

STALESURF (key includes `impls.len()`, 2026-11-08) and IMPLIDX-GUARD were added
for the same `live_len 0/1` symptom, assuming the memo was stale. They are
harmless, but they did not address this cause.
