# Bug: self-hosted native-build crashes on ANY struct field access ("field access on nil receiver")

- **Date:** 2026-07-24
- **Lane:** self-hosted AOT `native-build` (flat `--entry-closure` path; both default and `--backend cranelift`)
- **Severity:** P0 for the AOT lane — blocks compiling essentially any real program
- **Status:** OPEN — characterized, root-cause narrowed to `lower_hir_expr` Field arm

## Repro (5 lines, reproduces on the DEPLOYED `bin/release` binary)

```simple
struct S:
    name: text
fn main():
    val v = S(name: "A")
    print(v.name)          # native-build: SIGILL "field access on nil receiver"
```

`bin/release/<triple>/simple native-build repro.spl -o out` → SIGILL (rc 132).
Also crashes with `--backend cranelift`, with `--entry-closure --mode one-binary`,
and for field access via a **method receiver** (`self.name`), a **typed param**
(`s: S` → `s.name`), and in **arithmetic** (`v.a + 1`). i64 and text fields both
crash. Multi-field and single-field both crash.

## What works (isolation)

- **Interpreter** `simple run repro.spl` → prints `A` (rc 0). HIR lowering logic
  is correct; only the AOT lowering path crashes.
- **Seed** (`compiler_rust/target/bootstrap/simple`) native-builds it fine — the
  seed uses its own Rust lowering, not the `.spl` lowering.
- `match` on a plain enum local, enum-payload binds, and non-field programs all
  native-build fine (probe_enum3/enum6/trivJ/t2/rich/pm1/pm2/pm4 green).

So the defect is specific to the **`.spl` AOT lowering of a struct FieldAccess
expr** on the `lower_parser_module_unstub → lower_module` path.

## Crash site (gdb backtrace, stage4 binary, origin e0d214b8fb0)

```
runtime error: field access on nil receiver
SIGILL in hir__hir_lowering__expressions__HirLowering.lower_hir_expr
  <- lower_interpolation_list           (for the "{v.name}" form)
  <- lower_hir_expr
  <- lower_hir_stmt / lower_hir_stmt_multi
  <- lower_hir_block_unit
  <- lower_function
  <- lower_module
  <- lower_parser_module_unstub
  <- CompilerDriver.lower_and_check_impl -> compile -> cli_native_build
```

Field-access lowering is `expressions.spl` lines 305–420 (dispatched by
`kind_disc_v == 21232742  # hash("Field")`, `case ExprKind.Field(base, field)`).
Candidate nil-deref sites in the type-recovery block (reached when
`local_struct_types` does NOT resolve the base — plausible on the flat
`--entry-closure` path, which registers type defs separately; see recent
`2f475c2329f` / `7091b3ebfa9`):
- L401 `self.symbols.get_symbol_type(fld_base_sym).unwrap().kind` — `.?`-guarded
  but the JIT/native `Option` unwrap-nil landmine can slip a nil through.
- L409 `self.current_method_self_type.unwrap().kind`.
- Or a nil receiver from the recursive `lower_hir_expr(base)` at L311.

## Context — this is the AOT FRONTIER, not a regression of shipped behavior

The flat `--entry-closure` self-hosted native path is under active construction:
recent commits `2f475c2329f` (register class field layout in flat entry-closure
MIR), `7091b3ebfa9` (register enum/struct type defs), `b96c8203a69` (first CORRECT
self-hosted-compiled binary), `2f6430a87c8` (probe_enum6 SIGILL cleared). Struct
field access is simply the next unimplemented edge. Parallel sessions are actively
editing this path — coordinate before large changes here.

## Next step

Add print-trace bisection in the `expressions.spl` Field arm (L305–420) to find
the exact nil-deref, or make the flat `--entry-closure` path populate
`local_struct_types` / `struct_field_types_by_name` for locally-constructed
structs so the type-recovery block is not entered at all. One stage4 build
(~10 min, `--threads 4` under memory contention) per iteration.
