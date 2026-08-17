# Bug: self-hosted native-build crashes on ANY struct field access ("field access on nil receiver")

- **Date:** 2026-07-24
- **Lane:** self-hosted AOT `native-build` (flat `--entry-closure` path; both default and `--backend cranelift`)
- **Severity:** P0 for the AOT lane — blocks compiling essentially any real program
- **Status:** OPEN — an earlier layout-metadata nil was repaired in source; rebuilt execution and the later Field arm remain pending

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

## Earlier in-process blocker found (2026-07-24)

The true pure-Simple bootstrap path is the single positional source form:
`simple native-build file.spl ...`. The earlier `--entry`/`--source` probes
routed through `rt_native_build` and did not exercise self-hosted lowering.
With a no-stub 675-file candidate (SHA-256
`a654b28ca1c9f4917293f124eb75769302ec47dfb268f867105860f3997d6eb7`),
the positional C5 build fails first with:

```
runtime error: field access on nil receiver
SIGILL in TypeLayout.compute_struct_layout
  <- MirLowering.lower_struct_type
  <- MirLowering.lower_module
  <- CompilerDriver.lower_to_mir
```

An unannotated struct should carry `has_layout_attr=false` plus a valid default
`LayoutAttr`. HIR lowering instead constructed a `LayoutAttr?` in value
position and passed it into the desugared `has_layout_attr`/`layout_attr` pair;
on Stage4 this can produce a true flag with a nil payload. Current source keeps
the parsed layout value plain, computes the presence bit directly, and supplies
both desugared fields explicitly for structs and classes. No consumer-side nil
default was added because that would hide malformed explicit ABI metadata.
Source contract: 5/5 passing. Rebuilt positional execution is pending the next
bounded cycle.

## Update (2026-08-17): both cited nil-deref candidates are GONE from current source; native lane still unverifiable

Classified by CONTENT (grep of current source), not commit ancestry.

**Crash site A — `TypeLayout.compute_struct_layout` via `lower_struct_type`
(the `LayoutAttr?`-in-value-position nil): FIXED in-tree.**
`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:657,675` (and
`:753` for structs) now reads

```
val layout: LayoutAttr = parse_layout_attrs(class_attributes)
val has_layout = layout.layout_kind != TypeLayoutKind.Simple or layout.has_explicit_align or layout.is_packed
```

— a plain non-optional `LayoutAttr` value with the presence bit computed
directly, exactly what this doc's own closing paragraph prescribed.
`hir_definitions.spl:154,185` declares `layout_attr: LayoutAttr` (not
`LayoutAttr?`), so no consumer can receive a true flag with a nil payload.
All four `35.semantics` consumers (`effect_validation.spl:78`,
`layer_eq_validation.spl:77`, `lint/sffi_lint.spl:298,613`) read
`.layout_attr` only under `if ...has_layout_attr:` and are safe as a result.

**Crash site B — the `expressions.spl` Field arm (L401 `get_symbol_type(...).unwrap().kind`,
L409 `current_method_self_type.unwrap().kind`): those `.unwrap()`s no longer
exist.** `src/compiler/20.hir/hir_lowering/expressions.spl` now contains **one**
`.unwrap()` in the whole file, and the field-access type recovery goes through
`self.symbols.get_symbol_named_type_raw(raw_base_symbol_id)` (`expressions.spl:225`)
— a nil-safe raw-i64 helper added in `src/compiler/20.hir/hir_types.spl:738`
alongside `get_symbol_type_raw` (`:723`), whose docstring names this exact bug.
`hir_lowering/**` is owned by another lane this session and was NOT edited here.

**Not proven:** that the SIGILL is actually gone. This host has no usable
self-hosted `native-build`. `bin/simple` is the Rust seed (mtime 2026-08-16
22:59, prints the seed banner). `bootstrap/stage3/simple` is a 3.4 MB
`simple-bootstrap` stub that **SIGSEGVs (rc 139, core dumped) on a trivial
`fn main(): print("hi")`** — the control fails, so it cannot witness this bug.
Interpreter control passes: `bin/simple run repro.spl` prints `A`, rc 0.

**Not a shared root cause with
`stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`.**
`"field access on nil receiver"` is the generic runtime trap emitted for ANY
nil receiver; it is referenced by ~20 unrelated call sites across
`10.frontend`, `20.hir`, `40.mono`, `50.mir`, `70.backend` and `src/lib`. The
two docs are the same SYMPTOM class with three distinct nil sources. Do not
merge them.

### Native lane is fully unavailable in this worktree (2026-08-17, measured)

Three independent attempts, all on the 5-line repro from this doc's own Repro
section, none of which reached the defect:

| binary | result |
|---|---|
| `bin/simple run` (interpreter) | prints `A`, rc 0 — control PASSES |
| `bootstrap/stage3/simple native-build` | **SIGSEGV rc 139, core dumped, even on `fn main(): print("hi")`** — it is a 3.4 MB `simple-bootstrap` stub, not a stage3 self-host |
| `bin/simple native-build` (Rust seed) | rc 1: `error: LLVM native linking failed: ... ld.lld: error: cannot ope[n]` then `native-build worker exited with code 1` |

Note the third row contradicts this doc's "What works (isolation)" claim that
the seed native-builds the repro fine: it no longer does *here*, and it fails
at LINK time, i.e. before any lowering defect could be observed. So this is an
environment/toolchain breakage, not evidence about the bug either way.

**Nothing in this session verifies or refutes the native SIGILL.** The
content-level findings above stand on source inspection alone.
