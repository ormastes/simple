# Unwrapped `[Struct]?` in an unannotated local loses element provenance

- **Status:** open. Found while narrowing
  `transient_promote_struct_param_copy_dangles_2026-10-25.md`. It is not the
  cause of that crash: gdb showed the crashing elements were reused memory.
- **Compiler:** Stage 2 `S/r27/stage2-simple` (sha 49f16554), native,
  aarch64, cranelift.

## Repro

```
struct PuEv:
    source: text
    operation: text
    ident: text
    n: i64

fn e1(events: [PuEv], p: text) -> [PuEv]?:
    Some(events.push(PuEv(source: "git", operation: "create", ident: p, n: 7)))
```

| form | result |
|---|---|
| `val v: [PuEv] = e1(z, "a")!; v[0].operation` | OK `create` |
| `match e1(z, "a"): case Some(r): r[0].operation` | OK |
| `val v = e1(z, "a")!; v[0].operation` | prints a heap handle as i64 (~2e14) |
| `val v = e1(z, "a")!; val f: PuEv = v[0]; f.operation` | `git` (field 0, for every field) |
| `var v: [PuEv] = []; v = e1(v, "a")!; v[0].operation` | `git` (field 0) |
| `for x in e1(z, "a")!: x.operation` | heap handle as i64 |
| non-optional `fn e3(...) -> [PuEv]`, `e3(...)[0].operation` | OK |

The lead's `inv8` (`compiler_inventory_parse_name_status_v1(...)!` then
`p[0].operation`) is the third row.

## Suspected location (not verified)

`HirExprKind.Unwrap` MIR lowering (`50.mir/_MirLoweringExpr/expr_dispatch.spl`,
`case Unwrap(base)`) carries `struct_value_syms` only for a `Named` payload.
For an `Array(Named)` payload it records neither the payload HIR type
(`remember_local_hir_type`) nor `array_element_struct_syms`. As a result,
Index on the result has no element owner, and `resolve_field_index` falls
back to field 0.

The `var` reassignment row shows that the declared type of the assigned
local is not consulted either.
