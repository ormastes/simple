# Self-hosted compiler: same-named `unit` declarations overwrite each other

Status: open. Found by code read, 2026-11-26; **not reproduced by a run** (no
self-hosted full-CLI binary is deployed on the finding host).

## What the code does

`src/compiler/10.frontend/core/types.spl` keeps unit declarations in a pool of
parallel arrays keyed by the bare unit name:

- `unit_decl_find(name)` (line 1089) scans `unit_decl_names` for the name only.
- `unit_decl_register_origin(...)` (line 1114) calls it, and when a row with
  that name already exists (lines 1117-1124) rewrites that row's role, short
  symbol, underlying type tag, alias target and legacy origin in place and
  returns the existing index.

There is no module in the key. Two modules that each declare `unit X` with
different underlying types, suffixes or roles therefore share one row, and
the declaration registered last wins for every module in the program.

## Why it matters

The pool feeds the unit checks (`SPL-UNIT-002` family) and the suffixed
literal checks (`unit_decl_find_by_suffix`). With one row per name, a module
can be checked against another module's unit: its literals take the other
unit's suffix and its arithmetic takes the other unit's underlying type. No
diagnostic reports the collision.

The standard library already declares the same unit name in more than one
family (`unit Count: i64` in `src/lib/common/types.spl`,
`src/lib/gc_async_mut/types.spl` and `src/lib/nogc_async_mut/types.spl`). Those
three agree today, so the overwrite is invisible; it stops being invisible the
first time two same-named units differ.

The Rust seed had the neighbouring defect (a plain `type Count = i64` alias in
one module was read as the unit `Count` declared in another) and it broke
every compiled run of the window-manager module graph. The self-hosted
compiler does not have that one: it expands aliases to their target per
module before the unit check (`20.hir/hir_lowering/type_aliases.spl`).

## Unproven

- Whether the parser's flat-AST tagging keeps a plain alias that collides
  with a unit name distinct from the unit.
- A module that declares the plain alias while also importing the unit.

## Proposed fix

Key the pool by (declaring module, name), resolve a use through the
declaration visible in the using module, and report a diagnostic when two
visible declarations of one unit name disagree. Red spec first: two modules
declaring `unit X` with different underlying types, each checked against its
own.
