# HIR lowering is quadratic in symbols-per-module (stage-4 blocker)

- **Status:** open, root cause identified and measured; fix NOT landed (see "Why no fix landed")
- **Filed:** 2026-07-28
- **Severity:** blocks the stage-4 bootstrap run (three-plus modules consume ~72% of total HIR phase time)
- **Area:** `src/compiler/20.hir/hir_types.spl` (`SymbolTable.define`),
  `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`
  (`register_glob_imported_symbols_depth`),
  `src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl`
  (`_bootstrap_hir_functions`)

## Measured regression

Per-module HIR lowering time from the live stage-4 run, anchored on a `module=`
word boundary (59 modules completed, 1,535,618 ms total phase time):

| module | now | prior run |
|---|---|---|
| `compiler.10.frontend.core.tokens` | 512,761 ms | 1,960 ms (262x) |
| `compiler.10.frontend.core.parser` | 391,773 ms | — |
| `std.io_runtime` | 197,793 ms | — |
| `lib.nogc_async_mut.database.test` | 183,198 ms | — |
| `lib.nogc_async_mut.database.bug` | 956 ms | — |
| other 56 modules | 9–956 ms | — |
| `compiler.10.frontend.core.lexer_struct` | 468 ms | 2,263 ms (FASTER) |

`heap_registry` grew to 64M entries this run vs 25M at the same module count in
the prior run (2.5x allocation), consistent with copy-churn rather than extra
hashing.

## Root cause 1 (MEASURED): `SymbolTable.define` is O(scope size) per call

`src/compiler/20.hir/hir_types.spl`. `Scope` is a **struct** (value type) whose
`symbols` field is a `Dict<text, i64>`. `define()` ends with:

```
var scope = self.scopes[self.current_scope.id]
var scope_syms = scope.symbols
scope_syms[name] = raw_id
scope.symbols = scope_syms
self.scopes[self.current_scope.id] = scope
```

Every one of those four lines copies the whole scope dictionary by value, so a
single `define()` costs O(|scope|) and defining N symbols into one module scope
costs **O(N²)**.

Confirmed empirically with a standalone probe replicating the block exactly
(`/tmp/perfprobe/define_quad.spl`, `bin/simple run`):

```
N=1000 ms=77
N=2000 ms=255
N=4000 ms=936
N=8000 ms=4596
```

~4x per doubling — clean quadratic. Extrapolating to ~80,000 defines gives
~460 s, matching the observed 512,761 ms for `tokens`.

This scales with **symbols-per-module**, which is exactly the property that
varies between same-directory siblings, and it explains the `heap_registry`
growth (each define allocates a fresh copy of the scope dict).

## Root cause 2: unmemoized recursive glob expansion (the regression delta)

`register_glob_imported_symbols_depth` in `module_lowering.spl`, widened by
`67024e9c0a51`, now additionally sweeps (a) the imported module's `exports` list
and (b) its **transitive star imports'** entire function/class/struct/enum/trait/
alias/const surface, and recurses through `export member.*` facades to depth 8
with **no visited set and no memoization**. Every symbol it touches is another
`define()` call, so N (and hence N²) grows sharply, and diamond-shaped facade
graphs re-sweep the same modules many times.

Evidence from the sibling probe pair the coordinator supplied — the two files
differ precisely in their **module-only (glob) imports**:

- `src/lib/nogc_async_mut/database/bug.spl` (956 ms) globs only
  `nogc_async_mut.database.query`.
- `src/lib/nogc_async_mut/database/test.spl` (183,198 ms) globs
  `nogc_async_mut.database.core`, `nogc_async_mut.database.query` **and
  `std.io`** — a large package facade whose transitive star-import expansion is
  now swept recursively.

Glob-import cost is reproducible on a standalone compile (wall time,
`bin/simple compile` on a 2-line file):

```
no imports                                  55 ms
use std.io                                 322 ms
use std.io + std.io_runtime + database.core 875 ms
```

Note the multiplier is on N; the quadratic in root cause 1 then squares it.

## Root cause 3: O(G²) rebuild of the global function accumulator per module

`lower_parser_module_unstub` (`module_lowering.spl`) runs, for **every** module
in bootstrap mode:

```
var flat_functions: [HirFunction] = []
var flat_fn_idx = 0
while flat_fn_idx < bootstrap_hir_function_count():
    flat_functions = flat_functions.push(bootstrap_hir_function_at(flat_fn_idx))
    flat_fn_idx = flat_fn_idx + 1
```

`_bootstrap_hir_functions` (`lowering_helpers.spl`) is a module-level **global**
accumulated across the whole run and reset only for the bootstrap entry module,
so `G` grows monotonically. Per the standing rule "seed `.push()` always clones —
`arr = arr.push(v)` is O(N²)", this rebuild is **O(G²) per module**, plus G
by-value `HirFunction` struct copies (each carrying a body). This cost scales
with **registry-size-at-time-of-lowering**, i.e. with a module's position in the
lowering order rather than any property of the module itself.

## Hypotheses REFUTED

1. **"`resolve_import_symbols` re-resolves the module from the registry for
   every imported symbol (O(symbols x registry-lookup))."** False. The registry
   lookup is already hoisted out of the per-symbol loop —
   `module_lowering.spl:921` does `val imported_mod = self.modules_by_name[imported_key]`
   once per *import statement*, and the per-item loop at 932-937 reuses it. The
   `imported_key`-instead-of-`Option<Module>` change carries a `text` key but
   dereferences it exactly once per import, not once per symbol.
2. **"`tokens` is slow because it has a huge imported-symbol surface."** False.
   `src/compiler/10.frontend/core/tokens.spl` has **zero** `use` lines — only
   `export` lines — so `resolve_import_symbols` is a no-op for it. Its
   same-package sibling `lexer_struct` (identical sibling sweep, *plus* real
   imports) lowers in 468 ms.
3. **"The extra `contains_key` + index read doubled hashing costs."** False; a
   uniform ~2x would show on all 59 modules, and 56 of them are 9–956 ms. The
   `contains_key`+index correctness fix is not implicated and must stay.
4. **"The symbol table accumulates across modules, so timings are
   order-dependent."** False for the symbol table specifically: `driver.spl:852`
   constructs a **fresh `HirLowering` per source file**. (Root cause 3's global
   accumulator *is* order-dependent, but the `SymbolTable` is not.)

## Still unexplained

`tokens` has no imports, so its N must come from
`resolve_package_sibling_symbols` sweeping the 48 siblings of
`compiler/10.frontend/core`. That sweep is symmetric with `lexer_struct`, which
is 1000x faster — so root cause 2 alone does not explain `tokens`. Root cause 1
(quadratic `define`) and root cause 3 (order-dependent global rebuild) do
explain it, but the specific N for `tokens` has not been counted directly.
Worth checking whether the compiler symlink module spellings
(`compiler.10.frontend.core.X` vs `compiler.frontend.core.X` vs
`compiler.core.X`, see `.claude/memory/reference_compiler_symlink_module_spellings.md`)
give `tokens` and `lexer_struct` different `pkg_prefix` values and therefore
different sibling sets in `resolve_package_sibling_symbols`.

## Why no fix landed

A perf fix needs a before/after number, and there is currently no cheap feedback
loop:

- `bin/simple compile src/compiler/10.frontend/core/tokens.spl` cannot lower the
  module in isolation (no `main`: "the entry script could not be lowered to a
  real `main` entry point").
- The deployed `bin/release/x86_64-unknown-linux-gnu/simple` could not be
  confirmed to contain the 2026-07-27 `module_lowering.spl` changes (its mtime,
  22:06, is after the commits, but no compiler diagnostic string literals are
  recoverable from the binary via `strings`, so provenance is unverified). Any
  before/after taken with it would be untrustworthy.
- The only faithful lane is the multi-hour stage-4 run, which was explicitly
  ruled out as a feedback loop.

Landing an unmeasured change into `module_lowering.spl` while a stage-4 build is
actively reading it was judged the worse risk.

## Recommended fixes, in order of leverage

1. **Root cause 1** — make `define()` O(1). The natural in-place forms are both
   rejected by the language today (see "Language limitation" below), so the
   viable shape is to flatten scope storage onto `SymbolTable` as a single-level
   `Dict<text, i64>` keyed by `"{scope_id} {name}"`, so the hot write is a
   single-level index assignment on a field. Touches `define`, `lookup`,
   `lookup_or_invalid`, `push_scope`/`pop_scope` and any reader of
   `scope.symbols`. Highest leverage: it fixes every module at once and is
   independent of import shape.
2. **Root cause 2** — add a per-`HirLowering` visited set of already-swept module
   keys to `register_glob_imported_symbols_depth`. Caveat to settle first:
   skipping a re-sweep of the same module can change which module's same-named
   *function* wins the scope slot (type symbols already dedupe first-write-wins,
   functions/consts/aliases do not), so verify the resolved symbol set is
   unchanged before landing.
3. **Root cause 3** — stop rebuilding `flat_functions` element-by-element; add a
   `bootstrap_hir_functions_all() -> [HirFunction]` accessor in
   `lowering_helpers.spl` and pass the global array directly.

All three must preserve the two standing correctness constraints: dict access
stays `contains_key` + index read (never `.get()` on struct values, never
`Dict.len()`), and import resolution must keep resolving the same symbol set
(current stage-4 state: unresolved = 0, parse = 0, HIR errors = 0).

## Language limitation found while probing

Both compact in-place forms that would fix root cause 1 directly are rejected:

- `self.scopes[0].symbols[name] = raw_id`
  -> `error: semantic: invalid assignment: complex field access not supported`
- `self.scope_syms[0][name] = raw_id`
  -> `error: semantic: invalid assignment: index assignment requires identifier
     or field access as container`

Per the repo rule on short, safe grammar forms that fail, this is recorded here
rather than silently worked around; nested index/field assignment is what a
value-type-dict language needs to avoid exactly this class of accidental
quadratic. Filed as part of this bug.

## Reproduction

- Quadratic `define` probe: `/tmp/perfprobe/define_quad.spl` (replicates the
  copy-modify-reassign block; run with `bin/simple run`).
- Glob-import cost probe: 2-line files with and without `use std.io`, timed with
  `bin/simple compile`.
