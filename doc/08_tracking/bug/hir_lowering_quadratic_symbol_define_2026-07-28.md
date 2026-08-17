# HIR lowering is quadratic in symbols-per-module (stage-4 blocker)

- Status: **RETIRED 2026-08-17 — all three root causes are refuted or fixed in
  current source.** Do not re-open this row for the live stage-3/stage-4 parse
  stall; that is a different defect (see
  `stage3_parse_stalls_at_tail_43_files_2026-08-17.md`).
- **Retirement independently corroborated 2026-08-17 (W1)** by grepping current
  source: the `GLB2` memo (`glob_expand_memo`) exists at
  `module_lowering.spl:1547-1572` with the field declared at
  `hir_lowering/types.spl:158`, initialised `:209/:247` and cleared per module
  `:312`; and `module_lowering.spl:1928` is `lowered_module.functions.values()`
  with no accumulator rebuild loop. Both matching the RETIRED verdict below.
- **The "one defect, two symptoms" link between this row, the stage-3 parse
  stall, and `lint_timeout_hwir_zca_rows_2026-08-17.md` is REFUTED.** The
  linter does not run the compiler frontend at all:
  `/usr/bin/grep -rln "parse_full_frontend\|compiler.frontend"
  src/compiler/tools/lint/ src/compiler/tools/fix/` returns **nothing**, and
  `src/compiler/tools/lint/_LintMain/lint_checks.spl` iterates over `lines`
  (3 `while ... < lines.len()` loops). So lint's superlinear cost shares no code
  path with `phase=parse` in stage 3 or with HIR lowering, and neither cost curve
  is evidence about the other. Anyone treating the lint fixture as a cheap
  reproducer for the stage-3 stall is measuring a different program.
- **The linter's superlinear term is real and reproducible in ~2 min**, which is
  useful for `lint_timeout_hwir_zca_rows_2026-08-17.md` (not for this row).
  Synthetic fixture: one function whose body is a single `[(text, i64, i64)]`
  array literal of N elements, one per line
  (generator + fixtures were scratch-only). Binary: the stale Rust seed
  `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, mtime
  2026-08-16 22:59, 59,536,728 bytes. Shared box under heavy load, so treat as an
  envelope:

  | N array elements | wall | minus ~12 s startup |
  |---|---|---|
  | 25 | 64 s | ~52 s |
  | 50 | 149 s | ~137 s |

  2x the elements costs 2.6x the work — superlinear (exponent ~1.4), and driven
  by ONE declaration's content, which is the shape that file's row reports. The
  offender is therefore inside the pure-Simple lint checks (or the seed
  interpreter executing them), not the parser.
- The earlier line here ("Root causes 2 and 3 remain unproven and unfixed; no fix
  landed", stamped "re-verified 2026-08-17 by source inspection") was WRONG on
  both counts. Re-verified by grepping current source, not by SHA ancestry:

  | root cause | verdict 2026-08-17 | proof in current source |
  |---|---|---|
  | 1. `SymbolTable.define` O(scope) copy | REFUTED on the native lane (see CORRECTION below; both forms linear, flat form slower) | unchanged, correctly so |
  | 2. unmemoized recursive glob expansion | **FIXED** | `glob_expand_memo` memo (`GLB2`) at `module_lowering.spl:1566-1573`, field declared `hir_lowering/types.spl:158`, initialised `:209/:247`, cleared per module `:312`. Re-entry at same-or-shallower depth returns early. |
  | 3. O(G²) per-module rebuild of the global fn accumulator | **FIXED** | `module_lowering.spl:1928` is now `val flat_functions: [HirFunction] = lowered_module.functions.values()` — the `while idx < bootstrap_hir_function_count(): flat_functions = flat_functions.push(...)` loop is gone. `bootstrap_hir_function_count` now has only two referencing files (`lowering_helpers.spl`, where it is defined, and an import line in `80.driver/driver_bootstrap.spl`); no per-module rebuild remains. |

  The interpreter-only offshoot this report discovered ("`self.<dict field>[k] = v`
  inside a `me` method copies the whole target dict, O(size) per write") also
  **no longer reproduces**. Probe: a class with a `Dict<text,i64>` field, prefilled
  to N, then 2000 writes to one hot key, run under
  `env SIMPLE_EXECUTION_MODE=interpreter bin/simple run` (binary: the stale Rust
  seed at `bin/simple`, mtime 2026-08-16 22:59 — stated because it is not current
  source):

  | N (prefill) | wall, 2000 hot writes | doc's 2026-07-28 figure |
  |---|---|---|
  | 1000 | 0.07 s | 387 ms |
  | 2000 | 0.07 s | 572 ms |
  | 4000 | 0.07 s | 929 ms |
  | 8000 | 0.10 s | 1775 ms |

  Flat, not quadratic (the residual 0.03 s at N=8000 is the linear prefill). No
  separate interpreter bug needs filing.

  Incidental observation from the same probe, NOT part of this row: under the JIT
  (`bin/simple run` with no `SIMPLE_EXECUTION_MODE`) `Dict.len()` returned `-1`
  while the interpreter returned the correct value. That is the old
  native-`Dict.len()` defect which `.claude/rules/code-style.md` records as fixed
  2026-08-01 — consistent with `bin/simple` being a pre-fix stale seed, so it is
  evidence about that binary, not a live regression.
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

## CORRECTION 2026-07-28 (second pass): root cause 1 is REFUTED on the stage-4 lane

**Do not implement "recommended fix 1" (flattening `SymbolTable` scope
storage). It was measured on the wrong execution engine and is a no-op at best,
a regression at worst.**

The probe below (`/tmp/perfprobe/define_quad.spl`) declares
`extern fn rt_time_now_monotonic_ms()`. That symbol is **not resolvable by the
JIT or the native backend**, so every run of it falls back to the tree-walking
interpreter:

```
[INFO] JIT compilation failed, falling back to interpreter:
  unresolved external symbol 'rt_time_now_monotonic_ms'
```

Stage-4 does not use the interpreter. `bootstrap.log` records
`Stage 4: compiling full CLI (main.spl) with bootstrap compiler`, i.e. the
**native** stage3 binary. Re-running the *exact* `define()` shape (both the
`self.symbols[raw_id] = symbol` write and the four-line copy-modify-reassign
tail) with a resolvable timer (`rt_time_now_unix_micros`), compiled with
`bin/simple compile --native`, gives (`/tmp/perfprobe/define_shape.spl`):

| N | current copy-modify-reassign | proposed flat `"{scope_id} {name}"` dict |
|---|---|---|
| 1000 | 2 ms | 2 ms |
| 2000 | 5 ms | 5 ms |
| 4000 | 10 ms | 15 ms |
| 8000 | 22 ms | 29 ms |

Both are **linear** (~2x per doubling). The proposed flat form is consistently
*slower* because it builds an interpolated composite key per call. Lookups
round-tripped correctly in both (`bad=0` at every N).

### What the interpreter measurement actually found (a real, separate defect)

The quadratic is real, but it is **interpreter-only**, and it is not the four
lines the report blamed. Isolated with `/tmp/perfprobe/me_recv.spl` and
`/tmp/perfprobe/me_read.spl` (2000 calls against a pre-filled dict):

| dict size | `me` method writing **that** dict | `me` method mutating a scalar field | `me` method writing a **different, small** dict | read via method |
|---|---|---|---|---|
| 1000 | 387 ms | 14 ms | 237 ms | 19 ms |
| 2000 | 572 ms | 14 ms | 228 ms | 20 ms |
| 4000 | 929 ms | 14 ms | 228 ms | 18 ms |
| 8000 | 1775 ms | 11 ms | 228 ms | 18 ms |

So under the tree-walk interpreter, `self.<dict field>[k] = v` inside a `me`
method copies the entire target dict (O(size) per write). Reads are O(1),
scalar-field writes are O(1), and writes to a *different* field-held dict are
O(1). Flattening does not dodge this — the flat dict is the one being written,
so it grows and gets copied identically (measured: flat was quadratic too under
the interpreter, 73/249/1002/5745 ms at N=1k/2k/4k/8k, matching the
copy-modify-reassign shape 90/286/1061/5299 ms).

This deserves its own bug against the interpreter's index-assign path; it makes
every interpreter-hosted symbol-table build accidentally quadratic. It does not
affect the native/JIT lane.

## Root cause 1 (interpreter-only — see CORRECTION above): `SymbolTable.define` is O(scope size) per call

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

## Still unexplained (updated 2026-07-28, second pass)

Two candidate explanations for `tokens` were checked and **eliminated**:

1. **"The 512 s window is really a batch of several modules."** No. Each
   `phase3:hir:file:start` window in `s4final.log` contains exactly one
   `[hir-lower] lower_module:start`. Verified for the `tokens` window
   (lines 52573-55084), `lexer_struct` (48605-52572), `database.bug`
   (59371-61217) and `database.test` (61218-62761) — all `nested=1`.
2. **"`tokens` does more lowering work."** No — it does *less*. The `tokens`
   window has 2,512 log lines and 10 `lower_function:start`; `lexer_struct`
   has 3,968 lines and 22, and is 1,096x faster. The 512 s is spent in an
   **uninstrumented, allocation-heavy region**: `heap_registry` grows by
   **26,035,397** entries across the `tokens` window versus **41,714** for
   `lexer_struct` (624x).

The strongest remaining structural difference between the two files:

| file | ms | heap_registry delta | `use` lines | `export` lines |
|---|---|---|---|---|
| `tokens.spl` | 512,761 | 26,035,397 | 0 | 30 (~200 names) |
| `lexer_struct.spl` | 468 | 41,714 | 3 | 2 |
| `database/test.spl` | 183,198 | 10,882,448 | 5 | 0 |
| `database/bug.spl` | 956 | 21,334 | 3 | 0 |

`tokens.spl` has no imports but the **largest re-export surface in its
package**, and its package (`src/compiler/10.frontend/core`) has 48 siblings,
5 of which carry `export ....*` facade forms. `resolve_package_sibling_symbols`
glob-sweeps all 48 siblings, and each sweep re-walks the `exports` list and
recurses to depth 8 **with no visited set** (root cause 2). A re-walking sweep
over a densely cross-exporting 48-module package is the only mechanism found
that produces a 26M-allocation blowup from a file that lowers 10 functions.
**Root cause 2 is therefore the leading hypothesis for `tokens`, not root
cause 1.** It is unproven — see "Why no fix landed (second pass)".

The original text follows for reference:

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

## Why no fix landed (second pass, 2026-07-28)

Root cause 1 was refuted (above), so its fix was deliberately not implemented.
Root causes 2 and 3 were **not** landed because no trustworthy in-lane feedback
loop could be built:

- **`bin/simple compile` measures the wrong compiler.** `bin/simple` is the
  Rust bootstrap seed (it prints the seed banner). Its HIR lowering is the Rust
  implementation, so it is completely insensitive to edits in
  `src/compiler/20.hir/**`. The glob-import numbers in this report
  (55 / 322 / 875 ms) were taken with it and therefore say nothing about
  `register_glob_imported_symbols_depth` in `.spl`.
- **The pure-Simple lane exists but the probe is swamped.** The stage3
  pure-Simple compiler is on disk
  (`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`, copied to
  `/tmp/claude_s4_compiler`) and does accept
  `compile <f> --format=smf` under `SIMPLE_BOOTSTRAP=1
  SIMPLE_COMPILER_PHASE_PROFILE=1`. On it, the two-line probes give
  `g_none` = 16 ms to end of HIR, but `g_io` (`use std.io`) never reaches HIR
  at all: it spends **176 seconds in phase2 parse of a single file**,
  `src/std/nogc_async_mut/io/driver.spl` (31,090 chars, +16,944 ms ->
  +193,636 ms). That is the known lexer O(n^2) parse defect, and it dwarfs and
  masks the HIR cost, so the glob probe cannot isolate root cause 2.
- **Symbol-set equivalence could not be verified.** Adding a visited set can
  change resolution: non-type symbols are **last-write-wins** in `define()`, so
  in a diamond (A -> B -> D, A -> C -> D) the current sweep order is
  A,B,D,C,D and a visited set makes it A,B,D,C. For any name defined in both
  `C` and `D` the winner flips. Proving "identical symbol set" needs a stage2
  rebuild plus a before/after symbol dump.

**The loop that would work** (untested, but the pieces are verified to exist):
`stage2-native-build` took ~3 minutes and `stage3-native-build` ~6 minutes in
`build/bootstrap/logs/x86_64-unknown-linux-gnu/`. Rebuilding stage2 from a
modified tree yields a pure-Simple compiler containing the change, which can
then be driven exactly as `~/.claude/jobs/4403a7d8/tmp/run_s4final.sh` does.
Any future attempt at root cause 2 or 3 should establish that loop first and
dump the registered symbol set before and after.

## Recommended fixes, in order of leverage

**Item 1 below is superseded — see the CORRECTION section at the top. Start
from item 2.**

1. ~~**Root cause 1**~~ (REFUTED on the native lane; do not implement) — make `define()` O(1). The natural in-place forms are both
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
  copy-modify-reassign block; run with `bin/simple run`). **Interpreter-only —
  its `rt_time_now_monotonic_ms` extern forces JIT fallback. Do not use it to
  judge the stage-4 lane.**
- Native-lane `define` probe: `/tmp/perfprobe/define_shape.spl`
  (`bin/simple compile --native`, times with `rt_time_now_unix_micros`).
  Compares the current shape against the proposed flat dict at N=1k/2k/4k/8k.
- Engine-semantics probes: `/tmp/perfprobe/me_recv.spl`,
  `/tmp/perfprobe/me_read.spl`, `/tmp/perfprobe/me_forms.spl`,
  `/tmp/perfprobe/field_dict.spl`, `/tmp/perfprobe/dict_raw.spl`.
  `dict_raw.spl` shows a bare `Dict<text,i64>` insert loop is linear on every
  engine, so `Dict` itself is not the problem.
- Glob-import cost probe: 2-line files with and without `use std.io`.
  **Timing them with `bin/simple compile` measures the Rust seed, not the
  `.spl` compiler.** Use `/tmp/claude_s4_compiler` (stage3) instead — but note
  it stalls 176 s in phase2 parse before reaching HIR.

## Language / runtime gaps recorded by this bug

1. Nested index/field assignment is not expressible (original report, below):
   `self.scopes[0].symbols[name] = v` and `self.scope_syms[0][name] = v` are
   both rejected.
2. **Interpreter copies a whole `Dict` on `self.<field>[k] = v` inside a `me`
   method** (measured above). Reads, scalar-field writes, and writes to other
   field-held dicts are all O(1); only the written dict is copied. This makes
   any interpreter-hosted accumulation into a class-held dict quadratic.
3. **Lexer/parser O(n^2)**: `src/std/nogc_async_mut/io/driver.spl` (31 KB)
   takes 176 s to parse on the stage3 pure-Simple compiler. Pre-existing (see
   `project_lexer_on2_perf_and_native_slice_2026-07-12`), but it is now the
   blocking obstacle to building a cheap HIR feedback loop.

## Third pass 2026-07-28: loop ESTABLISHED, cost LOCALIZED, two fixes REJECTED

### The feedback loop now exists (~4 min build + ~7 min measure)

The "only faithful lane is the multi-hour stage-4 run" claim above is wrong.

1. **Rebuild stage2 only** (~90-200 s, 692 modules) by replaying
   `build/bootstrap/stage3/<triple>/stage2-command.transcript` with the seed at
   `.../stage2-runtime-authority/simple` and `-o <scratch>`. That binary is
   pure-Simple and *does* contain `src/compiler/20.hir/**` edits.
2. **Measure on a REDUCED source set.** `native-build ... --source
   src/compiler/10.frontend --source src/app/cli --entry src/app/cli/main.spl`
   (entry must stay `src/app/cli/main.spl`: `SIMPLE_BOOTSTRAP_STAGE4=1` rejects
   any other entry, and the `[BOOTSTRAP-PHASE]` profile only exists on that
   lane). Do NOT pass `--entry-closure` — it prunes to the entry and nothing
   lowers. This reaches `tokens` in ~5 min and reproduces the defect
   **exactly**: heap delta 26,035,386, byte-identical to the full stage-4 run.

### The probes were silently mute (Trap D, now fixed)

`hir_module_perf_probe` existed but its gate was
`if (rt_env_get("X") ?? "") == "1":` inline — that evaluates FALSE on the
native bootstrap binary even when X=1. Binding the read to a `val` first, via
`hir_module_env_get`, makes it fire. Every probe in `module_lowering.spl`
depended on it, so the whole file was uninstrumented.

### Where the time actually goes (measured, `SIMPLE_HIR_PERF_PROBE=1`)

For `compiler.10.frontend.core.tokens` (162,331 ms total HIR):

| region | ms | allocations |
|---|---|---|
| `resolve_package_sibling_symbols` | **162,273** | **26,011,445** |
| everything else (declare, 10 function bodies, consts, tail) | 58 | 23,941 |

Per-sibling breakdown of that sweep (26 siblings):

| sibling | ms | allocations |
|---|---|---|
| **`compiler.10.frontend.core.__init__`** | **194,381** | **26,002,095** |
| `...core.types` | 33 | 2,710 |
| `...core.parser` | 12 | 609 |
| remaining 23 siblings | 2-5 each | < 1,200 each |

So **99.96 % of the cost is a single sibling: the package facade
`__init__.spl`**, whose `export <member>.*` lines are expanded transitively by
`register_glob_imported_symbols_depth` to depth 8.

### Why `tokens` and not `lexer_struct` — the symlink spelling split

`lexer_struct` lowers in 118 ms with a 34 ms sweep. The two files are NOT in
the same package as far as this code is concerned: `tokens` registers as
`compiler.10.frontend.core.tokens` and `lexer_struct` as
`compiler.frontend.core.lexer_struct`. Different `pkg_prefix` ⇒ different
sibling sets, and only the `10.frontend` spelling has `__init__` as a direct
sibling. (See `.claude/memory/reference_compiler_symlink_module_spellings.md`;
the earlier "worth checking" note was correct.)

### Two fixes built, measured, and REJECTED

Both were full stage2 rebuilds measured on the loop above.

1. **Visited set keyed by module key** (recommended fix 2 in this report).
   `heap+26,011,445` before → `heap+26,011,445` after — **byte-identical**.
   The memo never fires: the sweep does not revisit the same key. Recommended
   fix 2 as written is refuted.
2. **Visited set keyed by the module's FILE PATH** (spelling-independent).
   `heap+26,008,738` — still 26.0 M, no speedup, and it **changed the symbol
   set**: `tokens` ended with **2,317** symbols instead of **2,574**. Rejected
   on correctness.
3. Also tried and reverted as a no-op: changing `register_imported_symbol` /
   `register_imported_type_methods` / `find_reexport_source` from
   `Module` (by value) to `any`, on the theory that the by-value struct
   parameter deep-copied the module. No measurable change.

The memo results together say the expansion visits ~26 M allocations' worth of
**distinct** modules exactly once — i.e. expanding `core.__init__`'s star
exports transitively pulls essentially the whole module graph into the
importer's scope. Memoization cannot help; the fix has to be to stop the
package-facade sweep from recursing through `export <member>.*` into the
transitive world (or to build the facade surface once, globally, instead of
once per lowered file).

### Do not repeat

- Recommended fix 1 (flatten `SymbolTable`) — refuted in the second pass.
- Recommended fix 2 (visited set) — refuted here, both key choices.
- The `Module`-by-value theory — refuted here.
- `resolve_import_symbols` / per-symbol registry lookup — refuted in pass 1.
- The whole `lower_module` body-lowering path: 58 ms of 162,331 ms.

### Instrumentation

Level-gated and default-off, in `module_lowering.spl`:
`SIMPLE_HIR_PERF_PROBE=1` (`[HIR-PERF] t= heap= <phase>`) and
`SIMPLE_HIR_SYMBOL_DUMP=1` (`[HIR-SYMS] <module>\t<name>\t<kind>\t<owner>`,
for before/after symbol-set equivalence diffs). The symbol-set count is the
cheap equivalence check: `unstub:flat_symbols:done n=` per module.

## Fourth pass 2026-07-28 (lane R4): ROOT CAUSE FOUND, FIXED, MEASURED — 26x

**Status: root cause identified and proven. Fix built, measured, and verified
symbol-set-identical. NOT landed — see "Why not landed" below. Patch:
`doc/08_tracking/bug/patch/hir_facade_selfhop_2026-07-28.patch` (applies cleanly
to `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`).**

### The mechanism (it is NOT the sweep, it is a self-recursion inside the chase)

`resolve_package_sibling_symbols` sweeps `compiler.10.frontend.core.__init__`.
That facade **declares nothing** and carries **447 `export` decls / 1,367 export
items**, only ONE of which is a star form (`export dangerous_keywords.*`, line
479). So for every one of the 1,367 names:

1. `register_glob_imported_symbols_depth` calls `register_imported_symbol`.
2. All seven `has_*` checks miss (the facade declares nothing), so it calls
   `find_reexport_source(__init__, ..., wanted, 0)`.
3. `find_reexport_source` walks the facade's **entire 1,367-item export list**
   looking for `exp_local == wanted` — and finds the very item the caller is
   already standing on.
4. At that item, `hir_module_declares_item` is false, so it runs
   `find_reexport_source(facade_mod, facade_name, exp_source, depth + 1)`.
   For a plain `export foo` (no alias) `exp_source == wanted`, so this is a
   **self-recursion with IDENTICAL arguments** and only a smaller depth budget.
   It re-scans the list from 0, rediscovers the same item, and recurses again —
   all the way to the depth-8 bound, then re-scans the tail on every unwind.

Cost per name ≈ 14 x E; total ≈ 14 x E² with a `split(":")` array allocation on
every single visit. Arithmetic check against the measurement:
26,002,095 allocs / 1,367 names = **19,022 visits per name = 13.9 x E**. The
model predicts the observed number to within 1%.

This also explains every refuted hypothesis: the blowup is not in the *sweep*
(so a visited set over swept modules cannot fire), not in `define()` (only 58 ms
of 162,331 ms is real lowering), and not module-copy cost.

### The fix (two changes, both provably result-preserving)

In `find_reexport_source`, non-star export branch:

1. **Skip the self-hop.** Only chase when `exp_source != wanted`. A call with
   identical `(facade_mod, facade_name, wanted)` at `depth+1` explores a strict
   subset of what the current invocation already explores (same imports loop,
   same export list, same DFS order, strictly smaller budget), so it can never
   contribute a hit the outer call does not already find. Kills the ~14x
   multiplier.
2. **Do not `split(":")` unless the item actually is an alias** (`"src:local"`).
   Kills the per-visit array allocation on the remaining O(E²) scan.

`find_reexport_source` is a **pure function** — it defines no symbols — so the
only way it can change the symbol set is via its return value. Both changes are
argued above to leave the return value unchanged, and that is confirmed
empirically below.

### Measured before/after (stage2 rebuild loop, same machine, load ~67/32 cores)

Loop: rebuild stage2 from the modified tree with the seed (263 s), then
`native-build --source src/compiler/10.frontend --source src/app/cli --entry
src/app/cli/main.spl` under `SIMPLE_BOOTSTRAP_STAGE4=1
SIMPLE_HIR_PERF_PROBE=1 SIMPLE_HIR_SYMBOL_DUMP=1`.

`compiler.10.frontend.core.tokens`, `resolve_imports:done` -> `siblings:done`:

| | ms | allocations | symbols |
|---|---|---|---|
| before | 206,210 | 26,011,720 | 2,574 |
| after | **7,817** | **1,192,854** | **2,574** |
| ratio | **26.4x faster** | **21.8x fewer** | unchanged |

(The baseline reproduces the third pass exactly: 26,011,720 vs 26,011,445
allocations, and n=2,574 both times. The larger ms is machine load, not a
different defect.)

**Whole-run progress in the same wall-clock window: 80 modules -> 994 modules
(12.4x).** Zero HIR errors in both runs. Stage-4 now moves well past `tokens`;
the run ended only on the harness `timeout`, mid-module, with no error.

### Proof the resolved symbol set is unchanged

`SIMPLE_HIR_SYMBOL_DUMP=1` emits `<module>\t<name>\t<kind>\t<owner>` per
registered symbol. Comparing the **first-pass dump of every one of the 79
modules both runs completed**: 47,273 symbol rows on each side,
**byte-identical** after sort. `tokens` alone: 2,574 rows, byte-identical.
Per-module `flat_symbols:done n=` counts: **0 mismatches across all 80**.

Two traps when reproducing this comparison:
- Grep the module path **anchored** (`awk -F'\t' '$1==path'`). An unanchored
  `grep tokens.spl` also matches `cmm_tokens.spl` and invents 2,149 phantom
  differences.
- Compare only modules whose `flat_symbols:done` line is present in the *same
  frozen snapshot*, and only the **first** dump block per module — a run that
  gets further re-lowers some files in a later pass, which looks like 2,933
  extra symbols when it is just the faster run doing more work.

### Residual (follow-up, not a blocker)

The self-hop is gone but the scan is still O(E²) per importing file: 8 modules
still pay >1M allocations each (`src/compiler/__init__.spl` 11,883 ms /
1,452,421 allocs; `ast_types`, `parser_cli` and others at ~1,193,500), together
31% of all sibling-sweep time. The structural fix is to build the facade's
`local -> source` export index **once per facade module** and reuse it, instead
of rescanning the export list per wanted name. Filed as follow-up; the 26x above
is what unblocks stage-4.

### Why not landed

`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` in the shared
working copy carries **another session's uncommitted change** (a
`m.type_aliases.contains_key(name)` arm added to `hir_module_declares_item`).
`jj`/`git` commit at file granularity, so committing this fix would also land
that untested WIP under this commit — exactly the clobber the VCS rules forbid.
The fix is therefore parked as an applies-cleanly patch; land it with
`git apply doc/08_tracking/bug/patch/hir_facade_selfhop_2026-07-28.patch` once
that WIP is committed or reverted by its owner.

### Do not repeat (added)

- Do not look for the cost in `resolve_package_sibling_symbols` itself, in
  `define()`, or in module-copy overhead. It is 100% inside
  `find_reexport_source`'s export-list walk.
