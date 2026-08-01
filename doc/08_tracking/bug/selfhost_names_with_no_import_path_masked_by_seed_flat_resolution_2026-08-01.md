# Self-hosted stage3 "unresolved name": names that have NO import path at all, masked by the Rust seed's flat resolution

Status: All 545 unresolved-name errors of the 2026-08-01 census are now classified.
319 closed (104 by 70bd64128eb; 215 by 5d3223e329e / b9940d8ca5b / e57d171eba2 / f93c9b26232),
126 are class (A) and need no action, 66 remain as class (B) one-liners, 9 are separate defects.
See the full-classification section at the end.
Date: 2026-08-01
Area: compiler / name resolution (HIR lowering), compiler source hygiene

## Summary

The residual stage3 `unresolved name` class is not one defect. It splits into two,
and only one of them is a resolver defect:

- **(A) glob re-export propagation** — the name IS reachable, through a glob
  (`use X.*`) whose target reaches it via its own named or glob imports. This half
  was closed by `GLB1` (unconditional named-item half) and by `3226faaf9eb`
  (memoized + ungated nested-glob recursion). Verified fixed here — see
  "Repro 1" below.
- **(B) no import path at all** — the name is declared in exactly one module,
  and *no* module on the importer's import graph names it or globs its declaring
  module. Under the self-hosted resolver this can never resolve. It compiles
  through the Rust seed only because the seed resolves flat over the whole loaded
  closure. No resolver change can fix (B); the source is genuinely missing an
  import.

This document records (B), its proof, and the fix.

## Class (B) instances fixed here

| file | name | count in census |
|---|---|---|
| `src/compiler/70.backend/backend/vulkan_backend.spl` | `compileerror_backend_error` | 89 |
| `src/compiler/10.frontend/treesitter/outline.spl` | `span_new` | 5 |
| `src/compiler/10.frontend/treesitter/outline_decls.spl` | `span_new` | 5 |
| `src/compiler/10.frontend/treesitter/outline_members.spl` | `span_new` | 3 |
| `src/compiler/10.frontend/desugar/desugar_async.spl` | `span_new` | 1 |
| `src/compiler/10.frontend/desugar/poll_generator.spl` | `span_new` | 1 |

Fix: add the missing named import. Each addition mirrors an existing in-tree
idiom, adds exactly one name, and points at the sole declaring module — so it
cannot swap an import winner (there was no winner: the name was unresolved).

## Proof that these have no import path

`compileerror_backend_error`
- Declared in exactly one module: `src/compiler/70.backend/backend/backend_types.spl:379`.
- `vulkan_backend.spl` has three globs — `compiler.mir.mir_data.*`,
  `compiler.backend.backend_api.*`, `compiler.backend.vulkan_type_mapper.*` —
  and **none of the three source files contains the string
  `compileerror_backend_error` at all**, so no glob hop of any depth can reach it.
  (`backend_api.spl` named-imports `compileerror_target_unsupported`, a different
  symbol.)
- `use compiler.backend.backend_types.*` elsewhere in the tree resolves to
  `src/compiler/70.backend/backend_types.spl`, a *different* module that does not
  declare this function.
- **In-tree control:** its sibling `cuda_backend.spl:9` carries
  `use compiler.backend.backend.backend_types.{compileerror_backend_error}`
  explicitly — and `cuda_backend.spl` has **zero**
  `unresolved name: compileerror_backend_error` in the same census that gives
  `vulkan_backend.spl` 89. Same directory, same globs, one has the import and
  passes, the other does not and fails.

`span_new`
- Declared in exactly one module: `src/compiler/10.frontend/block_types.spl:258`.
- `/usr/bin/grep -rn "use .*{[^}]*span_new" --include=*.spl src/compiler/` → **0 hits**:
  no module anywhere in the compiler names it in an import list.
- `/usr/bin/grep -rn "^use .*block_types\.\*" --include=*.spl src/compiler/` → **0 hits**:
  no module globs its declaring module either.
- The near-miss names that *are* imported (`flat_span_new`, `lex_span_new`) are
  different functions in different modules.

## Minimal repros (12 lines, both run against a stage2 built at the tip)

Build: seed → stage2 at the current tip
(`728 compiled, 0 cached, 0 failed`, 204.8 s). Invocation must be a **bare
positional `.spl`**; `native-build --entry X` delegates to the Rust seed codegen
and is therefore not a valid probe of the self-hosted resolver.

Repro 1 — second-hop glob (class A). **RESOLVES at the tip.**

```
# probe/defs.spl
enum MyEnumX:
    A
    B
fn my_free_fn() -> i64:
    7

# probe/mid.spl        (declares its own symbol AND globs defs)
use probe.defs.*
struct MidOwn:
    v: i64

# leaf.spl
use probe.mid.*
fn main() -> i64:
    val e = MyEnumX.A
    my_free_fn()
```

`SIMPLE_BOOTSTRAP=1 <stage2> native-build --mode dynload -o out leaf.spl`
emits `[bootstrap-real-llvm] function probe.defs.my_free_fn` — positive
evidence the name resolved and was lowered. Against a **pre-`3226faaf9eb`**
stage2 the same input emits
`HIR lowering error in leaf.spl: unresolved name: MyEnumX` and
`... unresolved name: my_free_fn`.

Repro 2 — no import path (class B). **STILL FAILS at the tip, correctly.**

```
# probe2/defs2.spl
fn my_free_fn2() -> i64:
    7

# probe2/user2.spl     (pulls defs2 into the compiled closure)
use probe2.defs2.{my_free_fn2}
fn user_calls() -> i64:
    my_free_fn2()

# flat.spl             (calls my_free_fn2 with NO import for it)
use probe2.user2.{user_calls}
fn main() -> i64:
    val a = user_calls()
    a + my_free_fn2()
```

→ `error: in-process native-build: HIR lowering error in flat.spl: unresolved name: my_free_fn2`

This is the correct behaviour and is exactly the shape of every class-(B) site
above: the declaring module is in the closure, but the importer never names it.
The Rust seed accepts the same source because it resolves flat over the loaded
closure.

## Census provenance (read this before quoting the numbers)

The per-name counts quoted around this lane — `BackendKind` 174,
`compileerror_backend_error` 89, `HirExprKind` 40, `int_to_str` 25,
`span_new` 15 — come from
`build/bootstrap/release_beta_verify/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(2026-08-01 03:44), which totals **545 `unresolved name` + 3345 `unresolved type`**.
They are the distribution of the **545** census, not of the later 161 one; the
two were conflated in lane hand-off. Enumerate classes before drilling:

```
/usr/bin/grep -oE 'unresolved (type|name)' "$LOG" | sort | uniq -c
```

Whole-class per-file attribution from that log (8 files carry 341 of 545):

```
 92 70.backend/backend/vulkan_backend.spl : BackendKind
 89 70.backend/backend/vulkan_backend.spl : compileerror_backend_error
 80 70.backend/backend/cuda_backend.spl   : BackendKind
 40 semantics/resolve.spl                 : HirExprKind
 22 frontend/core/_Ast/decl_nodes.spl     : int_to_str
  8 frontend/treesitter/heuristic.spl     : Span
 13 frontend/treesitter/outline*.spl      : span_new
  2 frontend/desugar/{desugar_async,poll_generator}.spl : span_new
```

Class-(A) members of that list and their glob hop, for the record:
`BackendKind` via `backend_api.spl`'s named import; `int_to_str` via
`ast_stmt.spl:10`'s named import; `Span` via `lexer.spl:21`'s named import;
`HirExprKind` via `hir.spl`'s `export use compiler.hir.hir_definitions.*`.

## Traps hit while measuring this

- A stage3 run under `SIMPLE_BOOTSTRAP=1` **without** `SIMPLE_BOOTSTRAP_STAGE4=1`
  runs a weaker pipeline; a "0 unresolved / 0 failed" result from it is not
  evidence that names resolve. See
  `doc/08_tracking/bug/stage3_clean_baseline_is_bootstrap_flat_artifact_2026-08-01.md`.
- `native-build --entry X` is Rust-seed codegen; only a bare positional `.spl`
  exercises the self-hosted front end.
- Default `grep` in this environment is ugrep. Pin `/usr/bin/grep` for counts.
- A resolution-count census is blind to *swapped import winners*: a name that
  resolves to the wrong provider emits no `unresolved` line. Class (A) fixes that
  widen glob visibility need an identity check, not a count check.

## 2026-08-01 — full classification of the 545 census (all 145 unique file/symbol pairs)

Status of this pass: **all 545 errors classified**; 215 more closed (four scoped
commits, below). Every number in this section comes from the **545 census**
(`build/bootstrap/release_beta_verify/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`,
2026-08-01 03:44) — not from the separate later "161" census.

### The 545 errors are only 145 unique `(file, symbol)` pairs

That is the real work unit; the count column is just how many call sites each
pair has. Method: a static reachability check per pair — find every declaring
module in `src/`, then test whether the using file has (a) a named import of the
symbol, (b) an `export use M.*` / `export use M.{sym}` re-export chain reaching a
declaring module, or (c) neither.

Distribution over the 545 error lines:

| class | error lines | unique pairs | action |
|---|---|---|---|
| (A) reachable via a glob re-export hop | 126 | 51 | none — closed by `GLB1` + `3226faaf9eb` |
| (B) no import path at all | 102 | 50 | add one named import per site |
| already named-imported at tip | 308 | 36 | none — includes the 104 fixed by `70bd64128eb` and the 215 fixed here |
| neither — a *different* defect | 9 | 8 | filed below |

### Two class-(A) attributions in the section above are WRONG — corrected here

The earlier note "`BackendKind` via `backend_api.spl`'s named import;
`int_to_str` via `ast_stmt.spl:10`'s named import" is incorrect. Both are
class **(B)**. A plain `use` inside a glob target is **not** a re-export, and one
of the two module paths does not resolve to a file at all:

- `BackendKind` — PROVED class (B). `vulkan_backend.spl` / `cuda_backend.spl` /
  `lean_backend.spl` glob `compiler.backend.backend_api.*`, which maps to
  `src/compiler/70.backend/backend_api.spl` — **that file does not exist**
  (`git ls-tree -r --name-only $TIP | /usr/bin/grep backend_api.spl` returns
  exactly one path, `src/compiler/70.backend/backend/backend_api.spl`, which is
  the module `compiler.backend.backend.backend_api`). Even that file imports
  `BackendKind` with a plain `use` at line 28, not `export use`, so it re-exports
  nothing. The other globs (`compiler.mir.mir_data.*`,
  `compiler.backend.vulkan_type_mapper.*`) do not contain the string.
  **In-tree control:** 24 files in the same directory name
  `compiler.backend.backend.backend_types.{BackendKind, ...}` explicitly —
  including the structural analogues `hip_backend.spl` and `opencl_backend.spl`,
  which have **zero** `unresolved name` lines in the same log.
- `int_to_str` — PROVED class (B). `decl_nodes.spl` / `module_state.spl` glob
  `compiler.core.ast_stmt.*`. `ast_stmt.spl:10` is
  `use compiler.core.types.{int_to_str}` — a plain `use`, and `int_to_str` does
  not appear in that module's explicit `export` lists (lines 537-545 export only
  `STMT_*` / `stmt_*`). So the glob cannot carry it.
  **In-tree control:** 17 compiler files import
  `compiler.core.types.{int_to_str}` by name and none has an `int_to_str` error.
  The two other in-tree declarations (`35.semantics/lint/stub_impl.spl:94`,
  `35.semantics/lint/wide_public.spl:44`) are file-local private copies with an
  identical `fn int_to_str(n: i64) -> text` signature and no importers, so naming
  `compiler.core.types` cannot change behaviour under last-write-wins.

`HirExprKind` (40) **is** genuine class (A), and the hop is nameable:
`resolve.spl:16` globs `compiler.hir.hir.*`, and `20.hir/hir.spl:10` is
`export use compiler.hir.hir_definitions.*`, where `HirExprKind` is declared
(`hir_definitions.spl:437`). All 13 `Hir*` symbols in `resolve.spl` (59 error
lines) ride that same hop. No action.

### Class (B) closed in this pass — 215 error lines, four scoped commits

| commit | files | symbols | error lines |
|---|---|---|---|
| `5d3223e329e` | `vulkan_backend.spl`, `cuda_backend.spl`, `lean_backend.spl` | `BackendKind`, `compileoptions_default_options` | 177 |
| `b9940d8ca5b` | `_Ast/decl_nodes.spl`, `_Ast/module_state.spl` | `int_to_str` | 25 |
| `e57d171eba2` | `treesitter/outline.spl`, `treesitter/outline_members.spl` | `blockoutlineinfo_opaque`, `prelexinfo_empty`, `span_empty` | 3 |
| `f93c9b26232` | `placeholder_lambda.spl`, `effect_pass.spl`, `_MirLoweringExpr/{expr_dispatch,switch_operators_calls}.spl` | `EXPR_INTERPOLATED_STRING`, `effectsolver_create`, `effectsolver_solve`, `MirPlace` | 10 |

Every edit names **one declaring module** and adds names to an import line the
file already has (or, for `MirPlace`, the facade two sibling files already use),
so no import winner can be swapped — consistent with the rule that
`Function`/`Const`/`TypeAlias` are last-write-wins in `SymbolTable.define`.

### Class (B) remaining — 66 error lines, sole declaring module each

These are proved-unreachable and each has exactly one declaring module, so the
fix is one named import. Left unlanded in this pass:

| symbol | using file | declaring module | n |
|---|---|---|---|
| `expr_interpolated_string` | `10.frontend/desugar/placeholder_lambda.spl` | `compiler.core.ast_expr` (re-exports `_AstExpr/accessors.spl:16`) | 2 |
| `parser_parse_type_with_union` | `10.frontend/core/parser_decls_use.spl` | `compiler.frontend.core.parser` — **check for an import cycle first** | 3 |
| `parse_fn_lambda_after_kw` | `10.frontend/core/parser_stmts.spl` | `compiler.frontend.core._ParserPrimary.primary_expr` | 3 |
| `CodegenMode`, `CodegenPipeline` | `70.backend/backend/compiler.spl` | `compiler.backend.codegen` | 4 |
| `blockoutlineinfo_opaque` (2nd site) | `10.frontend/treesitter/outline.spl` | done | — |
| `DriverManifestAttrKind` | `50.mir/_MirLowering/module_lowering.spl` | `compiler.common.attributes` (already imported for `FunctionAttr`) | 2 |
| `MirPlace` (`switch_operators_calls`) | done | — | — |
| `vhdl_clock_domain_from_metadata` | `70.backend/backend/_VhdlProcess/process_codegen.spl` | `compiler.mir.mir_instruction_support` | 1 |
| `mir_fold_binop` | `60.mir_opt/_OptimizationPasses/engine.spl` | `compiler.mir.mir_instruction_graph` | 1 |
| `GpuBarrierScope`, `GpuMemoryScope` | `50.mir/_MirLoweringExpr/method_calls_literals.spl` | `compiler.mir.mir_instruction_support` (`GpuBarrierScope` has 3 declaring modules — confirm before landing) | 2 |
| `make_core_decl` | `10.frontend/core/_Ast/module_state.spl` | `compiler.core.ast_types` (already imported) | 1 |
| `decl_aop_advice`, `decl_arch_rule` | `10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl` | `compiler.core._Ast.decl_nodes` | 2 |
| `get_shb_interface_hash` | `80.driver/driver_aot_smf_output.spl` | `compiler.driver.cache.cache_validator` | 1 |
| `CompileMode` | `80.driver/driver_source_pipeline_loading.spl` | `compiler.common.driver_core_modes` | 1 |
| `effectsolver_*` | done | — | — |
| `rt_file_delete`, `rt_getpid`, `rt_file_rename`, `rt_process_exists` | linker/codegen/daemon_sdk | `runtime/simple_core/*` — these are runtime externs; see "different defect" below | 5 |
| `dir_walk`, `file_write_bytes` | `70.backend/linker/{smf_getter,link}.spl` | ambiguous (7-10 declaring modules) — **do not guess** | 2 |

The remainder of the 66 is the long tail of one-off sole-module symbols with the
same shape.

### Neither (A) nor (B) — separate defects, filed here

These are **not** import defects. Adding an import would be wrong.

1. **`use lazy` named imports are silently dropped — FIXED 2026-08-01.** PROVED.
   `80.driver/driver.spl:20` and `80.driver/driver_types.spl:19` both carry
   `use lazy compiler.backend.backend.interpreter.{InterpreterBackendImpl}`, and
   the census still reported `unresolved name: InterpreterBackendImpl` for both.
   The name IS imported; the `lazy` modifier dropped it. 2 error lines. This is a
   resolver defect, not source hygiene. **See the dedicated section below.**
2. **`_` and `_1` are resolved as ordinary names.** 8 error lines across
   `40.mono/monomorphize/engine.spl` (4), `70.backend/backend/vulkan/spirv_builder.spl`
   (2 + one `_1`), `70.backend/linker/linker_wrapper_helpers.spl` (1),
   `99.loader/loader/compiler_sffi.spl` (1). A wildcard pattern binding is
   leaking into name resolution.
3. **`error` and `panic` are treated as user names, not builtins.** 12 + 9 error
   lines across six backend/type-mapper files. Their only in-tree declarations
   are unrelated local functions in `src/app/**` and `src/runtime/**`. The
   self-hosted front end is not pre-registering these intrinsics.
4. **Block-DSL body identifiers escape into name resolution.** `15.blocks/blocks/builtin_blocks_math.spl`
   (`x`, `y`, `pred`, `mse`, `model`, `target`, `test_data` — 7) and
   `builtin_blocks_shell.spl` (`ls`, `la` — 2). These are tokens inside block
   literals, never expressions.
5. **`nilnilnilnilnilnil`** in `10.frontend/core/parser_preprocessor.spl` — a
   concatenation artifact, declared nowhere. 1 error line. Likely an
   interpolation/lowering bug producing a synthetic identifier.
6. **`float`** in `src/std/common/format.spl` (2) — a builtin type name reaching
   the value namespace.
7. `selected` (`stage4_symbol_closure.spl`) and `pred`
   (`builtin_blocks_math.spl`) are declared **in the same file** that reports
   them unresolved — a scoping defect, not a missing import. 2 error lines.

### Method notes (reusable)

- The decisive discriminator between (A) and (B) is `export use` vs plain `use`
  in the glob target. An analyzer that only greps `^use` misclassifies
  `HirExprKind` as (B); one that treats any named import in a glob target as a
  re-export misclassifies `BackendKind` and `int_to_str` as (A). Both mistakes
  were made and corrected in this lane.
- `use lazy M.{sym}` must be parsed as a named import or you will misreport
  `InterpreterBackendImpl` as class (B) and "fix" an import that already exists.
- Path-based counting double-counts: 17 `src/compiler/<name>` entries are
  symlinks to the numbered layer dirs (`backend -> 70.backend`, `hir -> 20.hir`,
  …). Canonicalise through the symlink before indexing declarations.
- A module path that maps to no file is silent. `compiler.backend.backend_api`
  has no file; the glob simply contributes nothing, and nothing warns.


---

## Defect #1 in full: `use lazy M.{sym}` named imports dropped from the entry closure

Status: **FIXED 2026-08-01.** Fix in `src/compiler/80.driver/driver_source_loading.spl`.
Regression cover: `test/01_unit/compiler/driver/lazy_named_import_closure_spec.spl`.

### Root cause (PROVED) — it is not HIR lowering

The original filing said "HIR lowering does not register it". That is the
symptom, not the cause. HIR lowering is entirely `lazy`-agnostic:
`resolve_import_symbols` (`20.hir/hir_lowering/_Items/module_lowering.spl:1050`)
never reads `imp.is_lazy`, and the parser stores the named list correctly
(`10.frontend/core/parser_decls_use.spl:124-187` collects `imported_names`, then
`decl_set_lazy` only flags the decl). The names survive all the way into
`ParserImport.items`.

The drop is one line earlier in the pipeline, in the **entry-closure scanner**:

    src/compiler/80.driver/driver_source_loading.spl:446
        if line.starts_with("use lazy "):
            continue

This is the only closure scanner in the tree (callers:
`app/io/_CliCompile/compile_targets.spl:618` BFS and
`80.driver/driver_source_pipeline_loading.spl:197` phase1 load_sources). Skipping
the line means the module is never loaded, so in `resolve_import_symbols`
`imported_key == ""`, the whole `if imported_key != ""` block is skipped, and
**nothing is registered** — no error, no warning. The name then reports
`unresolved name`. The Rust seed masks it entirely because it resolves flat over
the loaded closure.

### Reproduction

Interpreter lane, `bin/simple_seed run` (rebuilt from origin tip today), calling
`_driver_entry_import_module_paths` directly, one process per measurement. The
`use lazy` / plain contrast is the whole diagnosis:

| import form | before | after |
|---|---|---|
| `use M.{sym}` | `[M]` | `[M]` |
| `use lazy M.{sym}` | **`[]`** | `[M]` |
| `use M (sym)` | `[M]` | `[M]` |
| `use lazy M (sym)` | **`[]`** | `[M]` |
| `use M.{sym as alias}` | `[M]` | `[M]` |
| `use lazy M.{sym as alias}` | **`[]`** | `[M]` |
| `use M.*` | `[M]` | `[M]` |
| `use lazy M.*` | `[]` | `[]` (intended) |
| `use M` | `[M]` | `[M]` |
| `use lazy M` | `[]` | `[]` (intended) |
| `use M as a` | `[M]` | `[M]` |
| `use lazy M as a` | `[]` | `[]` (intended) |
| `export use M.{sym}` | `[M]` | `[M]` |
| `export use lazy M.{sym}` | **`[lazy]`** | `[M]` |
| `pub use M.{sym}` | `[M]` | `[M]` |
| `pub use lazy M.{sym}` | **`[lazy]`** | `[M]` |
| `import M.{sym}` | `[M]` | `[M]` |
| `import lazy M.{sym}` | **`[lazy]`** | `[M]` |

**Sibling defect found by enumerating the family:** `export use lazy`,
`pub use lazy` and `import lazy` never matched the `use lazy ` prefix test at
all. They fell through to the plain arms and collected the literal module path
**`"lazy"`** — a phantom module that maps to no file and therefore contributes
silently nothing, while the real module was lost. Zero in-tree instances today,
so this was latent, but it is fixed by the same change.

### The fix

Strip the `lazy` modifier after the `use`/`pub use`/`export use`/`import`
prefix, then skip **only** when the lazy import carries no explicit name list.

- **Named** (`M.{a, b}` / `M (a, b)`) — a static name dependency. The names must
  resolve, so the module is collected like any other import.
- **Name-less** (`use lazy M`, `use lazy M.*`, `use lazy M as a`) — genuinely
  dynamic, still skipped.

That split matches in-tree usage exactly (see blast radius): every one of the 9
name-less lazy imports is an MCP deferred tool module (#LAZY-002 startup cost),
and every one of the 36 named lazy imports references its names in code.

### Blast radius (PROVED, `/usr/bin/grep`, whole tree at the tip)

45 lazy import lines across 19 files:

| form | count | effect of fix |
|---|---|---|
| `use lazy M.{...}` | 28 | now collected |
| `use lazy M (...)` | 8 | now collected |
| `use lazy M` (name-less) | 9 | unchanged, still deferred |
| `use lazy M.*` | 0 | — |
| `export use lazy` / `pub use lazy` / `import lazy` | 0 | latent fix |

All 9 name-less sites are in `src/lib/nogc_async_mut/mcp/main_lazy.spl`.

### Import-winner analysis (required by `SymbolTable.define` semantics)

`SymbolTable.define` (`20.hir/hir_types.spl:246`) is first-write-wins only for
`Class`/`Struct`/`Enum`/`Trait`; `Function`/`Const`/`TypeAlias` are
**last-write-wins**, so a change in *when* a symbol registers can swap a winner.

The fix newly registers **49 distinct names** (the named items of the 36 lazy
imports). Provider counts, by declaring module:

- 40 of 49 have 0 or 1 declaring module — cannot swap.
- 3 are first-write-wins kinds and so cannot swap even when contested:
  `Size` (5, class/struct), `FixApplicator` (2, class), `BackendError` (2, enum/struct).
- **6 are last-write-wins functions with more than one provider** and are the
  residual risk: `read_file` (8), `compile_native` (3),
  `aot_native_project_with_backend` (3), `aot_native_file_with_backend` (3),
  `check_short_grammar_refactor` (2), `check_formatting` (2).

Bounding measurement (PROVED): **all 10 modules** named by the lazy imports
already have at least one NON-lazy importer elsewhere in the tree
(`compiler.mir.mir_instructions` 100, `compiler.driver.driver` 29,
`compiler.backend.backend_types` 19, `compiler.tools.fix.rules` 43,
`compiler.backend.linker.lib_smf_writer` 4, `compiler.driver.driver_api` 3,
`compiler.backend.backend.interpreter` 3, `compiler.tools.formatter.main` 1,
`compiler.tools.fix.main` 1, `app.compile.native` 1). So the fix introduces **no
new provider** into the registry — every one of these modules was already
loadable into a closure. INFERRED from that: the residual exposure is ordering
within closures that could already contain these modules, not a new contested
name. Not verified by a full stage3 census; the 6 names above are the list to
check if a winner swap is later observed.

### Non-vacuity (sabotage)

With the fix reverted to the tip version, the regression spec goes RED:
`Results: 9 total, 3 passed, 6 failed`. The 3 that stay green are exactly the
preserved-behaviour cases (name-less lazy still deferred, MCP tool modules still
out of the closure, `lazy_thing.mod` not mistaken for the modifier), which is the
intended asymmetry. With the fix applied: `9 total, 9 passed, 0 failed`.

### Lane note

Every measurement here is the **tree-walking interpreter** lane
(`bin/simple_seed run` / `bin/simple_seed test`), one process per file. That is
sufficient and appropriate: the code under test is a pure text function over
source content, with no engine-divergent construct. It does NOT prove the
downstream stage3 census delta — that needs a stage2 build and is out of scope
for this lane.

---

## 2026-08-01 (later pass) — class (B) residue closed, and three method corrections

Scope of this pass: re-classify all 545 census lines against the **current tip**
(`3807bab68e8`), close the remaining class-(B) one-liners, and correct three
premises in the sections above that were producing wrong verdicts.

### Correction 1 — `compiler.backend.backend_api` DOES resolve (premise above is WRONG)

The note "A module path that maps to no file is silent. `compiler.backend.backend_api`
has no file" is **incorrect**, and so is the reasoning in the `BackendKind`
bullet that leans on it. Module paths are **not** a plain
`dots -> directories` mapping. `10.frontend/core/interpreter/module_loader_resolve.spl`
resolves a path with two extra rules:

- a segment matches a child dir named `seg` **or** `NN.seg`
  (`resolve_with_numbered_dirs` / `find_numbered_dir_interp`, lines 296-352), and
- a numbered layer dir may be **traversed without consuming a segment**
  (the transparent-dir path, `_find_transparent_file` / `_resolve_transparent`,
  lines 353-395).

So `compiler.backend.backend_api` resolves to
`src/compiler/70.backend/backend/backend_api.spl` — the same file the earlier
section says is "a different module path".

The decisive, one-line demonstration that plain path mapping is wrong:
**there is no `src/compiler/core` directory anywhere in the tree**
(`ls src/compiler/core` → No such file or directory), yet
`use compiler.core.tokens.{...}` is written **266×** in-tree and resolves to
`src/compiler/10.frontend/core/tokens.spl`. Likewise `compiler.core.parser`
(66×) and `compiler.core.ast_types` (10×).

**The class-(B) verdict for `BackendKind` survives**, but for a different reason
than recorded: not "the glob target does not exist", but "the glob target exists
and imports the name with a plain `use`, which is not a re-export". The
`export use` vs plain `use` discriminator is the whole test; module-path
existence was a red herring in both directions.

### Correction 2 — multi-line brace imports must be parsed

A line-oriented `^use ...\{...\}` matcher silently misses imports that span
lines, e.g. `70.backend/backend/vhdl/vhdl_design_catalog.spl:6` opens
`use compiler.common.attributes.{` and closes three lines later. Before the
parser in this pass was made brace-balancing, that produced **3 false class-(B)
verdicts** — symbols reported as "no import path" that were already imported.
Any future analyzer must accumulate lines until braces balance, and must also
treat `use a.b.c.Symbol` (no braces) as a named import when `a.b.c` is a module.

### Correction 3 — exclude `src/compiler_rust/**` when counting declaring modules

It is the vendored seed tree, outside owned-code scope. Counting it inflates the
ambiguity that gates a fix: `Span` shows 10 declaring modules including it, 5
owned, and **2** in the compiler tier; `Visibility` shows 7 / 3 / **1**. Three
sites that were "ambiguous, do not guess" are decidable once the seed tree is
excluded.

### Re-classification of the 545 census at tip `3807bab68e8`

Method per pair: brace-aware import parse of the using file, declaration index
over the whole tree, then glob reachability that follows a glob's first hop and
thereafter **only `export use` edges**. Symlink-canonicalised
(17 `src/compiler/<name>` layer symlinks) so no file is double-counted.

| class | error lines | unique pairs |
|---|---|---|
| already named-imported at tip | 345 | 46 |
| (A) reachable via a glob re-export hop | 77 | 28 |
| (B) no import path at all | 120 | 68 |
| no declaration anywhere | 3 | 3 |
| **total** | **545** | **145** |

The 120 class-(B) lines break down as:

| bucket | lines | pairs | action |
|---|---|---|---|
| fixed in this pass | 51 | 30 | one named import per site |
| separate defects (already filed below) | 45 | 27 | not import defects |
| genuinely ambiguous provider | 24 | 11 | needs an owner — listed below |

### Fixed in this pass — 30 pairs, 51 census lines, 19 import lines, 16 files

Each addition names **one declaring module** that is the symbol's **sole**
declaring module (or, for the four tier-resolved sites, the sole *owned
compiler-tier* one), so no import winner can be swapped — consistent with
`SymbolTable.define` being last-write-wins for `Function`/`Const`/`TypeAlias`.

| using file | added import | symbols | lines |
|---|---|---|---|
| `10.frontend/core/_Ast/module_state.spl` | `compiler.core.ast_types` (extend) | `make_core_decl` | 1 |
| `10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl` | `compiler.frontend.core._Ast.decl_nodes` | `decl_aop_advice`, `decl_arch_rule` | 2 |
| `10.frontend/core/_ParserDecls/enum_module_body.spl` | `compiler.core.tokens` (extend) | `tok_kind_name` | 1 |
| `10.frontend/core/_ParserDecls/fn_struct_decls.spl` | `compiler.frontend.core._Ast.decl_nodes` | `decl_set_param_muts` | 1 |
| `10.frontend/core/parser_decls_use.spl` | `compiler.core.parser` (extend) | `parser_parse_type_with_union` | 3 |
| `10.frontend/core/parser_stmts.spl` | `compiler.frontend.core._ParserPrimary.primary_expr` | `parse_fn_lambda_after_kw` | 3 |
| `10.frontend/desugar/placeholder_lambda.spl` | `compiler.frontend.core._AstExpr.accessors` | `expr_interpolated_string` | 2 |
| `10.frontend/treesitter/heuristic.spl` | `compiler.common.dependency.visibility` | `Visibility` | 2 |
| `50.mir/_MirLowering/function_lowering.spl` | `compiler.mir.mir_types` | `MirConstant` | 1 |
| `50.mir/_MirLowering/module_lowering.spl` | `compiler.common._Attributes.decl_attrs` | `DriverManifestAttr`, `DriverManifestAttrKind`, `vhdl_hardware_metadata_default` | 6 |
| `50.mir/_MirLowering/module_lowering.spl` | `compiler.common.dependency.visibility` | `Visibility` | 3 |
| `50.mir/_MirLowering/module_lowering.spl` | `compiler.mir.mir_types` | `MirConstant`, `MirFieldDef`, `MirStatic`, `MirTypeDefKind` | 7 |
| `50.mir/_MirLoweringExpr/method_calls_literals.spl` | `compiler.mir.mir_instruction_support` | `GpuMemoryScope` | 1 |
| `60.mir_opt/_OptimizationPasses/engine.spl` | `compiler.mir.mir_instruction_graph` | `mir_fold_binop` | 1 |
| `70.backend/backend/_VhdlProcess/process_codegen.spl` | `compiler.mir.mir_instruction_support` | `vhdl_clock_domain_from_metadata` | 1 |
| `70.backend/backend/compiler.spl` | `compiler.backend.codegen` | `CodegenMode`, `CodegenPipeline` | 4 |
| `70.backend/backend/vhdl/vhdl_design_catalog.spl` | `compiler.hir.hir_types` (extend) | `SymbolId` | 4 |
| `70.backend/backend/vhdl/vhdl_design_catalog.spl` | `compiler.mir.mir_types` | `MirConstant`, `MirFieldDef`, `MirStatic`, `MirTypeDefKind`, `MirVariantDef` | 7 |
| `80.driver/driver_source_pipeline_loading.spl` | `compiler.common.driver_core_modes` | `CompileMode` | 1 |

Pre-landing checks, all PROVED, all green:

- every added symbol **is declared** in the module named (declaration scan of the
  resolved target file) — 0 exceptions;
- every module spelling **resolves to exactly one file**, and that file is the
  declaring file — 0 exceptions;
- every spelling is **already used in-tree** (the A/B control), from 1× up to
  266×; the highest-usage resolving spelling was chosen in every case;
- no added symbol was **already imported** in the using file — 0 duplicates;
- every added line **re-parses** as a named import of exactly the intended
  module — 0 exceptions;
- no `FIX` site's file has an **unresolved glob**, so no "class B" verdict rests
  on a glob the analyzer failed to follow.

Two sites called out earlier deserve their specific resolutions:

- **`parser_parse_type_with_union` — the cycle check is satisfied, no new edge.**
  `parser_decls_use.spl` **already** imports `compiler.core.parser` (line 26,
  `{par_kind_get, par_text_get, par_line_get, par_col_get}`); the symbol is added
  to that existing brace list, so the import edge already existed and no cycle
  can be created. In-tree control: `parser_stmts.spl:70` carries
  `use compiler.core.parser.{parser_parse_type, parser_parse_type_with_union}`
  and has **zero** `parser_parse_type_with_union` errors in the same census.
- **`SymbolId`** is added to the `compiler.hir.hir_types` import
  `vhdl_design_catalog.spl:5` already has — again zero new edges.

### Still blocked — 11 pairs / 24 census lines, ambiguous provider

`dir_walk` and `file_write_bytes` remain **DO-NOT-GUESS** and are confirmed so:
after excluding the vendored seed tree they still have 10 and 7 owned declaring
modules respectively, and **zero** in the compiler tier — they are lib-tier
functions called from `70.backend/linker/`, so the choice is a tier decision an
owner must make, not a lookup.

| symbol | using file | owned decls | compiler-tier decls | lines |
|---|---|---|---|---|
| `Span` | `10.frontend/treesitter/heuristic.spl` | 5 | 2 | 8 |
| `expr_kind` | `10.frontend/desugar/suspension_analysis.spl` | 2 | 2 | 4 |
| `stmt_kind` | `10.frontend/desugar/suspension_analysis.spl` | 3 | 3 | 3 |
| `shell` | `70.backend/linker/link.spl` | 18 | 0 | 2 |
| `Span` | `10.frontend/treesitter/outline_types.spl` | 5 | 2 | 1 |
| `Span` | `25.traits/trait_validation.spl` | 5 | 2 | 1 |
| `Span` | `25.traits/associated_types.spl` | 5 | 2 | 1 |
| `Span` | `30.types/type_infer/context.spl` | 5 | 2 | 1 |
| `GpuBarrierScope` | `50.mir/_MirLoweringExpr/method_calls_literals.spl` | 3 | 3 | 1 |
| `dir_walk` | `70.backend/linker/smf_getter.spl` | 10 | 0 | 1 |
| `file_write_bytes` | `70.backend/linker/link.spl` | 7 | 0 | 1 |

The two `Span` candidates in the compiler tier are
`00.common/diagnostics/span.spl` and `10.frontend/core/lexer_types.spl`; these
are different `Span` types, so picking one is a semantic decision. `Span` is a
first-write-wins kind, so a wrong pick would not swap an existing winner, but it
would bind the wrong type.

### Evidence basis for this pass — and its limits

Per symbol: a static reachability proof plus an in-tree A/B control, as above.

Additionally, each of the 19 added import lines was **executed through the real
compiler** in an isolated tree at the tip: a generated probe `.spl` carrying
exactly that `use` line was run with `simple_seed run`, and all 18 distinct
`(module, symbol-set)` probes printed their marker with no resolution
diagnostic. All 24 added `(module, symbol)` pairs are covered by those probes.

**Non-vacuity was measured, and the harness is only half sharp** — this is the
part to not over-read:

| deliberately broken probe | result |
|---|---|
| wrong **module** (`compiler.core.tokens_NOPE`) | correctly rejected — `cannot resolve import: module path segment ... not found` |
| wrong **symbol** (`tokens.{tok_kind_name_NOPE}`) | **FALSE PASS** — seed prints the marker and exits 0 |

So the probe is decisive for the **module spelling** axis and **vacuous for the
symbol-existence** axis — which is expected and is the very defect this document
is about: the seed resolves flat, so it does not check a named import against the
declaring module. Symbol existence is therefore carried by the static
declaration scan (every added symbol declared in the resolved target file, 0
exceptions), not by the probe. A symbol-level runtime check requires a
self-hosted stage2, not the seed.

**Not claimed:** a completed seed to stage2 A/B build. One was started against
this tip and was still emitting objects (about 5 per minute under
`--backend cranelift --low-memory` with a cold cache, roughly 90 minutes per
side) when this landed; it is not evidence and is not cited here. Note also that
the deployed `bin/simple_seed` (57 MB) is the **no-LLVM** variant —
`--backend llvm` fails with "native backend 'llvm' is not available in this
build", so any stage2 timing quoted elsewhere in this file was produced by a
different binary.

Stage3/stage4 counts were deliberately **not** used: stage4 exits 1 at
`[ERROR] phase 3 FAILED` (phase 3 is HIR lowering) with `[stmt_get_tag] OOB`
from log line 1, so its counts are early-abort artifacts, and stage3 runs the
bootstrap-flat pipeline which never performs this lowering.
