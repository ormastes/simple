# Module-Qualified Function Resolution — Scoping Plan

**Status:** scoping only. No migration performed.
**Date:** 2026-08-01
**Tracks:** item 2 ("key the registry on (module path, bare name)") of
`doc/08_tracking/bug/diag_stage_facet_cross_module_collision_under_test_2026-07-06.md`,
which that doc's "What is still open" section lists as not done.
**Predecessor:** commit `59c26310533` widened the *detector*. Detection is not
resolution. This plan scopes the resolution half.

---

## 0. TL;DR

- The registry is bare-name keyed in **four** engines with **four different**
  clobber policies. They do not agree on which definition wins, so the same
  program can dispatch to a different body under the interpreter than under
  Cranelift than under LLVM. That divergence is the real defect; "last-write-wins"
  understates it.
- **Module provenance already exists and is already plumbed** through the Rust
  interpreter (`FLATTEN_MODULE_OWNER_ATTR_PREFIX` attribute → `FUNCTION_MODULE_OWNER`
  → `CURRENT_EXEC_MODULE` → `select_overload` tie-break). A per-module *import view*
  also already exists (`MODULE_GLOBAL_BINDINGS_BY_OWNER`) but is wired only to
  globals, not to functions. The first stages are therefore *consumption* of
  existing data, not new plumbing.
- Exposure is large and the driver is structural, not accidental: **8,139 wildcard
  imports across 5,094 files**, amplified by **1,629 wildcard *re*-exports**. The
  five live colliders each have 7–10 definition sites in `src/`, and the reason is
  the `nogc_sync_mut` / `nogc_async_mut` / `gc_async_mut` tier structure carrying
  parallel copies of one API surface. Colliding names therefore arrive in *batches*
  per tier pair, not one at a time. See §3.5.
- The single most valuable cheap stage is **not** a resolution change at all: the
  detector currently `continue`s when all colliding signatures are identical
  (`module_loader.rs:1386-1390`, "all identical → harmless under last-write-wins").
  That is false — identical signature, different body, different module is the
  *worst* case and today it is completely unwarned. Stage 1 closes that blind
  spot. It is the same shape of wrong assumption that `59c26310533` fixed.

---

## 1. (a) Enumeration — every bare-name function resolution site

Paths are absolute. `R/` = `/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/`.
`S/` = `/home/ormastes/dev/pub/simple/src/compiler/`.

### 1.1 Rust interpreter — flat `HashMap<String, Arc<FunctionDef>>`

| Site | Kind | Clobber policy |
|---|---|---|
| `R/interpreter_eval.rs:387` | **DECLARE** `functions: HashMap<String, Arc<FunctionDef>>` | the one root registry, threaded `&mut` into ~40 fns |
| `R/interpreter_eval.rs:447` | lookup guard | fires **only** for active-`@cfg` duplicates (warn + `continue`) |
| `R/interpreter_eval.rs:487` | **INSERT `.insert()`** | **silent LAST-WRITE-WINS — the collision point for `bin/simple run` / `-c`** |
| `R/interpreter_eval.rs:1371, 1503, 1516, 1550` | insert (bare / alias name) | `.insert()`, silent |
| `R/interpreter_eval.rs:1638` | insert `"{mod}.{fn}"` | module-qualified key — already safe, precedent |
| `R/interpreter_eval.rs:619, 1377, 1808` | lookup | bare |
| `R/interpreter_call/block_execution.rs:666, 1578` | insert | `.insert()`, silent |
| `R/interpreter_module/module_merger.rs:31` | insert | `.insert()`, silent |
| `R/interpreter_module/module_loader.rs:1066` | insert | `.insert()`, silent |
| `R/interpreter_module/module_evaluator/evaluation_helpers.rs:173, 183, 626` | insert (dual local+global tables) | `.insert()`, silent |
| `R/interpreter/expr.rs:359`, `R/interpreter_method/mod.rs:1624`, `R/module_cache.rs:402` | insert | `.insert()`, silent |
| `R/interpreter_sffi.rs:32` | **DECLARE** `INTERP_FUNCTIONS` thread-local mirror | same type, same policy |

Bare-name **lookup** sites (all read the already-clobbered map):
`R/interpreter_call/mod.rs:292, 351, 690, 757, 926, 1166` ·
`R/interpreter_call/core/aop_advice.rs:74` · `R/interpreter_control.rs:1999, 2150` ·
`R/interpreter_method/mod.rs:230, 1501, 1772` ·
`R/interpreter_helpers/method_dispatch.rs:808` · `R/interpreter/expr/literals.rs:292` ·
`R/interpreter/expr/ops.rs:423, 478` · `R/interpreter/expr/calls.rs:342` ·
`R/interpreter/expr/collections.rs:226`.

**Methods are in the same flat map**, keyed `"{Type}__{method}"` — unique per
*type*, not per *module*:
`R/interpreter_eval.rs:763, 888, 960` · `R/interpreter/node_exec.rs:432, 460, 531` ·
`R/interpreter_call/block_execution.rs:694, 787, 815, 905, 1416, 1444, 1534` ·
`R/interpreter_module/module_evaluator/evaluation_helpers.rs:202, 255, 318, 376`.

**Already-existing module-qualified machinery (do not rebuild):**

| Site | What it is |
|---|---|
| `R/interpreter_state.rs:66` `FLATTEN_MODULE_OWNER_ATTR_PREFIX` | owner path carried *inside the AST node* as a synthetic attribute; survives `clone()`; collision-proof per node |
| `R/interpreter_state.rs:67` `tag_function_module_owner` | writer |
| `R/pipeline/module_loader.rs:508` `tag_node_function_owners`, `:588` | tags every flattened-in function at flatten time |
| `R/interpreter_eval.rs:475-486` | reads the attribute back at registration |
| `R/interpreter_state.rs:289` `FUNCTION_MODULE_OWNER: HashMap<usize, Arc<str>>` | `Arc` identity → owner |
| `R/interpreter_state.rs:297` `CURRENT_EXEC_MODULE: Option<Arc<str>>` | caller's module, maintained across frames (`function_exec.rs:552, 618, 1357, 1431`) |
| `R/interpreter_state.rs:276` `FUNCTION_OVERLOADS: HashMap<String, Vec<Arc<FunctionDef>>>` | **retains every colliding definition** (`entry().or_default().push()` at `interpreter_eval.rs:489`) |
| `R/interpreter_call/mod.rs:328` | Priority 4: consults `FUNCTION_OVERLOADS` **before** the flat map, whenever `len() > 1` |
| `R/interpreter_call/mod.rs:163-173` `is_current_module_candidate` | the existing tie-break |
| `R/interpreter_state.rs:222` `MODULE_GLOBAL_BINDINGS_BY_OWNER: HashMap<Arc<str>, HashMap<String, (Arc<str>, String)>>` | **the per-module import view already exists** — importer → local name → (source owner, source name); populated from `__simple_flatten_import_binding__=` markers (`module_loader.rs:539`, consumed `interpreter_eval.rs:77, 1249`). Wired to **globals only.** |

**Correction to the in-tree hazard comment.** `module_loader.rs:1305` says the
interpreter is a bare `HashMap<String, FunctionDef>` last-write-wins. That is
*stale*: `FUNCTION_OVERLOADS` retains all candidates and Priority 4 consults it
first, so the flat map is only reached when exactly one candidate exists. The
residual interpreter defect is narrower and should be stated precisely:

> Same name + **equal overload score** + neither candidate owned by the caller's
> module ⇒ `select_overload` (`R/interpreter_call/mod.rs:175-200`) falls through
> to "keep first-registered", which is registration-order-arbitrary.

That is exactly the shape of the five live colliders (`skip`, `shell`,
`shell_output`, `file_read_bytes`, `dir_remove_all`): the caller is a spec file
that owns *neither* definition, so the module tie-break is a no-op.

### 1.2 Cranelift codegen — `func_ids: BTreeMap<String, FuncId>`

| Site | Kind | Policy |
|---|---|---|
| `R/codegen/common_backend.rs:563` | **DECLARE** | — |
| `R/codegen/common_backend.rs:1371` | insert raw `func.name` | **`.insert()` LAST-WRITE-WINS — the clobbering write** |
| `R/codegen/common_backend.rs:1373` | insert `symbol_name` (mangled) | `.insert()` last-wins |
| `R/codegen/common_backend.rs:1319, 1379, 1381, 1519` | insert | `entry().or_insert` — **first**-wins |
| `R/codegen/common_backend.rs:2218` | insert `init_name` | `.insert()` |
| `R/codegen/common_backend.rs:1459, 1640, 1800, 1806, 1815, 2070, 2137, 2495, 2504` | lookup | — |
| `R/codegen/instr/calls.rs:60` `has_defined_local_function` | lookup | primary bare-name gate |
| `R/codegen/instr/calls.rs:3107` `ctx.func_ids[func_name]` | **panicking index** | main user-call dispatch |
| `R/codegen/instr/calls.rs:3196` | lookup fallback | — |
| `R/codegen/instr/calls.rs:3304, 3501, 3509` | insert | `.insert()` |
| `R/codegen/instr/mod.rs:97, 402, 452, 532, 540` | ctx field / lookups / inserts | mixed |
| `R/codegen/instr/{helpers.rs:304,465,478 · methods.rs:401,414 · basic_ops.rs:135,145 · closures_structs.rs:23,221,260,265,566,571,586,588,646,934,959,1183,1221,1237,1535 · body.rs:478,894,933}` | lookups + `.insert()` | last-wins |
| `R/codegen/shared.rs:98, 102, 124` | local map + **`contains_key → continue` dedup guard** | **FIRST-write-wins** |
| `R/codegen/cranelift_sffi.rs:63, 69` | separate `HashMap<String, FuncId>` (SFFI/hot-reload); inserts 443, 452, 849, 1626; lookups 1223, 1233, 1486 | last-wins |
| `R/codegen/cranelift_emitter.rs:112`, `R/codegen/jit.rs:170, 178` | lookup | — |

**Policy inconsistency, same backend:** `shared.rs:102` is first-wins while
`common_backend.rs:1371` is last-wins. The two paths can therefore select
*different* bodies for the same name in the same build.

### 1.3 LLVM backend — no `func_ids`; the LLVM module symbol table *is* the map

`R/codegen/llvm/backend_core.rs:282, 304-313, 335, 363-367 (`.`→`_dot_`),
436-449, 658-661, 746-772 (`declare_dot_aliases_for_methods`), 810, 1033-1037
(reuse-if-exists), 1055, 1081, 1336-1381 (`RUNTIME_FUNCS` pre-declare, skip-if-exists
1346), 1388-1443 (forward-declare pass)`.
Call-site chain: `R/codegen/llvm/functions/calls.rs:2283-2287`
(`sffi_name` → `resolved_name` → `resolved_dotted` → `func_name_raw` → `raw_dotted`),
declares at 2379/2384; also `functions.rs:410-418`.
Aux name maps: `backend_core.rs:53 import_map`, `:55 fn_arities`, `:61 use_map`,
`:63 function_return_types`.

**Distinct failure mode:** LLVM `add_function` on an existing name silently
**auto-renames** to `foo.1` rather than overwriting. So LLVM neither clobbers
(Cranelift) nor keeps-first (`shared.rs`) — it emits *both* and the call site
resolves to whichever the chain above names first. Three engines, three answers.

### 1.4 MIR / HIR lowering — the call target is a bare `String`

- `R/mir/effects.rs:541-553` — `CallTarget::{Pure,Io,…}(String)`. There is **no id**;
  the name string *is* the reference. `R/mir/inst_enum.rs:42` `MirInst::Call`.
- `R/mir/lower/lowering_expr_call.rs:207` `lower_call_expr`; bare-name branches
  208, 233, 266 on `HirExprKind::Global(name)`; `MirInst::Call` emitted 509, 568, 650.
- `R/hir/lower/expr/calls.rs:27` `lower_call` — `Expr::Identifier(name)` →
  `HirExprKind::Global(name.clone())` (e.g. `:57`).
- `R/hir/lower/lowerer.rs:61, 557` `function_aliases: HashMap<String,String>` +
  `resolve_function_alias`.
- `R/mir/lower/lowering_core.rs:275, 279, 1211, 1227` `function_param_types` /
  `inject_functions`, both `.insert()` last-wins; lookups `lowering_di.rs:118`,
  `lowering_expr_struct.rs:48`.
- `R/mir/lower/lowering_core.rs:1249-1275` — **the only existing duplicate-name
  mitigation anywhere**: `sigs_by_name`, renames to `name$dupK`. Gated to
  `_`-prefixed, non-dotted free functions **with differing signatures**. Public
  names and `Type.method` names are excluded — i.e. it carries the *exact* blind
  spot `59c26310533` removed from the detector, still uncorrected in the renamer.

### 1.5 Extern / builtin registry

- `R/codegen/runtime_sffi.rs:210` `RUNTIME_FUNCS: &[RuntimeFuncSpec]` keyed by bare
  `name`; `runtime_funcs_for_target()` `:162`.
- Materialized `R/codegen/common_backend.rs:564 runtime_funcs: HashMap<&'static str, FuncId>`;
  consumed `calls.rs:3109`, `instr_gpu.rs` (14 sites), `instr/parallel.rs`,
  `instr/actors.rs:39`, `instr/basic_ops.rs:55, 133, 159, 164`.
- `R/codegen/instr/calls.rs:2845` `sffi_alias_target` — bare-name aliasing to `rt_*`.
- Cross-module maps `R/codegen/common_backend.rs:580, 588, 599`, populated
  `R/pipeline/native_project/imports.rs:64, 285, 330, 346, 389, 475, 498, 522, 534`
  — all `.insert()`, last-wins.
- Interpreter side: `R/interpreter/core_types.rs:79` + `R/interpreter_eval.rs:418, 1027`
  `ExternFunctions = HashMap<String, ExternDef>`, bare, silent.
- Related known hazard: an unregistered `@extern fn` returns nil silently and the
  native linker emits a weak `return 0` stub for any non-`rt_` name — so an
  extern-name collision degrades to silent wrong-value, not a link error.

### 1.6 Pure-Simple mirror

| Site | What | Policy |
|---|---|---|
| `S/10.frontend/core/interpreter/eval_tables.spl:182` `func_table_register` | interpreter registry; flat `ft_keys/ft_vals/ft_buckets` on bare `name` | warns, then `ft_vals[idx] = decl_id` → **LAST-WRITE-WINS, unconditional, no kind check** |
| `S/10.frontend/core/interpreter/eval_tables.spl:194` `func_table_lookup` | bare name only, `-1` on miss | no module parameter exists |
| `S/10.frontend/core/interpreter/eval_tables.spl:203, 224, 260` | `func_table_remove` / `_owned` | `_owned` is the only ownership guard, and only for unload |
| `S/10.frontend/core/interpreter/eval_tables.spl:244-258` | comment | states the hazard in the same words as the Rust side |
| `S/10.frontend/core/interpreter/eval_tables.spl:124-142, 158, 165` | `_ftr_collision_kind`, `_ftr_warn_collision` | the pure-Simple half of `59c26310533` |
| `S/10.frontend/core/interpreter/module_loader_core.spl:257, 270, 291, 354, 400` | `register_module_functions` — flattening. `:291` registers `impl` methods under the **bare method name**, not `Type.method` | worse than Rust, which at least qualifies by type |
| `S/10.frontend/core/interpreter/module_loader_lazy.spl:526` | lazy mirror of the same | — |
| `S/20.hir/hir_types.spl:246` `SymbolTable.define` | branch at `:259-272`: `Class/Struct/Enum/Trait → true` = first-wins (returns existing id `:270`); **everything else falls through to `:273+`, `scope_syms[name] = raw_id` at `:283-289` = last-wins** | Function/Const/TypeAlias are last-wins **by omission**, not by decision |
| `S/20.hir/hir_types.spl:185, 196-204, 301, 322, 460` | `Scope.symbols: Dict<text,i64>`; `lookup` / `lookup_or_invalid` / `lookup_function` | bare-name scope-chain walk |
| `S/20.hir/hir_types.spl:93` `defining_module: text?` on `HirSymbol` | **module provenance already exists at HIR level** | populated only for imports (`S/20.hir/hir_lowering/_Items/module_lowering.spl:563-587, 811, 828, 1077`); consumed `hir_types.spl:475` (`method_symbol_name`) and `S/50.mir/_MirLowering/module_lowering.spl:165-186` — for **type canonicalization only, never for function resolution** |
| `S/10.frontend/core/interpreter/interp_resource_tracker.spl:92` `irt_track_func_owned(module_path, name, decl_id)` | records owning module per registration | **not consulted by lookup** — used only for unload safety |
| `S/00.common/dependency/symbol.spl:34-41, 71, 80` | `SymbolEntry{qualified_name, source_module}`, `DepSymbolTable` | **dead scaffolding** — only `symboltable_new` implemented; no `define`/`lookup` port of `dependency_tracker/src/symbol.rs:169/182` |

**Pure-Simple gaps vs Rust:** no `FUNCTION_OVERLOADS` equivalent (so a collision
is a *hard* overwrite, with none of the Rust overload-set recovery); no
`find_method_arity_collisions` mirror at all; `impl` methods registered under the
bare method name.

### 1.7 Detector blind spot (new finding, not previously recorded)

`R/pipeline/module_loader.rs:1386-1390`:

```rust
distinct.dedup();
if distinct.len() < 2 {
    continue; // all identical → harmless under last-write-wins
}
```

The comment is wrong. Two same-named functions with **identical signatures** and
**different bodies** from **different modules** are the maximally dangerous case
— arbitrary body selection, no signature mismatch to catch it downstream, and
**no warning at all today**. The five named colliders are the *differing*-signature
ones; the identical-signature population is entirely unmeasured. Additionally
`by_name` (`:1359`) records only signatures, not owners, so the warning cannot
name the two files even when it does fire.

---

## 2. (b) What module-qualified resolution changes at each site — and what stays bare

**Target model.** Two-level: `resolve(caller_module, bare_name)` =
1. definition owned by `caller_module`, else
2. the unique definition reachable through `caller_module`'s explicit import view
   (`use m.{f}` / `use m.f as g`), else
3. the unique definition reachable through `caller_module`'s **wildcard** imports —
   ambiguity here is the only genuinely new error class, else
4. the flat bare-name map (unchanged legacy fallback).

Step 4 is what keeps this landable. Nothing is *removed*; a preference order is
*inserted above* the existing lookup.

| Layer | Changes | Stays bare-name |
|---|---|---|
| Rust interpreter | `select_overload` (`R/interpreter_call/mod.rs:175`) gains steps 2–3 using a function-flavoured twin of `MODULE_GLOBAL_BINDINGS_BY_OWNER`. `is_current_module_candidate` (`:163`) already implements step 1. | `functions` map (`interpreter_eval.rs:387/487`) untouched — it is only reached when `FUNCTION_OVERLOADS[name].len() == 1`, i.e. no collision. **No change needed to the flat map at all.** |
| Cranelift | `common_backend.rs:1371` must emit a *distinct* symbol per (owner, name) and record the mapping; `calls.rs:3107/3196` must resolve through caller-owner. Requires owner to survive AST→MIR (see below). | `runtime_funcs` / `RUNTIME_FUNCS` / `rt_*` externs — a genuinely global flat namespace by design. |
| LLVM | Same, but the fix is *cheaper*: LLVM already auto-renames to `foo.1`, so both bodies exist; only `calls.rs:2283-2287`'s resolution chain needs owner input. | `RUNTIME_FUNCS` pre-declares; `_dot_` mangling. |
| MIR/HIR | `CallTarget(String)` (`R/mir/effects.rs:541`) must carry owner or a pre-resolved id. `HirExprKind::Global(name)` (`R/hir/lower/expr/calls.rs:57`) must carry the lowering module. **This is the load-bearing change and the reason a big bang is impossible** — it is a type change through the whole IR. | `function_aliases`, `sffi_alias_target`. |
| Pure-Simple interpreter | `func_table_register/lookup` (`eval_tables.spl:182/194`) gain a module parameter. `irt_track_func_owned` (`:92`) already has the data. | `struct_table` (separate lane). |
| Pure-Simple HIR | `SymbolTable.define` (`hir_types.spl:246`) already **takes `defining_module`** and `HirSymbol` already **stores it** (`:93`). Only `:283-289` needs to key on it and `lookup_function` (`:460`) needs to filter by import view. | `Class/Struct/Enum/Trait` first-wins branch (`:259-272`) — separate defect class. |

**Gating rule for any comparison:** per `SymbolTable.define`'s split policy, a
before/after comparison must be gated by **set inclusion** of resolved
`(caller, name) → definition` pairs, never by counts. Counts are equal in both
the correct and the clobbered world.

---

## 3. (c) What breaks

### 3.1 The genuinely new failure class

Today a wildcard import that pulls in two same-named functions is *silently*
resolved. Under the target model step 3 it becomes **ambiguous**. Every such
site is a new compile error unless it hits the step-4 fallback. This is why
step 4 must be retained through the whole migration and why the ambiguity
diagnostic must ship (and be *measured*) as a warning long before it is an error.

### 3.2 Re-export chains

`R/pipeline/module_loader.rs:601-628` already treats `ExportUseStmt` as an
ordinary import for binding-marker purposes, with an explicit comment that "an
importer may resolve a mutable module global through this facade (consumer →
facade → defining module)". So the import view is **transitive for globals
already**. Functions must reuse that same chain, not a new one. A facade that
re-exports a name which also exists locally in the consumer is a step-1-vs-step-2
conflict: step 1 (own module) wins, which is the correct and least-surprising rule
but *is* a behaviour change where the facade currently wins by registration order.

### 3.3 Method registration

Pure-Simple registers `impl` methods under the **bare** method name
(`module_loader_core.spl:291`). Qualifying functions without simultaneously
qualifying methods there will *increase* divergence between the two
implementations. Pure-Simple method keying must move to `Type.method` before or
with the function work — this is a prerequisite, not a follow-up.

### 3.4 Engine divergence is a blocker for verification, not just a symptom

Because the interpreter is last-wins, `shared.rs` first-wins, and LLVM
auto-renames, **any** verification that runs on one engine proves nothing about
the others. Each stage below therefore names its engine explicitly.

### 3.5 Quantification — measured 2026-08-01

All counts from `/usr/bin/grep` (default `grep` here is ugrep — never use it for
a reported count), vendored paths excluded (`src/compiler_rust/vendor/**`,
`src/runtime/vendor/**`).

| Metric | `src/` | `test/` |
|---|---|---|
| `.spl` files | 13,902 | 25,618 |
| Wildcard `use x.y.*` occurrences | 1,983 | 6,156 |
| Distinct files with ≥1 wildcard | 851 | 4,243 |
| `export use` re-exports | 3,672 | 16 |
| …of which are themselves wildcard (`export use a.b.*`) | 1,629 | — |
| `pub use` | 322 | 6 |

**Combined: 8,139 wildcard imports across 5,094 distinct files.**

Per-directory: `src/compiler` 687 occ / 329 files · `src/lib` 396 / 218 ·
`src/app` 390 / 104 · `src/os` 177 / 84 · `src/unit` 30 / 1 · `test/` 6,156 / 4,243.

Top wildcard-imported modules by distinct importer file:
`std.spec.*` **1,974** · `std.spipe.*` **1,701** · `compiler.mir.mir_data.*` 196 ·
`std.ndarray.*` 190 · `std.gc_async_mut.web.browser_session_runtime.*` 59 ·
`std.df.*` 53 · `compiler.mir.mir.*` 44 · `std.linalg.*` 42 ·
`compiler.hir.hir_lowering.items.*` 40 · `compiler.hir.hir.*` 40.

**Re-export syntax is `export use <path>`**, not `pub use` — `export` is this
codebase's primary visibility keyword. 3,672 re-exports across 2,590 distinct
files, and **1,629 of them are wildcard re-exports**, which is the chain
amplifier: a wildcard re-export of a wildcard import makes the reachable name set
of a consumer transitively unbounded without reading the whole chain.

**Definition sites for the five live colliders** (`src/`, top-level, all
`/usr/bin/grep -n -E '^(pub |export |extern |pub extern )?fn <NAME>\('`):

| Name | `src/` defs | Notable |
|---|---|---|
| `skip` | **8** | `src/lib/nogc_sync_mut/spec.spl:216` (`pub fn`) + three tier `spec/__init__.spl:43` + `spec/decorators.spl:16` + three `testing/gpu_helpers.spl:56`. `+13` more in `test/`. |
| `shell` | **10** | across `src/app/io`, three `src/lib` tiers, `src/compiler_rust/lib/std/src/sys/env.spl:67`, `.../execution/semihost_capture.spl:205`. `+73` in `test/`. |
| `shell_output` | **7** | mirrors `shell` minus the outliers. |
| `file_read_bytes` | **7** | `src/app/io/file_ops.spl:139` + `io_runtime`/`ffi`/`sffi`/`file_system` tiers. |
| `dir_remove_all` | **8** | `src/app/io/mod_stub.spl:74` + `io_runtime`/`ffi`/`sffi`/`dir_ops` + three tier `mod_stub`. |

**The tier structure is the root multiplier.** These are not accidental
same-names: `nogc_sync_mut` / `nogc_async_mut` / `gc_async_mut` each carry a
parallel copy of the same API surface (`ffi/system.spl` vs `sffi/system.spl`,
`io/file_ops.spl` vs `file_system/file_ops.spl`). Under bare-name flattening,
importing two tiers into one unit collides *every* shared API name at once, not
just one helper. Any migration must handle the tier case as the common case.

**What is NOT measured, and cannot be by grep.** The question "how many *call
sites* resolve to a symbol from a wildcard import" is not answerable statically
here: resolution is what is broken, so counting it requires the resolver. The
numbers above are an **upper bound on exposure** (5,094 files sit downstream of a
wildcard), not the disagreement set. The exact disagreement set is precisely
Stage 4's deliverable, and that is the load-bearing reason Stage 4 exists as a
shadow resolver before any dispatch changes.

**Do not schedule Stage 6 on this upper bound.** 5,094 files is an exposure
figure; treating it as the migration size would be acting on an assumed
population, which is how the two prior regressions in this family happened.
Stage 6 is scheduled off Stage 4's measured disagreement set, not off this table.

---

## 4. (d) Staged migration

Each stage is independently landable, independently verifiable, and independently
revertable. No stage depends on a later stage.

### Stage 1 — Close the identical-signature detector blind spot (SAFE, SMALL)

**Change:** at `R/pipeline/module_loader.rs:1386-1390`, stop `continue`-ing when
`distinct.len() < 2`. Record the **owner** alongside each signature in `by_name`
(`:1359`) — the owner is already on the node as
`FLATTEN_MODULE_OWNER_ATTR_PREFIX` — and warn when the same name is defined by
**two or more distinct owners**, regardless of whether signatures match. Mirror
in `S/.../eval_tables.spl:165`.

**Why it is safe:** `warn_duplicate_private_signatures` is `eprintln!` only, on a
`OnceLock`-deduped path. It has no effect on resolution. Worst case is warning
noise, and the noise is bounded and measurable before landing.

**Verification:** run the 275-module unit that produced the five known colliders;
the five must still appear (set inclusion, not count), plus the
identical-signature population, each naming both owning files. If the new
population is large, that number is itself the Stage 4 blast-radius input.

**This is the recommended first stage.** It is small, it is pure diagnostic, and
it measures the very population every later stage needs.

### Stage 2 — Import view for functions, interpreter only, tie-break only (Rust)

**Change:** add `FUNCTION_IMPORT_BINDINGS_BY_OWNER` populated from the *same*
`__simple_flatten_import_binding__=` markers `MODULE_GLOBAL_BINDINGS_BY_OWNER`
already consumes (`R/interpreter_eval.rs:77, 1249`). Extend `select_overload`
(`R/interpreter_call/mod.rs:175-200`) so that on an exact score tie it prefers,
after the existing own-module check, the candidate reachable through the caller's
explicit (non-wildcard) import view.

**Why it is safe:** strictly an extra tie-break arm. It fires only where the
current code is documented-arbitrary ("keep first-registered"). Both owner and
import data already exist and are already populated; no new plumbing, no IR
change, no codegen change.

**Verification:** interpreter engine only. A spec that defines the same name in
two modules with equal arity and asserts the caller's imported one is selected —
today that spec fails, and it must fail before the change to be evidence.

### Stage 3 — Pure-Simple parity: method keying + owner recorded in the registry

**Change:** (3a) `S/.../module_loader_core.spl:291` register `impl` methods as
`Type.method`, matching Rust. (3b) `func_table_register`
(`S/.../eval_tables.spl:182`) records the owning module (data already available
via `irt_track_func_owned`, `interp_resource_tracker.spl:92`) — **recorded only,
lookup unchanged**.

**Why it is safe:** 3b adds a side-table with no reader. 3a is a real behaviour
change and must land alone, with its own verification.

**Verification:** pure-Simple engine. Blocked today — `bin/simple` has no `test`
subcommand at HEAD and `simple test` silently delegates to the Rust seed child,
which is *not* a valid control for pure-Simple changes. **Stage 3 must not be
attempted until a pure-Simple execution path is restored.** Recording that
blocker is part of this plan's deliverable.

### Stage 4 — Ambiguity diagnostic under the real resolution rule (warn only)

**Change:** compute `resolve(caller_module, name)` per call site using steps 1–3
and warn where the answer differs from what step 4 returns today. Change nothing
else. This is a *shadow* resolver.

**Why it is safe:** no dispatch change. It produces the exact list of call sites
that a real migration would move — i.e. it converts the unmeasured blast radius
into an enumerated one.

**Verification:** the shadow resolver's disagreement set must be non-empty and
must include the five known colliders' call sites. An empty set means the shadow
resolver is not wired up (the fall-through-exits-0 failure mode this repo has
been burned by).

### Stage 5 — Owner in the IR (HIR `Global`, MIR `CallTarget`)

**Change:** `HirExprKind::Global(name)` → carries lowering module;
`CallTarget(String)` → `(owner, name)`. Purely additive at first: the owner field
is populated and threaded but **not consulted**.

**Why it is not last:** it is the long pole and it is mechanical. Landing it
inert de-risks Stage 6 entirely.

**Verification:** compiler builds; MIR dumps show owner populated; no behavioural
delta (byte-identical codegen output for a fixed input is the gate).

### Stage 6 — Flip codegen to owner-qualified symbols, behind a gate

**Change:** `common_backend.rs:1371/1373` emit per-(owner, name) symbols;
`calls.rs:3107/3196` and `llvm/functions/calls.rs:2283-2287` resolve through
owner. Behind an env gate, default off. Also reconcile the `shared.rs:102`
first-wins vs `common_backend.rs:1371` last-wins inconsistency — they must agree
before either is trusted.

**Verification:** Cranelift and LLVM separately. Gate on set inclusion of
resolved pairs, per §2's rule.

### Stage 7 — Promote the detector to a hard error; remove step 4

Only after Stage 6 is on by default and the Stage 4 disagreement set is empty.

---

## 5. Explicit non-goals / anti-masking

Restating the three masking modes from the source bug doc, which apply to every
stage above:

- **Do not rename the five live colliders** (`skip`, `shell`, `shell_output`,
  `file_read_bytes`, `dir_remove_all`). They are deliberately un-renamed so they
  stay visible. Renaming them turns every stage's verification green while
  changing nothing — Masking B.
- **Do not replace `use std.spec.*` with concrete imports** to make a spec pass.
  That removes the composition under test — Masking C.
- **Do not add test isolation.** The bug is a product defect.
- **Do not "fix" the detector's noise by re-narrowing its scope.** That is
  precisely the regression `59c26310533` repaired.

---

## 6. Open questions

1. Does any pure-Simple execution path exist at HEAD that can verify Stage 3?
   (Currently: no. `bin/simple` lacks `test`/`run`/`lint`; the bootstrap binary at
   `src/compiler_rust/target/bootstrap/simple` is the canonical 154 MB
   with-LLVM build and is the only candidate.)
2. Should `Type.method` keying become `(owner, Type, method)` or is
   `(Type, method)` sufficient? Two modules defining `impl Style` with the same
   method is the documented cross-module method case with no detector before
   `59c26310533` — so `(Type, method)` is **not** sufficient.
3. `MODULE_GLOBAL_BINDINGS_BY_OWNER` is transitive through re-export facades for
   globals. Confirm the same marker chain is emitted for function-only re-exports
   before Stage 2 relies on it.
