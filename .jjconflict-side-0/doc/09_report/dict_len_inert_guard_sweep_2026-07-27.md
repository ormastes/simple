# Sweep: inert guards / garbage arithmetic caused by `Dict.len() == -1` in native codegen

- **Date:** 2026-07-27
- **Type:** reconnaissance only — **nothing was fixed by this sweep**
- **Defect being traced:** `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`
  (`Dict.len()` returns `-1` for **every** dict under native codegen — local or
  struct field, empty or populated. `keys().len()`, `contains_key()`/`has()` and
  indexed reads `d[k]` are all correct.)
- **Scope:** all tracked `.spl` under `src/`, excluding `src/compiler_rust/vendor/**`
  and `src/runtime/vendor/**`. 13,723 files scanned; 50,086 `.len()`/`.length()`
  call sites; 36,905 of those feed a comparison or arithmetic.

## Headline numbers

| | count |
|---|---|
| `.len()` sites in a comparison or arithmetic | 36,905 |
| …with a **Dict** receiver (confirmed by declaration) | **75** |
| of those, receiver type read directly from a declaration (`certain`) | 62 |
| receiver type inferred from a unique global declaration (`likely`) | 13 |
| in `src/compiler/**` (hot path) | 41 |
| in `src/lib/**` | 10 |
| in `src/app/**` | 6 |
| in `src/compiler_rust/lib/std/**` (seed stdlib, non-vendor `.spl`) | 18 |

## ⚠️ First finding: the two known-bad sites are STILL LIVE in this checkout

The campaign brief states these were removed in `24ebf39ffcdc` and `4283bb222893`.
Neither commit is an ancestor of the current `HEAD`:

```
git merge-base --is-ancestor 24ebf39ffcdc HEAD  -> NOT ancestor
git merge-base --is-ancestor 4283bb222893 HEAD  -> NOT ancestor
```

Both broken expressions are present verbatim in the working tree at
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:457` and `:760`.
**Any fix pass must reconcile with those two commits before editing this file**,
or it will re-litigate work already done on another tip.

## Failure classes used below

| class | meaning under `len() == -1` |
|---|---|
| `EMPTY` | emptiness/non-emptiness test — silently takes the **wrong branch** |
| `SENTINEL` | `< 0` / `>= 0` — **always true / always false**, guard is permanently inert |
| `SIZE` | `== N` / `!= N` / `>= N` against a literal — always false / always true |
| `CMPVAR` | compared against another runtime value — `-1` vs a real count |
| `LOOPBOUND` | `.len()` on the **right** of a comparison — `i < d.len()` is `0 < -1` = false, **loop body never runs** |
| `ARITH` | `-1` enters a sum/index/capacity computation — garbage result |

---

## Top 15 by blast radius

### 1. `src/compiler/80.driver/driver_build/parallel.spl:428` — **WORST SITE**

```
while in_flight_pid.len() < max_workers and ready_idx < ready.len():
```

- Receiver: `in_flight_pid: {i64: i64}` (`parallel.spl:421`) — **certain**
- Class: `CMPVAR` / worker-cap bypass
- **What breaks:** `-1 < max_workers` is **always true**, so the parallel build
  scheduler's worker-slot cap is entirely bypassed. Every unit returned by
  `self.graph.ready_units()` is spawned in the same pass, so `--jobs`/`max_workers`
  means nothing and a wide dependency frontier spawns as many concurrent compiler
  processes as the graph allows. This is a fork-storm / machine-overload defect,
  not a cosmetic one, and it matches the historic "oversubscription thrash"
  symptoms.
- **Fix:** maintain an explicit `var in_flight_count: i64` incremented on spawn and
  decremented on reap. This is a hot loop — do **not** use `keys().len()` here, it
  allocates an array on every scheduler iteration.

### 2. `src/compiler/99.loader/loader/module_loader.spl:828` (and `99.loader/module_loader.spl:409`, `:589`)

```
val stored_deps = self.dependency_semantic_fingerprints[path]
if stored_deps.len() != current_dependencies.len():
    return false
```

- Receivers: `stored_deps` and `current_dependencies: Dict<text, text>`
  (`module_loader.spl:401`, `:581`) — **certain**
- Class: `LOOPBOUND`/`CMPVAR` — both sides are `-1`, so `-1 != -1` is **false**
- **What breaks:** the dependency-count mismatch check **never fires**. The
  enclosing function is documented at `loader/module_loader.spl:818` as
  *"Fail-closed semantic cache validation"* — it is currently **fail-open**. A
  module whose dependency set shrank or grew still passes the freshness check
  (the subsequent per-key loop only catches *changed* or *missing* deps, never
  *extra stored* deps). Result: stale semantic cache entries are accepted and a
  rebuild is silently skipped. Three copies of this bug exist.
- **Fix:** `stored_deps.keys().len() != current_dependencies.keys().len()`. This is
  a per-module cold path, so the `keys()` allocation is acceptable.

### 3. `src/compiler/99.loader/settlement/container.spl:339`

```
if sorted.len() != self.modules.len():
    # Circular dependency — find the cycle
    ...
    return Err(ContainerError.CircularDependency(cycle))
```

- Receiver: `self.modules: Dict<text, ModuleEntry>` (`container.spl:107`) — **certain**
- Class: `CMPVAR` — `sorted` is an array (real count `N`), `self.modules.len()` is `-1`
- **What breaks:** `N != -1` is **always true**, so the topological sort **always**
  reports a circular dependency and returns `Err`. Every DI-container module
  resolution fails, even for a perfectly acyclic graph. Hard, total failure of
  this subsystem under native builds.
- **Fix:** `self.modules.keys().len()`.

### 4. `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl:345`

```
var order: [SymbolId] = []
var emitted: Dict<i64, bool> = {}
while order.len() < types.len():
```

- Receiver: `types` is a `Dict` of type defs — **certain**
- Class: `LOOPBOUND` — `0 < -1` is false
- **What breaks:** the loop body **never executes once**. `order` stays empty, so
  the VHDL type-emission ordering is empty and no user types are ever emitted into
  the design catalog. Silently produces a structurally incomplete VHDL design.
  This is the canonical "loop bound of -1 skips all work" case.
- **Fix:** hoist `val type_keys = types.keys()` before the loop and use
  `type_keys.len()` — one allocation, then a normal array bound.

### 5. `src/compiler/70.backend/backend/vhdl_backend.spl:187` and `:193`

```
if module.types.len() > 0 or module.constants.len() > 0 or self.active_tuple_type_order.len() > 0 or self.active_helper_name_by_source.len() > 0:
    builder.emit_use_package("work", "{module.name}_pkg")     # line 187 branch
    ...
    val pkg_builder = VhdlBuilder.create(module.name)          # line 193 branch
```

- Receivers: all four operands are Dicts — **certain**
- Class: `EMPTY` — every disjunct is `-1 > 0` = false, so the whole `or` chain is
  **always false**
- **What breaks:** the `use work.<module>_pkg` clause is never emitted **and** the
  package itself is never generated. The produced VHDL references types/constants
  that have no declaring package — a downstream synthesis/analysis failure, and the
  two sites are consistent with each other so it fails silently at emit time and
  loudly only in the VHDL toolchain.
- **Fix:** `keys().len()` on each (emit path, not hot).

### 6. `src/compiler/70.backend/backend/stage4_symbol_closure.spl:387` and `:420`

```
var runtime_undefined: Dict<text, bool> = {}            # :382
...
if runtime_undefined.len() != 1 or not runtime_undefined.has("rt_value_bool"):
    return Err("Stage4 runtime legacy compatibility source runtime dependencies differ from exact ABI: " + ...)
```

- Receiver: **certain** (declared `Dict<text, bool>` at `:382`)
- Class: `SIZE` — `-1 != 1` is **always true**
- **What breaks:** the ABI contract validation **always returns `Err`**, regardless
  of the actual symbol set. Stage-4 symbol-closure validation is unconditionally
  broken under native builds — a false-negative gate that blocks a correct build.
- **Fix:** `runtime_undefined.keys().len() != 1`.

### 7. `src/compiler/70.backend/backend/stage4_symbol_closure.spl:523`, `:526`, `:528`, `:565`

```
if definitions.len() != 3 or not definitions.has("spl_dlclose") or ...       # :523
if undefined.len() != 4 or not undefined.has("FreeLibrary") or ...           # :526
elif undefined.len() != 4 or not undefined.has("dlclose") or ...             # :528
if definitions.len() != expected.len():                                      # :565
```

- Receivers: `definitions` / `undefined` are dicts (assigned `dict[symbol] = true`,
  queried with `.has()`, `:517`, `:521`, `:563`) — **certain**
- Class: `SIZE` (`:523`/`:526`/`:528`), `CMPVAR` (`:565`, dict `-1` vs array `expected.len()`)
- **What breaks:** all four dynamic-loader / runtime-provider ABI contract checks
  **always return `Err`**. Same class as #6: correct object files are rejected.
- **Fix:** `keys().len()` on the dict side of each comparison.

### 8. `src/compiler/70.backend/backend/stage4_symbol_closure.spl:271`

```
if definition_counts.len() == 0:
    return Err("Stage4 compiler backfill defines no rt_cranelift_* symbols")
```

- Receiver: `definition_counts` (dict, `definition_counts[symbol] = (definition_counts[symbol] ?? 0) + 1` at `:265`) — **certain**
- Class: `EMPTY` — `-1 == 0` is **always false**
- **What breaks:** the *opposite* polarity to #6/#7 — this guard is **permanently
  inert**. A backfill object with **zero** `rt_cranelift_*` definitions sails
  through and the loop at `:273` iterates an empty key set, so the caller believes
  the contract held. Silent acceptance of a genuinely broken artifact.
- **Fix:** `definition_counts.keys().len() == 0`.

### 9. `src/compiler/99.loader/loader/module_loader.spl:250` and `:270` (also `99.loader/module_loader.spl:336`)

```
if symbols.len() == 0 and reader_exports.len() > 0:   # :250 — SMF export fallback
...
if symbols.len() == 0:                                # :270 — get_module_bytes fallback
```

- Receiver: `symbols` is a dict (`symbols[smf_sym.name] = loaded_sym`, `:246`, `:267`) — **certain**
- Class: `EMPTY` — `-1 == 0` is **always false**
- **What breaks:** **both** module-loading fallback paths are dead code. When the
  primary symbol-mapping pass yields nothing, the loader neither retries via
  `reader.exported_symbols()` nor via `provider.get_module_bytes(path)`. It returns
  a module with an empty symbol table and no error. This is a silent "module loaded
  but has no symbols" outcome — exactly the kind of thing that manifests far away
  as an unresolved-name failure.
- **Fix:** `symbols.keys().len() == 0`.

### 10. `src/compiler/40.mono/monomorphize/cache.spl:131`

```
if self.entries.len() >= self.config.max_entries:
```

- Receiver: `entries: {text: CacheEntry}` (`cache.spl:114`) — **certain**
- Class: `CMPVAR` — `-1 >= max_entries` is **always false**
- **What breaks:** the monomorphization cache **never evicts**. The cache grows
  without bound for the life of the process — an unbounded memory leak in the
  compiler's hottest allocation path. Directly relevant to the known
  stage-4 memory-balloon history.
- **Fix:** maintain a `var entry_count: i64` updated on insert/evict. This is a hot
  path — `keys().len()` per insert would be O(n) per operation.

### 11. `src/lib/nogc_async_mut/http_server/response_cache.spl:43`

```
me put(path: text, response_bytes: text, content_length: i64, now: i64):
    if self.entries.len() >= self.max_entries:
        self.evict_oldest()
```

- Receiver: `entries: Dict<text, CacheEntry>` (`response_cache.spl:18`) — **certain**
- Class: `CMPVAR` — always false
- **What breaks:** identical to #10 — the HTTP response cache never evicts.
  `max_entries` is inert and the cache grows unbounded for every distinct request
  path. A remotely-triggerable memory-exhaustion path in a server component.
- **Fix:** explicit maintained counter (hot path, per-request).

### 12. `src/compiler/80.driver/driver_build/incremental.spl:652`

```
var result: {text: text} = {}          # :639
...
if result.len() == 0:
    return nil
Some(result)
```

- Receiver: **certain** (`:639`)
- Class: `EMPTY` — always false
- **What breaks:** returns `Some(<empty dict>)` instead of `nil` when **no** cached
  MIR functions were found on disk. The caller reads this as a cache **hit** with
  zero functions rather than a miss, so the incremental build skips the work it
  should have redone.
- **Fix:** `result.keys().len() == 0`.

### 13. `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:457`, `:465`, `:760`, `:930`

```
if imported_mod.functions.len() < 0:                                          # :457  SENTINEL, ALWAYS TRUE
    ...
    if (part_src ?? imported_mod).functions.len() >= 0:                        # :465  SENTINEL, ALWAYS FALSE
val declaration_count = imported_mod.classes.len() + imported_mod.structs.len()
    + imported_mod.enums.len() + imported_mod.traits.len()
    + imported_mod.functions.len() + imported_mod.constants.len()              # :760  ARITH, = -6
if depth == 0 and declaration_count == 0 and glob_imp.items.len() == 0:        # :761  ALWAYS FALSE
elif lowered_module.constants.len() == 0 and parser_constants.len() > 0:       # :930  EMPTY, ALWAYS FALSE
```

- Receivers: `Module.{functions,classes,structs,enums,traits,constants}` are all
  `Dict<text, …>` (`src/compiler/10.frontend/parser_types.spl:25-35`) — **certain**
- **What breaks:** `:457` — every import takes the "header-only / partial module"
  re-export-chase path. `:465` — the inner recursion is then never taken, so the
  symbol is registered as an opaque placeholder (`:469`). `:760`/`:761` — the sum is
  `-6`, so the nested glob-import descent never happens. `:930` — the constant
  recovery path is inert, so a module whose HIR constants failed to lower is never
  repaired.
- **Fix:** `keys().len()`; for `:457`/`:465` the intent is a nil/empty-dict test, so
  prefer restructuring around an explicit "header-only" flag on `Module` rather
  than inferring it from a count.
- **NOTE:** see the ancestry warning at the top — `:457` and `:760` are already
  fixed on a tip that is not an ancestor of this `HEAD`.

### 14. `src/compiler/80.driver/watcher/smf_manifest.spl:125`

```
if manifest.entries.len() > 0:
    lines.push("entries |source_path, smf_path, source_hash, ...")
    for key in manifest.entries.keys():
        ...
```

- Receiver: `entries: Dict<text, SmfManifestEntry>` (`smf_manifest.spl:38`) — **certain**
- Class: `EMPTY` — `-1 > 0` is **always false**
- **What breaks:** the SMF manifest is **always serialized with an empty entries
  section**, even when entries exist. The watcher then reads back a manifest that
  claims nothing is compiled, so every incremental watch cycle recompiles
  everything (or worse, loses the source→SMF mapping entirely).
- **Fix:** `manifest.entries.keys().len() > 0` — or just drop the guard and let the
  `for` loop over `.keys()` handle the empty case, since `.keys()` is already correct.

### 15. `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:249` and `src/compiler/80.driver/driver_bootstrap.spl:307`

```
if self.unknown_func_decls.len() > 0:
    self.builder.emit("")
    self.builder.emit("; External call declarations")
    for unknown_name in self.unknown_func_decls.keys():
        ... emit "declare ... @{unknown_name}(...)"
```

- Receiver: `unknown_func_decls: Dict<text, bool>`
  (`src/compiler/70.backend/backend/_MirToLlvm/class_def.spl:61`) — **certain**
- Class: `EMPTY` — always false
- **What breaks:** the `declare` block for externally-called functions is **never
  emitted** into the generated LLVM IR. Any module that calls an undeclared external
  produces IR that `llc` rejects (or, worse, that links against an implicit wrong
  signature). Both the mainline codegen path and the bootstrap trailer path have
  the same bug, so there is no fallback.
- **Fix:** `keys().len() > 0`, or drop the guard entirely — the `for` over `.keys()`
  below it is already correct and the only cost is two stray blank/comment lines.

---

## Remaining confirmed sites (16–75)

### `src/compiler/**` (rest of tier 0)

| file:line | expression | conf. | class | what breaks | replacement |
|---|---|---|---|---|---|
| `src/compiler/80.driver/driver_build/parallel.spl:257` | `if in_flight_pid.len() == 0: return (-1, -1)` | certain | EMPTY | `wait_for_finished_process` never short-circuits on an empty in-flight set; burns its full bounded-poll budget every call before returning `(-1,-1)` anyway | maintained counter |
| `src/compiler/80.driver/driver_build/parallel.spl:466` | `if in_flight_pid.len() == 0:` | certain | EMPTY | drain/completion check never fires — scheduler loop keeps polling after all work is reaped | maintained counter |
| `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl:553` | `if modules.len() == 0:` | certain | EMPTY | the "VHDL design catalog requires at least one MIR module" precondition is inert; an empty input produces an empty catalog instead of a clear `Err` | `modules.keys().len()` |
| `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl:966` | `helper_function_count: functions.len() - hardware_entity_count,` | certain | ARITH | reported helper-function count is `-1 - hardware_entity_count`, i.e. negative garbage in the emitted catalog metadata | `functions.keys().len()` |
| `src/compiler/70.backend/backend/vhdl_validation.spl:646` | `if self.active_helper_name_by_source.len() > 0:` | likely | EMPTY | helper-name validation block never runs — VHDL helper collisions go unchecked | `keys().len()` |
| `src/compiler/70.backend/backend/stage4_symbol_closure.spl:565` | `if definitions.len() != expected.len():` | certain | CMPVAR | dict `-1` vs array `N` — exact-ABI count check always `Err`s (see #7) | `definitions.keys().len()` |
| `src/compiler/60.mir_opt/mir_opt/_Inline/driver.spl:274` | `if inline_candidates.len() == 0: return module` | certain | EMPTY | early-out never taken; the inliner walks every function with an empty candidate set. Wasted work rather than wrong output, but it defeats the fast path on every module | `keys().len()` |
| `src/compiler/40.mono/monomorphize/metadata.spl:61-64` | `(self.functions.len() + self.structs.len() + self.classes.len() + self.enums.len() + …)` | certain | ARITH | generic-metadata total is `-4` plus the real remainder — any reporting or capacity decision built on it is garbage | `keys().len()` per operand, or 4 maintained counters |
| `src/compiler/90.tools/context_pack.spl:71` | `pack.symbol_count = pack.functions.len() + pack.types.len()` | certain | ARITH | `symbol_count` is `-2`; context-pack sizing/reporting is wrong | `keys().len()` |
| `src/compiler/90.tools/coupling/api_quality.spl:22` | `if counts.len() == 0:` | likely | EMPTY | empty-input guard inert; downstream divides/averages over an empty key set | `keys().len()` |
| `src/compiler/25.traits/trait_coherence.spl:100` | `val suggestion = if self.local_types.len() > 0:` | certain (`{text: bool}` at `:59`) | EMPTY | the "Create a newtype wrapper in your module" hint is never attached to an orphan-impl error. Cosmetic — diagnostic quality only | `keys().len()` |
| `src/compiler/00.common/effects.spl:381` | `assert env.builtins.len() > 0` | certain (`builtins: Dict<text, EffectTag>` at `:98`) | EMPTY | **a test assertion that always fails** under native codegen — `test_effect_env_basic` is a false red | `env.builtins.keys().len() > 0` |
| `src/compiler/99.loader/module_loader.spl:407`, `:587` | `return current_dependencies.len() == 0` | certain | EMPTY | always returns `false` (cache-not-fresh) when no stored dep fingerprints exist. Conservative direction — causes needless rebuilds, not staleness | `keys().len()` |
| `src/compiler/99.loader/loader/module_loader.spl:825` | `return current_dependencies.len() == 0` | certain | EMPTY | same as above, conservative | `keys().len()` |

### `src/lib/**` (tier 1)

| file:line | expression | conf. | class | what breaks | replacement |
|---|---|---|---|---|---|
| `src/lib/nogc_sync_mut/i18n/bundle.spl:76` | `if msgs.len() == 0 and fallback.len() == 0:` (**two** dict receivers, `Dict<text,text>` at `:68`/`:60`) | certain | EMPTY | the "No i18n bundle found" error **never fires**; `ResourceBundle` is returned `Ok` with both message maps empty, so every lookup silently falls through to the raw key | `keys().len()` on both |
| `src/lib/nogc_sync_mut/test_runner/doc_generator.spl:285` | `if subcategories.len() > 1:` (`Dict<text,bool>` at `:278`) | certain | SIZE | the `## Subcategories` section is **never** emitted in generated feature docs, regardless of how many subcategories exist | `keys().len()` |
| `src/lib/gc_async_mut/web/browser_session.spl:1002` | `val changed = changes.len() > 0` | certain | EMPTY | `changed` is always `false`, so `_apply_dom_changes` is **never called** — DOM mutations are computed and then discarded; the sync returns the unmodified root | `keys().len()` |
| `src/lib/common/json/parser.spl:387` | `if pairs.len() > 0:` (`{text: any}` at `:381`) | certain | EMPTY | a parsed JSON object with members is treated as having none — object emptiness is inverted in the parser's post-processing | `keys().len()` |
| `src/lib/nogc_sync_mut/spec/condition.spl:261` | `if env_vars.len() == 0:` (`{text: text}` at `:259`) | certain | EMPTY | the "no env constraints → match" fast path is inert; matching proceeds into a loop over `.keys()` which happens to be empty, so the observable result is usually the same but the intent is lost | `keys().len()` |
| `src/lib/gc_async_mut/spec/condition.spl:261` | same | certain | EMPTY | duplicate of the above (tier copy) | `keys().len()` |
| `src/lib/nogc_async_mut/spec/condition.spl:261` | same | certain | EMPTY | duplicate of the above (tier copy) | `keys().len()` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:305` | `if old.entries.len() > 0:` (`entries: {text: TestCacheEntry}`) | certain | EMPTY | the old test-duration cache is treated as empty, so duration-based test ordering never uses prior data — every run reorders from scratch | `keys().len()` |

### `src/app/**` (tier 2)

| file:line | expression | conf. | class | what breaks | replacement |
|---|---|---|---|---|---|
| `src/app/interpreter/collections/persistent_dict_spec.spl:11` | `assert dict.len() == 0` | certain | EMPTY | **test assertion always fails** natively | `dict.keys().len()` |
| `…:52` | `assert dict.len() == 3` | certain | SIZE | always fails | `keys().len()` |
| `…:63` | `assert dict.len() == 1` | certain | SIZE | always fails | `keys().len()` |
| `…:113` | `assert dict.len() == 1000` | certain | SIZE | always fails | `keys().len()` |
| `…:175` | `assert dict.len() == 3` | certain | SIZE | always fails | `keys().len()` |
| `…:257` | `assert dict.len() == 100` | certain | SIZE | always fails | `keys().len()` |

> These six are the **canary suite**: they are the cheapest existing signal for
> whether the underlying `Dict.len()` defect is fixed. They should pass in the
> interpreter and fail natively today. Do not "fix" them by switching to
> `keys().len()` — that would delete the only regression detector for the root bug.
> Root-fix `.len()` lowering instead.

### `src/compiler_rust/lib/std/**` (seed stdlib `.spl`, non-vendor, tier 4)

Lower priority — this is the seed's bundled stdlib, only reachable when that copy
is compiled natively. All are `EMPTY`/`ARITH` on `self.<dict-field>`.

| file:line | expression | conf. | class |
|---|---|---|---|
| `src/compiler_rust/lib/std/src/cli/parsed_args.spl:22` | `return self.flags.len() > 0` | certain | EMPTY — `has_flags()` always `false` |
| `src/compiler_rust/lib/std/src/cli/parsed_args.spl:26` | `return self.options.len() > 0` | certain | EMPTY — `has_options()` always `false` |
| `src/compiler_rust/lib/std/src/core/json.spl:116` | `case Object(obj): obj.len() > 0` | certain | EMPTY — non-empty JSON object reads as empty |
| `src/compiler_rust/lib/std/src/core/json_serialize.spl:152` | `return self.obj.len() == 0` | certain | EMPTY — `is_empty()` always `false` |
| `src/compiler_rust/lib/std/src/core/json_serialize.spl:156` | `return self.obj.len() > 0` | certain | EMPTY — always `false`; both accessors agree on the wrong answer |
| `src/compiler_rust/lib/std/src/core/set.spl:72` | `self.elements.len() == 0` | certain | EMPTY — `Set.is_empty()` always `false` |
| `src/compiler_rust/lib/std/src/infra/config_env.spl:212` | `return self.data.len() == 0` | certain | EMPTY |
| `src/compiler_rust/lib/std/src/tooling/config_env.spl:184` | `return self.data.len() == 0` | certain | EMPTY (duplicate copy) |
| `src/compiler_rust/lib/std/src/tooling/core/dependency.spl:236` | `self.nodes.len() == 0` | certain | EMPTY |
| `src/compiler_rust/lib/std/src/tooling/core/dependency.spl:244` | `self.nodes.len() > 0` | certain | EMPTY |
| `src/compiler_rust/lib/std/src/tooling/core/dependency.spl:318` | `if node.dependencies.len() == 0:` | certain | EMPTY — **topological-sort root detection never finds a root** |
| `src/compiler_rust/lib/std/src/tooling/core/dependency.spl:610` | `self.dependencies.len() > 0` | certain | EMPTY |
| `src/compiler_rust/lib/std/src/tooling/core/dependency.spl:646` | `self.dependencies.len() == 0` | certain | EMPTY |
| `src/compiler_rust/lib/std/src/tooling/core/incremental.spl:527` | `self.entries.len() == 0` | certain | EMPTY |
| `src/compiler_rust/lib/std/src/tooling/deployment/packaging.spl:398` | `self.scripts.len() > 0` | certain | EMPTY |
| `src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:500` | `self.pending_changes.len() > 0` | certain | EMPTY — pending changes never flushed |
| `src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:576` | `if self.pending_changes.len() == 0:` | certain | EMPTY |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/coverage.spl:280` | `"Symbols covered: " + coverage.symbol_coverage.len().to_string()` | likely | ARITH — coverage report prints `-1` |

---

## Verified NOT affected (checked and cleared)

These looked like hits in the mechanical pass but the receiver is an **array** or
**text**, where `.len()` is correct. Recorded so a later pass does not re-flag them:

- `src/compiler/70.backend/backend/stage4_symbol_closure.spl:327`, `:701`, `:874` —
  `localize` / `definitions` here are `[text]` (`.join(", ")`, `.push(symbol)`).
- `src/compiler/60.mir_opt/mir_opt/outline.spl:348`, `:442` — `cold_blocks` is an
  array (`cold_blocks.push(...)`).
- `src/compiler/80.driver/driver_build/incremental.spl:48`, `:50` — that `result` is
  `var result = values` where `values: [text]`; a *different* `result` at `:639` is
  the dict.
- `src/compiler/30.types/associated_types_defs.spl:356`,
  `associated_types_phase4d.spl:226` — `assoc_type_constraints: text`
  (`associated_types_defs.spl:323`), a text-encoded dict; `.len()` is a string length.
- `src/lib/nogc_sync_mut/ui/theme_package.spl:407`, `:409` — `out` is an array.
- `src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/http/headers.spl:393-394` —
  `singletons = singleton_header_names()` returns `[text]`.
- `src/lib/common/compress/lzma2_*.spl`, `src/lib/common/encoding/sfnt_glyf.spl` —
  the locals named `dict` / `meta` are byte/i64 arrays.
- `src/app/check/targets.spl:23`, `src/app/check/main.spl:82` — `discovered` is the
  array returned by `discover_spl_files`.

## Campaign files explicitly re-checked (task item 5)

| file | dict-`.len()` sites found |
|---|---|
| `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` | **4** — `:457`, `:465`, `:760`, `:930` (see #13). `:457`/`:760` are the two already fixed on a non-ancestor tip. `:930` is **new** and not covered by either commit. All other `.len()` uses in this file are on arrays (`imports`, `exports`, `items`, `params`, `keys()` results) and are fine. |
| `src/compiler/80.driver/driver.spl` | **0** — every `.len()` comparison here is on `ctx.errors: [text]` (`driver_types.spl:47`), `ctx.sources: [SourceFile]` (`:40`), `driver_inputs: [text]` (`:443`), or `closure_loaded`/`bulk_loaded` (arrays, iterated with `for`). `ctx.modules: Dict<text, Module>` (`:42`) exists but its `.len()` is never taken. **Clean.** |
| `src/compiler/80.driver/driver_source_loading.spl` | **0** — all 14 comparison sites are on `[text]` arrays or `text` (`parts`, `bytes`, `buckets`, `module_path`, `quote_parts`, `_skip_dirs`). **Clean.** |
| `src/compiler/20.hir/hir_lowering/expressions.spl` | **0** — `.len()` sites are on `name: text` and `args: [..]`. **Clean.** |

---

## How to avoid this in future work

1. **Never take `.len()` on a `Dict` in Simple code until the root defect lands.**
   The bug is in `.len()`/`.length()` lowering
   (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1287+`), where an
   erased receiver falls through to `rt_len` → `rt_string_len`, which returns `-1`
   for a non-string handle (`src/runtime/runtime_native.c:1741-1745`).

2. **Pick the replacement by call frequency, not by taste:**
   - **membership** → `d.contains_key(k)` / `d.has(k)` — correct today, allocation-free.
   - **cold-path count** → `d.keys().len()` — correct today, but **allocates the key
     array**. Fine once per module/file/request.
   - **hot-path count** (per-iteration scheduler bounds, per-insert cache caps) →
     an explicit `var count: i64` maintained on insert/remove. `keys().len()` in a
     loop condition turns an O(1) check into O(n) *per iteration*.
   - **loop over contents** → iterate `for k in d.keys():` directly and delete the
     surrounding `len() > 0` guard entirely. `.keys()` is correct, and an empty
     `for` is already a no-op — the guard buys nothing and is the single most
     common shape in this sweep (43 of 75 hits are `EMPTY`).

3. **`len() < 0` / `len() >= 0` is never a legitimate test.** A length cannot be
   negative, so these were already dead code *before* this bug — they were written
   as nil/erased-receiver probes. Two of them (`module_lowering.spl:457`, `:465`)
   are exactly how this defect stayed hidden: the author read `-1` as "signal", not
   as "wrong". Encode nil-ness as an explicit `Option` or a boolean field on the
   struct, never as a sentinel length.

4. **Watch for the `LOOPBOUND` shape specifically.** `while i < d.len():` with
   `d.len() == -1` does not error, does not warn, and does not loop — it silently
   completes having done nothing. `vhdl_design_catalog.spl:345` is the live example.
   Any "the output is mysteriously empty" bug should check for a dict on the right
   side of a loop bound first.

5. **Mixed comparisons are the sneakiest.** `array.len() != dict.len()` compares a
   real count against `-1` and is therefore *always true* — which flips a
   consistency check into an unconditional failure (`container.spl:339`) or an
   unconditional pass (`module_loader.spl:828`, where both sides are `-1`).
   When auditing, resolve **both** operands, not just the obvious one.

6. **Suggested lint (not implemented):** flag any `.len()` whose receiver resolves
   to `Dict<…>` or the `{K: V}` shorthand. Note the shorthand form — `{text: bool}`,
   `{i64: i64}` — is easy to miss with a naive `Dict<` grep; it accounted for 22 of
   the 75 sites found here, including the worst one (`parallel.spl:428`).

## Method / reproduction

Read-only static sweep. Receiver types were resolved by (a) file-local declarations
(`name: Dict<…>`, `name: {K: V}`, `= {}` initializers), then (b) a repo-wide
declaration index for struct fields used as `x.field.len()`, then (c) manual reading
of the declaration site for every reported hit. Sites whose receiver resolved to an
array or text in the same file were dropped. Confidence is `certain` when the
declaration was read directly, `likely` when the name has exactly one dict
declaration repo-wide and no conflicting array/text declaration.

**No source file was modified by this sweep.**
