# `Dict.get()` struct-value corruption — repo-wide exposure sweep (2026-07-27)

Reconnaissance only. **No code was changed by this sweep.**

Related bug: `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
Only known fix so far: `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` (commit `9b612a11418c`).

## 1. The defect being swept for

Under the **native** backend:

| Operation | Behaviour |
|---|---|
| `d.get(k)` — **miss** | correct, returns `nil` |
| `d.get(k)` — **hit**, `V` = struct/class/enum | returns non-nil `Option` with a **CORRUPT payload**. `.unwrap()` or any field/method read **SEGFAULTS** |
| `d.get(k)` — **hit**, `V` = `i64` | returns the still-**BOXED** value (`7` reads back as `56` = `7<<3`) — wrong number, no crash |
| `d.contains_key(k)` | correct |
| `d.keys()` | correct |
| `d[k]` (indexed read) | correct |
| `Some(d[k])` | correct, incl. through an `Option`-typed parameter |

Consequence: the **only** safe read shape today is
`if d.contains_key(k): val v = d[k]` (and `Some(d[k])` where an `Option` is genuinely required).

This is exactly the deterministic stage-4 segfault at HIR module 32
(`traits.get(name)` → `lower_trait(as_trait.unwrap())`).

## 2. Method + coverage

- Corpus: **13,637** tracked `.spl` files under `src/`, excluding `src/compiler_rust/vendor/**` and `src/runtime/vendor/**`.
- **Two** Dict declaration syntaxes are used in this repo and both were swept:
  1. `name: Dict<K, V>`
  2. `name: {K: V}` — the shorthand form (e.g. `src/compiler/40.mono/monomorphize/deferred.spl:131` `template_cache: {text: GenericTemplate}`). *A sweep that only looks for `Dict<` misses roughly a third of the exposure, including four CRITICAL monomorphizer sites.*
- Receiver→value-type resolution: same-file declaration first (**HIGH** confidence), then a repo-global name→value-type map (**MED**), with names that are also declared as non-Dict types anywhere in the repo demoted to **LOW** (e.g. `properties`, which is `[JsProperty]` in `src/lib/common/js/types/js_types.spl:31` but `Dict<text, ConfigProperty>` in `src/compiler_rust/lib/std/src/vscode/manifest.spl:324` — the 31 `src/lib/common/js/builtins/object.spl` hits are List indexing, **not** Dict, and are excluded from the confident set).
- Severity was assigned by reading the call line plus 14 lines of lookahead on the bound name.

### Confidence legend

| Conf | Meaning |
|---|---|
| HIGH | Dict declaration for that receiver name is in the **same file** — treat as confirmed |
| MED | Resolved via repo-global name map, no conflicting non-Dict declaration anywhere — very likely real, verify the declaring type before fixing |
| LOW | Name also declared as a non-Dict type somewhere (List/array/struct) — needs manual triage, listed separately in §6 |

## 3. Summary counts

### Confident set (HIGH + MED confidence), struct/class/enum value types

| Severity | Count | What happens |
|---|---|---|
| **CRITICAL** | **193** | result is `.unwrap()`ed, destructured via `Some(v)`/`match`, or a field/method is read → **segfault** |
| **HIGH** | **85** | result flows onward (returned, or passed to a callee expecting the struct) → corrupt data propagates silently |
| **MEDIUM** | **60** | only compared `!= nil` / `== nil` in the observed window → behaves today, unsafe on any later use |
| **Confident total** | **338** | |

### Severity × tier

| Tier | CRITICAL | HIGH | MEDIUM |
|---|---|---|---|
| `src/compiler/**` | 11 | 8 | 13 |
| `src/lib/**` | 85 | 22 | 40 |
| `src/compiler_rust/lib/std/**` (seed-bundled std, `.spl`) | 55 | 45 | 2 |
| `src/app/**` | 40 | 10 | 4 |
| `src/os/**` | 2 | 0 | 1 |

### Other buckets

| Bucket | Count | Notes |
|---|---|---|
| **LOW severity** (`V` is a scalar: `text`/`i64`/`bool`/`f64`/…) | **651** | returns a boxed/undecoded value — wrong number, no crash. §7 |
| **LOW confidence** (needs manual triage) | **262** | receiver name collides with a non-Dict declaration elsewhere. §6 |

## 4. Top 20 — ranked by severity, then hot-path likelihood

All 20 are **CRITICAL** (segfault on the hit path). Ordered `src/compiler/**` → `src/os` + `src/lib/**` → `src/app/**`.

### Tier 1 — `src/compiler/**` (every one of these is on a compile path)

**1. `src/compiler/40.mono/monomorphize/deferred.spl:313`** — conf HIGH, `template_cache: {text: GenericTemplate}` (declared `:131`)
```
313:         val template = self.template_cache.get(name)
314:         if template == nil:
...
318:         val func_template = template.as_function()
```
Failure: on a cache **hit**, `template` is non-nil so the `nil` guard passes, then `template.as_function()` at `:318` dereferences the corrupt payload → segfault in the monomorphizer.
Fix:
```
if not self.template_cache.contains_key(name):
    deferred_set_error("Template not found: {name}")
    return nil
val template = self.template_cache[name]
```

**2. `src/compiler/40.mono/monomorphize/deferred.spl:375`** — identical shape, deref at `:380`. Same fix.

**3. `src/compiler/40.mono/monomorphize/deferred.spl:437`** — identical shape, deref at `:442`. Same fix.

**4. `src/compiler/40.mono/monomorphize/deferred.spl:499`** — identical shape, deref at `:504`. Same fix.

**5. `src/compiler/30.types/type_system/checker.spl:284`** — conf HIGH, `trait_impls: Dict<…, TraitImplRegistry>`
```
284:         val reg = match self.trait_impls.get(trait_name):
285:             case Some(value):
286:                 value
...
291:         if not reg.specific_impls.contains(source_type) and not reg.blanket_impl:
```
Failure: `case Some(value)` binds the corrupt payload; `reg.specific_impls` at `:291` segfaults. Every `dyn` coercion check on a registered trait hits this.
Fix:
```
if not self.trait_impls.contains_key(trait_name):
    return Err(TypeError.Other("type '{source_type}' does not implement trait '{trait_name}' (required for dyn coercion)"))
val reg = self.trait_impls[trait_name]
```

**6. `src/compiler/30.types/type_system/checker.spl:306`** — conf HIGH, `mixins: Dict<…, MixinInfo>`
```
305:     fn get_mixin(name: text) -> MixinInfo?:
306:         match self.mixins.get(name):
307:             case Some(info):
308:                 Some(info)
```
Failure: `info` is the corrupt payload and is handed straight back to every caller of `get_mixin`.
Fix: `if self.mixins.contains_key(name): Some(self.mixins[name]) else: nil`

**7. `src/compiler/35.semantics/const_keys.spl:318`** — conf HIGH, `templates: Dict<…, TemplateAnalysis>`
```
318:         match self.templates.get(template_var):
319:             case Some(analysis):
320:                 if analysis.can_validate():
```
Failure: `analysis.can_validate()` at `:320` on the corrupt payload → segfault on every `.with{}` check against a known template.
Fix: `if self.templates.contains_key(template_var): val analysis = self.templates[template_var]` then the existing body.

**8. `src/compiler/99.loader/module_resolver/manifest.spl:57`** — conf MED, `manifests: Dict<…, DirectoryManifest>`
```
57:         val cached = self.manifests.get(init_path)
58:         if cached != nil:
59:             return Ok(cached.clone())
```
Failure: the comment at `:55-56` already records that this cache "was silently dead". Now that it is live, every cache **hit** calls `.clone()` on a corrupt payload → segfault in module resolution.
Fix: `if self.manifests.contains_key(init_path): return Ok(self.manifests[init_path].clone())`

**9. `src/compiler/99.loader/module_resolver/resolution.spl:384`** — conf MED, same `manifests` Dict
```
384:             val manifest = self.manifests.get(init_path)
385:             if manifest != nil:
386:                 uses.extend(manifest.common_uses.clone())
```
Failure: `manifest.common_uses` at `:386` on the corrupt payload → segfault. Same fix shape.

**10. `src/compiler/70.backend/backend/vhdl_validation.spl:114`** — conf MED, `active_function_by_name: Dict<…, MirFunction>`
```
114:         val known = self.active_function_by_name.get(from)
115:         if not known.? or not self.active_helper_name_by_source.has(from):
119:         for block in known.unwrap().blocks:
```
Failure: `known.?` is true on a hit, so `known.unwrap().blocks` at `:119` segfaults.
Fix: `if not self.active_function_by_name.contains_key(from) or not …: return false` then `val known = self.active_function_by_name[from]` and iterate `known.blocks`.

**11. `src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:394`** — conf MED, identical shape, `.unwrap()` at `:399`. Same fix.

### Tier 2 — `src/os/**` and `src/lib/**`

**12. `src/os/compositor/host_compositor_core.spl:702`** — conf HIGH, `content_caches: Dict<…, WebRenderPixelArtifactCache>`
```
702:         val existing = self.content_caches.get(window_id)
703:         if existing != nil and existing.width == cw and existing.height == full_h and existing.backend_name == backend_name:
```
Failure: `existing.width` on the same line as the nil check reads the corrupt payload → segfault on every warm frame of the host compositor.
Fix: `if self.content_caches.contains_key(window_id): val existing = self.content_caches[window_id]` then the width/height/backend comparison.

**13. `src/os/compositor/host_compositor_core.spl:880`** — conf HIGH, same Dict, field read at `:882`. Same fix.

**14. `src/lib/gc_async_mut/engine/render/gpu_texture_cache.spl:26`** — conf HIGH, `entries: Dict<…, GpuTexture>`
```
26:         if val Some(gpu_tex) = self.entries.get(key):
```
Failure: the refutable `Some(…)` binding takes the corrupt payload on every texture-cache hit.
Fix: `if self.entries.contains_key(key): val gpu_tex = self.entries[key]`

**15. `src/lib/gc_async_mut/engine/render/gpu_texture_cache.spl:44`** — conf HIGH, `if val Some(_) = self.entries.get(key)`. Because the payload is discarded this one *happens* not to crash — but it is still the wrong primitive; replace with a bare `self.entries.contains_key(key)`.

**16. `src/lib/nogc_async_mut/async_host/scheduler.spl:245`** — conf HIGH, `tasks: Dict<…, HostTask>`
```
245:         match self.tasks.get(id):
```
Failure: `case Some(task)` binds a corrupt `HostTask` on the async host scheduler's lookup path.
Fix: `if self.tasks.contains_key(id): val task = self.tasks[id]`

**17. `src/lib/nogc_sync_mut/engine/audio/audio_group.spl`** (8 CRITICAL sites) — conf HIGH, `AudioGroup`-valued Dict. Every group lookup dereferences the corrupt payload. Same `contains_key` + index fix per site.

**18. `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl`** (6 CRITICAL sites) — conf HIGH, `AudioBus`/`AudioClip`/`Sound`-valued Dicts. Same fix.

**19. `src/lib/nogc_sync_mut/database/db_registry.spl`** + `src/lib/nogc_async_mut/database/db_registry.spl` (4 CRITICAL each) — conf HIGH, `SdnDatabase`-valued Dict; every registry hit dereferences the corrupt handle. Same fix.

**20. `src/lib/nogc_sync_mut/database/sql/stmt_cache.spl`** (4 CRITICAL) — conf HIGH, `PreparedStatement`-valued Dict; a prepared-statement cache **hit** segfaults, a miss re-prepares correctly — i.e. the bug only shows under load. Same fix.

### Tier 3 — `src/app/**` (just outside the top 20, but the single densest file in the repo)

`src/app/interpreter/async_runtime/actor_scheduler.spl` — **21 CRITICAL sites** (`:506, :527, :539, :554, :602, :611, :619, :628, :644, :659, :660, :669, :670, :681, :682, :691, :692, …`), all `val act = self.actors.get(<id>)` followed by `act.unwrap()` 2-4 lines later, on `actors: Dict<…, ActorContext>`. This is the interpreter's actor runtime: **every** actor send/link/monitor operation on a live actor takes the corrupt path.
Fix per site: `if not self.actors.contains_key(id): <existing miss branch>` then `val act = self.actors[id]` and drop the `.unwrap()`.

`src/app/debug/remote/breakpoint_manager.spl:156, :165, :238, :250` — conf HIGH, `breakpoints: Dict<text, BreakpointInfo>`, field read 2 lines after each `get`. Same fix.

## 5. Full confident-set table (338 sites)

Ordered CRITICAL → HIGH → MEDIUM, then `src/compiler` → `src/lib`+`src/os`+`src/compiler_rust` → `src/app`.

| Site | Receiver | Value type (conf) | Severity | What breaks | Mechanical fix |
|---|---|---|---|---|---|
| `src/compiler/30.types/type_system/checker.spl:284` | `trait_impls` | `TraitImplRegistry` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if trait_impls.contains_key(k): val v = trait_impls[k]` |
| `src/compiler/30.types/type_system/checker.spl:306` | `mixins` | `MixinInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if mixins.contains_key(k): val v = mixins[k]` |
| `src/compiler/35.semantics/const_keys.spl:318` | `templates` | `TemplateAnalysis` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if templates.contains_key(k): val v = templates[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:313` | `template_cache` | `GenericTemplate` (HIGH) | CRITICAL | field/method on bound Option at line 318 | `if template_cache.contains_key(k): val v = template_cache[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:375` | `template_cache` | `GenericTemplate` (HIGH) | CRITICAL | field/method on bound Option at line 380 | `if template_cache.contains_key(k): val v = template_cache[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:437` | `template_cache` | `GenericTemplate` (HIGH) | CRITICAL | field/method on bound Option at line 442 | `if template_cache.contains_key(k): val v = template_cache[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:499` | `template_cache` | `GenericTemplate` (HIGH) | CRITICAL | field/method on bound Option at line 504 | `if template_cache.contains_key(k): val v = template_cache[k]` |
| `src/compiler/70.backend/backend/vhdl_validation.spl:114` | `active_function_by_name` | `MirFunction` (MED) | CRITICAL | unwrap of bound Option at line 119 | `if active_function_by_name.contains_key(k): val v = active_function_by_name[k]` |
| `src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:394` | `active_function_by_name` | `MirFunction` (MED) | CRITICAL | unwrap of bound Option at line 399 | `if active_function_by_name.contains_key(k): val v = active_function_by_name[k]` |
| `src/compiler/99.loader/module_resolver/manifest.spl:57` | `manifests` | `DirectoryManifest` (MED) | CRITICAL | field/method on bound Option at line 59 | `if manifests.contains_key(k): val v = manifests[k]` |
| `src/compiler/99.loader/module_resolver/resolution.spl:384` | `manifests` | `DirectoryManifest` (MED) | CRITICAL | field/method on bound Option at line 386 | `if manifests.contains_key(k): val v = manifests[k]` |
| `src/compiler_rust/lib/std/src/diagram/arch_gen.spl:372` | `entities` | `ArchEntity` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if entities.contains_key(k): val v = entities[k]` |
| `src/compiler_rust/lib/std/src/diagram/arch_gen.spl:384` | `entities` | `ArchEntity` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if entities.contains_key(k): val v = entities[k]` |
| `src/compiler_rust/lib/std/src/diagram/class_gen.spl:216` | `methods` | `MethodInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if methods.contains_key(k): val v = methods[k]` |
| `src/compiler_rust/lib/std/src/diagram/class_gen.spl:249` | `classes` | `ClassInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if classes.contains_key(k): val v = classes[k]` |
| `src/compiler_rust/lib/std/src/diagram/class_gen.spl:294` | `classes` | `ClassInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if classes.contains_key(k): val v = classes[k]` |
| `src/compiler_rust/lib/std/src/diagram/sequence_gen.spl:139` | `participants` | `Participant` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if participants.contains_key(k): val v = participants[k]` |
| `src/compiler_rust/lib/std/src/diagram/sequence_gen.spl:145` | `participants` | `Participant` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if participants.contains_key(k): val v = participants[k]` |
| `src/compiler_rust/lib/std/src/lms/auth.spl:389` | `roles` | `Role` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if roles.contains_key(k): val v = roles[k]` |
| `src/compiler_rust/lib/std/src/lms/auth.spl:429` | `roles` | `Role` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if roles.contains_key(k): val v = roles[k]` |
| `src/compiler_rust/lib/std/src/lms/workspace.spl:137` | `files` | `FileMetadata` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if files.contains_key(k): val v = files[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:143` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:153` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:162` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:453` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:459` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:465` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:495` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:502` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:509` | `obj` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/mcp_extended.spl:54` | `entries` | `CacheEntry` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:414` | `symbols` | `QualifiedSymbol` (HIGH) | CRITICAL | field/method on bound Option at line 415 | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:423` | `symbols` | `QualifiedSymbol` (HIGH) | CRITICAL | field/method on bound Option at line 424 | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:488` | `symbols` | `QualifiedSymbol` (HIGH) | CRITICAL | field/method on bound Option at line 489 | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/compiler_rust/lib/std/src/mcp/tooling.spl:268` | `running_tasks` | `Task` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if running_tasks.contains_key(k): val v = running_tasks[k]` |
| `src/compiler_rust/lib/std/src/sdn/query.spl:104` | `fields` | `SdnValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if fields.contains_key(k): val v = fields[k]` |
| `src/compiler_rust/lib/std/src/sdn/query.spl:59` | `fields` | `SdnValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if fields.contains_key(k): val v = fields[k]` |
| `src/compiler_rust/lib/std/src/sdn/query.spl:68` | `fields` | `SdnValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if fields.contains_key(k): val v = fields[k]` |
| `src/compiler_rust/lib/std/src/sdn/query.spl:77` | `fields` | `SdnValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if fields.contains_key(k): val v = fields[k]` |
| `src/compiler_rust/lib/std/src/sdn/query.spl:86` | `fields` | `SdnValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if fields.contains_key(k): val v = fields[k]` |
| `src/compiler_rust/lib/std/src/sdn/query.spl:95` | `fields` | `SdnValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if fields.contains_key(k): val v = fields[k]` |
| `src/compiler_rust/lib/std/src/spec/formatter/html.spl:154` | `spec_results` | `Any` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if spec_results.contains_key(k): val v = spec_results[k]` |
| `src/compiler_rust/lib/std/src/spec/formatter/html.spl:191` | `spec_results` | `Any` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if spec_results.contains_key(k): val v = spec_results[k]` |
| `src/compiler_rust/lib/std/src/spec/formatter/html.spl:222` | `spec_results` | `Any` (HIGH) | CRITICAL | method/field chained on get() result | `if spec_results.contains_key(k): val v = spec_results[k]` |
| `src/compiler_rust/lib/std/src/spec/formatter/html.spl:223` | `spec_results` | `Any` (HIGH) | CRITICAL | method/field chained on get() result | `if spec_results.contains_key(k): val v = spec_results[k]` |
| `src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:186` | `spec_results` | `Any` (HIGH) | CRITICAL | method/field chained on get() result | `if spec_results.contains_key(k): val v = spec_results[k]` |
| `src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:190` | `spec_results` | `Any` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if spec_results.contains_key(k): val v = spec_results[k]` |
| `src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:197` | `spec_results` | `Any` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if spec_results.contains_key(k): val v = spec_results[k]` |
| `src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:238` | `spec_results` | `Any` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if spec_results.contains_key(k): val v = spec_results[k]` |
| `src/compiler_rust/lib/std/src/spec/gherkin.spl:425` | `variables` | `Any` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if variables.contains_key(k): val v = variables[k]` |
| `src/compiler_rust/lib/std/src/spec/runtime.spl:37` | `memoized` | `Any` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if memoized.contains_key(k): val v = memoized[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/dependency.spl:389` | `nodes` | `DependencyNode` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if nodes.contains_key(k): val v = nodes[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/dependency.spl:446` | `nodes` | `DependencyNode` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if nodes.contains_key(k): val v = nodes[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl:455` | `msg` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if msg.contains_key(k): val v = msg[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl:465` | `msg` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if msg.contains_key(k): val v = msg[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl:474` | `msg` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if msg.contains_key(k): val v = msg[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl:660` | `msg` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if msg.contains_key(k): val v = msg[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl:665` | `msg` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if msg.contains_key(k): val v = msg[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl:674` | `msg` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if msg.contains_key(k): val v = msg[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl:678` | `msg` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if msg.contains_key(k): val v = msg[k]` |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl:683` | `msg` | `JsonValue` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if msg.contains_key(k): val v = msg[k]` |
| `src/compiler_rust/lib/std/src/verification/models/async_effects.spl:627` | `function_effects` | `Effects` (HIGH) | CRITICAL | method/field chained on get() result | `if function_effects.contains_key(k): val v = function_effects[k]` |
| `src/compiler_rust/lib/std/src/verification/models/memory_model_drf.spl:589` | `threads` | `ThreadState` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if threads.contains_key(k): val v = threads[k]` |
| `src/compiler_rust/lib/std/src/verification/models/memory_model_drf.spl:629` | `threads` | `ThreadState` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if threads.contains_key(k): val v = threads[k]` |
| `src/compiler_rust/lib/std/src/verification/models/type_inference.spl:406` | `bindings` | `TypeScheme` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if bindings.contains_key(k): val v = bindings[k]` |
| `src/compiler_rust/lib/std/src/vscode/terminal.spl:193` | `active_terminals` | `Terminal` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if active_terminals.contains_key(k): val v = active_terminals[k]` |
| `src/lib/gc_async_mut/engine/render/gpu_texture_cache.spl:26` | `entries` | `GpuTexture` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/gc_async_mut/engine/render/gpu_texture_cache.spl:44` | `entries` | `GpuTexture` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/gc_async_mut/lsp/handlers/definition.spl:36` | `symbols` | `SymbolDefinition` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/lib/nogc_async_mut/async_host/scheduler.spl:245` | `tasks` | `HostTask` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/async_host/scheduler.spl:309` | `tasks` | `HostTask` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/async_host/scheduler.spl:344` | `tasks` | `HostTask` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/async/runtime.spl:121` | `tasks` | `TaskContext` (HIGH) | CRITICAL | field/method on bound Option at line 124 | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/async/runtime.spl:153` | `completed` | `TaskResult` (HIGH) | CRITICAL | field/method on bound Option at line 156 | `if completed.contains_key(k): val v = completed[k]` |
| `src/lib/nogc_async_mut/dap/dap_handlers.spl:326` | `global_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if global_variables.contains_key(k): val v = global_variables[k]` |
| `src/lib/nogc_async_mut/dap/dap_handlers.spl:333` | `local_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if local_variables.contains_key(k): val v = local_variables[k]` |
| `src/lib/nogc_async_mut/dap/server.spl:289` | `local_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if local_variables.contains_key(k): val v = local_variables[k]` |
| `src/lib/nogc_async_mut/dap/server.spl:294` | `global_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if global_variables.contains_key(k): val v = global_variables[k]` |
| `src/lib/nogc_async_mut/database/db_registry.spl:58` | `sdn_databases` | `SdnDatabase` (HIGH) | CRITICAL | field/method on bound Option at line 60 | `if sdn_databases.contains_key(k): val v = sdn_databases[k]` |
| `src/lib/nogc_async_mut/database/db_registry.spl:63` | `vector_databases` | `VectorDatabase` (HIGH) | CRITICAL | field/method on bound Option at line 65 | `if vector_databases.contains_key(k): val v = vector_databases[k]` |
| `src/lib/nogc_async_mut/database/db_registry.spl:72` | `sdn_databases` | `SdnDatabase` (HIGH) | CRITICAL | field/method on bound Option at line 74 | `if sdn_databases.contains_key(k): val v = sdn_databases[k]` |
| `src/lib/nogc_async_mut/database/db_registry.spl:76` | `vector_databases` | `VectorDatabase` (HIGH) | CRITICAL | field/method on bound Option at line 78 | `if vector_databases.contains_key(k): val v = vector_databases[k]` |
| `src/lib/nogc_async_mut/debug/remote/breakpoint_manager.spl:156` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 158 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_async_mut/debug/remote/breakpoint_manager.spl:165` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 167 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_async_mut/debug/remote/breakpoint_manager.spl:238` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 240 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_async_mut/debug/remote/breakpoint_manager.spl:250` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 252 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_async_mut/failsafe/circuit.spl:212` | `breakers` | `CircuitBreaker` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if breakers.contains_key(k): val v = breakers[k]` |
| `src/lib/nogc_async_mut/failsafe/circuit.spl:221` | `breakers` | `CircuitBreaker` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if breakers.contains_key(k): val v = breakers[k]` |
| `src/lib/nogc_async_mut/failsafe/core.spl:220` | `counters` | `Counter` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if counters.contains_key(k): val v = counters[k]` |
| `src/lib/nogc_async_mut/failsafe/core.spl:228` | `gauges` | `Gauge` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if gauges.contains_key(k): val v = gauges[k]` |
| `src/lib/nogc_async_mut/http_server/h2_connection.spl:659` | `streams` | `H2Stream` (HIGH) | CRITICAL | field/method on bound Option at line 661 | `if streams.contains_key(k): val v = streams[k]` |
| `src/lib/nogc_async_mut/http_server/h2_connection.spl:775` | `streams` | `H2Stream` (HIGH) | CRITICAL | field/method on bound Option at line 777 | `if streams.contains_key(k): val v = streams[k]` |
| `src/lib/nogc_async_mut/lsp/handlers/definition.spl:36` | `symbols` | `SymbolDefinition` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/lib/nogc_async_mut/mcp/editor.spl:157` | `documents` | `ManagedDocument` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if documents.contains_key(k): val v = documents[k]` |
| `src/lib/nogc_async_mut/mcp/editor.spl:84` | `documents` | `ManagedDocument` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if documents.contains_key(k): val v = documents[k]` |
| `src/lib/nogc_async_mut/mcp/session.spl:188` | `sessions` | `DebugSession` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if sessions.contains_key(k): val v = sessions[k]` |
| `src/lib/nogc_async_mut/mcp/session.spl:197` | `sessions` | `DebugSession` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if sessions.contains_key(k): val v = sessions[k]` |
| `src/lib/nogc_async_mut/mcp/session.spl:209` | `sessions` | `DebugSession` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if sessions.contains_key(k): val v = sessions[k]` |
| `src/lib/nogc_async_mut/mcp/session.spl:219` | `sessions` | `DebugSession` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if sessions.contains_key(k): val v = sessions[k]` |
| `src/lib/nogc_async_mut/mcp/tasks.spl:103` | `tasks` | `TaskInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/mcp/tasks.spl:112` | `tasks` | `TaskInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/mcp/tasks.spl:120` | `tasks` | `TaskInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/mcp/tasks.spl:130` | `tasks` | `TaskInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/mcp/tasks.spl:139` | `tasks` | `TaskInfo` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/process_set/manager.spl:103` | `workers` | `WorkerProcess` (HIGH) | CRITICAL | field/method on bound Option at line 108 | `if workers.contains_key(k): val v = workers[k]` |
| `src/lib/nogc_async_mut/process_set/manager.spl:97` | `workers` | `WorkerProcess` (HIGH) | CRITICAL | field/method on bound Option at line 98 | `if workers.contains_key(k): val v = workers[k]` |
| `src/lib/nogc_sync_mut/dap/dap_handlers.spl:326` | `global_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if global_variables.contains_key(k): val v = global_variables[k]` |
| `src/lib/nogc_sync_mut/dap/dap_handlers.spl:333` | `local_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if local_variables.contains_key(k): val v = local_variables[k]` |
| `src/lib/nogc_sync_mut/dap/server.spl:289` | `local_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if local_variables.contains_key(k): val v = local_variables[k]` |
| `src/lib/nogc_sync_mut/dap/server.spl:294` | `global_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if global_variables.contains_key(k): val v = global_variables[k]` |
| `src/lib/nogc_sync_mut/database/db_registry.spl:58` | `sdn_databases` | `SdnDatabase` (HIGH) | CRITICAL | field/method on bound Option at line 60 | `if sdn_databases.contains_key(k): val v = sdn_databases[k]` |
| `src/lib/nogc_sync_mut/database/db_registry.spl:63` | `vector_databases` | `VectorDatabase` (HIGH) | CRITICAL | field/method on bound Option at line 65 | `if vector_databases.contains_key(k): val v = vector_databases[k]` |
| `src/lib/nogc_sync_mut/database/db_registry.spl:72` | `sdn_databases` | `SdnDatabase` (HIGH) | CRITICAL | field/method on bound Option at line 74 | `if sdn_databases.contains_key(k): val v = sdn_databases[k]` |
| `src/lib/nogc_sync_mut/database/db_registry.spl:76` | `vector_databases` | `VectorDatabase` (HIGH) | CRITICAL | field/method on bound Option at line 78 | `if vector_databases.contains_key(k): val v = vector_databases[k]` |
| `src/lib/nogc_sync_mut/database/sql/stmt_cache.spl:120` | `entries` | `PreparedStatement` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/database/sql/stmt_cache.spl:40` | `entries` | `PreparedStatement` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/database/sql/stmt_cache.spl:65` | `entries` | `PreparedStatement` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/database/sql/stmt_cache.spl:77` | `entries` | `PreparedStatement` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/db/dbfs_engine/inline_data.spl:38` | `entries` | `InlineEntry` (HIGH) | CRITICAL | field/method on bound Option at line 51 | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/db/dbfs_engine/inline_data.spl:49` | `entries` | `InlineEntry` (HIGH) | CRITICAL | field/method on bound Option at line 51 | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/debug/remote/breakpoint_manager.spl:156` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 158 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_sync_mut/debug/remote/breakpoint_manager.spl:165` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 167 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_sync_mut/debug/remote/breakpoint_manager.spl:238` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 240 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_sync_mut/debug/remote/breakpoint_manager.spl:250` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 252 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_sync_mut/diag.spl:246` | `_g_deadline_budget` | `Deadline` (HIGH) | CRITICAL | field/method on bound Option at line 248 | `if _g_deadline_budget.contains_key(k): val v = _g_deadline_budget[k]` |
| `src/lib/nogc_sync_mut/diag.spl:263` | `_g_deadline_budget` | `Deadline` (HIGH) | CRITICAL | field/method on bound Option at line 265 | `if _g_deadline_budget.contains_key(k): val v = _g_deadline_budget[k]` |
| `src/lib/nogc_sync_mut/diag.spl:345` | `_g_timer_stats` | `_TimerStat` (HIGH) | CRITICAL | field/method on bound Option at line 356 | `if _g_timer_stats.contains_key(k): val v = _g_timer_stats[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:105` | `groups` | `AudioGroup` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:116` | `groups` | `AudioGroup` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:127` | `groups` | `AudioGroup` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:131` | `groups` | `AudioGroup` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:141` | `groups` | `AudioGroup` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:146` | `groups` | `AudioGroup` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:79` | `groups` | `AudioGroup` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:83` | `groups` | `AudioGroup` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl:185` | `buses` | `AudioBus` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if buses.contains_key(k): val v = buses[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl:206` | `buses` | `AudioBus` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if buses.contains_key(k): val v = buses[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl:211` | `buses` | `AudioBus` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if buses.contains_key(k): val v = buses[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl:222` | `buses` | `AudioBus` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if buses.contains_key(k): val v = buses[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl:261` | `buses` | `AudioBus` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if buses.contains_key(k): val v = buses[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl:76` | `clip_cache` | `AudioClip` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if clip_cache.contains_key(k): val v = clip_cache[k]` |
| `src/lib/nogc_sync_mut/engine/render/gpu_texture_cache.spl:27` | `entries` | `GpuTexture` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/engine/render/gpu_texture_cache.spl:45` | `entries` | `GpuTexture` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/engine/resource/manager.spl:116` | `audio_clips` | `AudioClip` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if audio_clips.contains_key(k): val v = audio_clips[k]` |
| `src/lib/nogc_sync_mut/engine/sprite/sprite.spl:193` | `clips` | `AnimationClip` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if clips.contains_key(k): val v = clips[k]` |
| `src/lib/nogc_sync_mut/engine/sprite/sprite.spl:217` | `clips` | `AnimationClip` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if clips.contains_key(k): val v = clips[k]` |
| `src/lib/nogc_sync_mut/failsafe/circuit.spl:212` | `breakers` | `CircuitBreaker` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if breakers.contains_key(k): val v = breakers[k]` |
| `src/lib/nogc_sync_mut/failsafe/circuit.spl:221` | `breakers` | `CircuitBreaker` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if breakers.contains_key(k): val v = breakers[k]` |
| `src/lib/nogc_sync_mut/failsafe/core.spl:220` | `counters` | `Counter` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if counters.contains_key(k): val v = counters[k]` |
| `src/lib/nogc_sync_mut/failsafe/core.spl:228` | `gauges` | `Gauge` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if gauges.contains_key(k): val v = gauges[k]` |
| `src/lib/nogc_sync_mut/lsp/handlers/definition.spl:36` | `symbols` | `SymbolDefinition` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/os/compositor/host_compositor_core.spl:702` | `content_caches` | `WebRenderPixelArtifactCache` (HIGH) | CRITICAL | field/method on bound Option at line 703 | `if content_caches.contains_key(k): val v = content_caches[k]` |
| `src/os/compositor/host_compositor_core.spl:880` | `content_caches` | `WebRenderPixelArtifactCache` (HIGH) | CRITICAL | field/method on bound Option at line 882 | `if content_caches.contains_key(k): val v = content_caches[k]` |
| `src/app/dap/dap_handlers.spl:326` | `global_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if global_variables.contains_key(k): val v = global_variables[k]` |
| `src/app/dap/dap_handlers.spl:333` | `local_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if local_variables.contains_key(k): val v = local_variables[k]` |
| `src/app/dap/server.spl:289` | `local_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if local_variables.contains_key(k): val v = local_variables[k]` |
| `src/app/dap/server.spl:294` | `global_variables` | `VariableInfo` (MED) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if global_variables.contains_key(k): val v = global_variables[k]` |
| `src/app/debug/remote/breakpoint_manager.spl:156` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 158 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/app/debug/remote/breakpoint_manager.spl:165` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 167 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/app/debug/remote/breakpoint_manager.spl:238` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 240 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/app/debug/remote/breakpoint_manager.spl:250` | `breakpoints` | `BreakpointInfo` (HIGH) | CRITICAL | field/method on bound Option at line 252 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:506` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 508 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:527` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 529 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:539` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 541 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:554` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 558 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:602` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 604 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:611` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 613 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:619` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 621 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:628` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 632 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:644` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 648 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:659` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 663 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:660` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 664 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:669` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 673 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:670` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 677 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:681` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 685 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:682` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 686 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:691` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 695 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:692` | `actors` | `ActorContext` (HIGH) | CRITICAL | unwrap of bound Option at line 699 | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/core/contract.spl:182` | `captures` | `Value` (HIGH) | CRITICAL | unwrap of bound Option at line 185 | `if captures.contains_key(k): val v = captures[k]` |
| `src/app/interpreter/core/environment.spl:102` | `bindings` | `Binding` (HIGH) | CRITICAL | unwrap of bound Option at line 104 | `if bindings.contains_key(k): val v = bindings[k]` |
| `src/app/interpreter/extern/i18n.spl:121` | `_catalogs` | `MessageCatalog` (HIGH) | CRITICAL | unwrap of bound Option at line 123 | `if _catalogs.contains_key(k): val v = _catalogs[k]` |
| `src/app/interpreter/extern/i18n.spl:48` | `_contexts` | `MessageContext` (HIGH) | CRITICAL | field/method on bound Option at line 50 | `if _contexts.contains_key(k): val v = _contexts[k]` |
| `src/app/interpreter/helpers/debug_spec.spl:1559` | `values` | `Value` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if values.contains_key(k): val v = values[k]` |
| `src/app/interpreter/helpers/debug.spl:128` | `breakpoints` | `Breakpoint` (HIGH) | CRITICAL | Option destructure binds corrupt payload | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/app/interpreter/helpers/macros.spl:191` | `bindings` | `MacroBinding` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if bindings.contains_key(k): val v = bindings[k]` |
| `src/app/interpreter/helpers/macros.spl:211` | `bindings` | `MacroBinding` (HIGH) | CRITICAL | match on get() Option; Some(v) binds corrupt payload | `if bindings.contains_key(k): val v = bindings[k]` |
| `src/app/interpreter/memory/refc_binary.spl:440` | `binaries` | `RefcBinary` (HIGH) | CRITICAL | unwrap of bound Option at line 444 | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/app/interpreter/memory/refc_binary.spl:475` | `binaries` | `RefcBinary` (HIGH) | CRITICAL | unwrap of bound Option at line 477 | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/app/interpreter/memory/refc_binary.spl:485` | `binaries` | `RefcBinary` (HIGH) | CRITICAL | unwrap of bound Option at line 487 | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/app/interpreter/memory/refc_binary.spl:498` | `binaries` | `RefcBinary` (HIGH) | CRITICAL | unwrap of bound Option at line 502 | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/app/interpreter/memory/refc_binary.spl:577` | `binaries` | `RefcBinary` (HIGH) | CRITICAL | unwrap of bound Option at line 579 | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/app/interpreter/memory/refc_binary.spl:588` | `binaries` | `RefcBinary` (HIGH) | CRITICAL | unwrap of bound Option at line 590 | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/app/interpreter/memory/refc_binary.spl:602` | `binaries` | `RefcBinary` (HIGH) | CRITICAL | unwrap of bound Option at line 604 | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/compiler/15.blocks/blocks/unified_registry.spl:110` | `prefixes` | `PrefixKind` (HIGH) | HIGH | result flows onward (arg/expr) | `if prefixes.contains_key(k): val v = prefixes[k]` |
| `src/compiler/40.mono/monomorphize/metadata.spl:265` | `bindings` | `ConcreteType` (HIGH) | HIGH | result flows onward (arg/expr) | `if bindings.contains_key(k): val v = bindings[k]` |
| `src/compiler/40.mono/monomorphize/table.spl:231` | `specialized_functions` | `FunctionDef` (HIGH) | HIGH | result flows onward (arg/expr) | `if specialized_functions.contains_key(k): val v = specialized_functions[k]` |
| `src/compiler/55.borrow/borrow_check/borrow_graph.spl:280` | `borrows` | `Borrow` (HIGH) | HIGH | get() result returned to caller | `if borrows.contains_key(k): val v = borrows[k]` |
| `src/compiler/70.backend/backend/vhdl_validation.spl:458` | `blocks` | `MirBlock` (HIGH) | HIGH | passed to callee at line 460 | `if blocks.contains_key(k): val v = blocks[k]` |
| `src/compiler/80.driver/driver_build/incremental.spl:458` | `entries` | `DependencyEntry` (HIGH) | HIGH | result flows onward (arg/expr) | `if entries.contains_key(k): val v = entries[k]` |
| `src/compiler/80.driver/driver_build/incremental.spl:477` | `entries` | `DependencyEntry` (HIGH) | HIGH | result flows onward (arg/expr) | `if entries.contains_key(k): val v = entries[k]` |
| `src/compiler/80.driver/driver_build/incremental.spl:490` | `entries` | `DependencyEntry` (HIGH) | HIGH | result flows onward (arg/expr) | `if entries.contains_key(k): val v = entries[k]` |
| `src/compiler_rust/lib/std/src/core/json_serialize.spl:169` | `obj` | `JsonValue` (HIGH) | HIGH | get() result returned to caller | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/core/json_serialize.spl:51` | `obj` | `JsonValue` (HIGH) | HIGH | passed to callee at line 52 | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/core/json_serialize.spl:92` | `obj` | `JsonValue` (HIGH) | HIGH | passed to callee at line 93 | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/lms/workspace.spl:171` | `files` | `FileMetadata` (HIGH) | HIGH | result flows onward (arg/expr) | `if files.contains_key(k): val v = files[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/provider.spl:33` | `resources` | `Resource` (HIGH) | HIGH | get() result returned to caller | `if resources.contains_key(k): val v = resources[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/provider.spl:86` | `resources` | `Resource` (HIGH) | HIGH | result flows onward (arg/expr) | `if resources.contains_key(k): val v = resources[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/server.spl:264` | `tools` | `ToolHandler` (HIGH) | HIGH | result flows onward (arg/expr) | `if tools.contains_key(k): val v = tools[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/server.spl:299` | `tools` | `ToolHandler` (HIGH) | HIGH | result flows onward (arg/expr) | `if tools.contains_key(k): val v = tools[k]` |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:550` | `obj` | `JsonValue` (HIGH) | HIGH | result flows onward (arg/expr) | `if obj.contains_key(k): val v = obj[k]` |
| `src/compiler_rust/lib/std/src/mcp/examples/template_provider.spl:147` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:348` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:349` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:350` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:366` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:367` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:368` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:369` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:384` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:385` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:386` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:401` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:416` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/lsp/mod.spl:417` | `args` | `Any` (HIGH) | HIGH | result flows onward (arg/expr) | `if args.contains_key(k): val v = args[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/coverage.spl:210` | `symbol_coverage` | `SymbolCoverage` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbol_coverage.contains_key(k): val v = symbol_coverage[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/coverage.spl:317` | `symbol_coverage` | `SymbolCoverage` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbol_coverage.contains_key(k): val v = symbol_coverage[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/coverage.spl:334` | `symbol_coverage` | `SymbolCoverage` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbol_coverage.contains_key(k): val v = symbol_coverage[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:350` | `symbols` | `QualifiedSymbol` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:359` | `symbols` | `QualifiedSymbol` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:397` | `symbols` | `QualifiedSymbol` (HIGH) | HIGH | get() result returned to caller | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:407` | `symbols` | `QualifiedSymbol` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/compiler_rust/lib/std/src/sdn/query.spl:55` | `fields` | `SdnValue` (HIGH) | HIGH | result flows onward (arg/expr) | `if fields.contains_key(k): val v = fields[k]` |
| `src/compiler_rust/lib/std/src/spec/arch.spl:240` | `layers` | `Layer` (HIGH) | HIGH | get() result returned to caller | `if layers.contains_key(k): val v = layers[k]` |
| `src/compiler_rust/lib/std/src/spec/mock.spl:41` | `_mock_stub_returns` | `Any` (HIGH) | HIGH | get() result returned to caller | `if _mock_stub_returns.contains_key(k): val v = _mock_stub_returns[k]` |
| `src/compiler_rust/lib/std/src/spec/mock.spl:606` | `_stub_returns_with_args` | `Any` (HIGH) | HIGH | get() result returned to caller | `if _stub_returns_with_args.contains_key(k): val v = _stub_returns_with_args[k]` |
| `src/compiler_rust/lib/std/src/spec/mock.spl:618` | `_stub_returns` | `Any` (HIGH) | HIGH | get() result returned to caller | `if _stub_returns.contains_key(k): val v = _stub_returns[k]` |
| `src/compiler_rust/lib/std/src/spec/mock.spl:693` | `values` | `Any` (HIGH) | HIGH | get() result returned to caller | `if values.contains_key(k): val v = values[k]` |
| `src/compiler_rust/lib/std/src/spec/runtime.spl:118` | `config` | `Any` (HIGH) | HIGH | get() result returned to caller | `if config.contains_key(k): val v = config[k]` |
| `src/compiler_rust/lib/std/src/spec/runtime.spl:24` | `state` | `Any` (HIGH) | HIGH | get() result returned to caller | `if state.contains_key(k): val v = state[k]` |
| `src/compiler_rust/lib/std/src/tooling/compiler/compiler_interface_impl.spl:64` | `compilers` | `LanguageCompiler` (HIGH) | HIGH | result flows onward (arg/expr) | `if compilers.contains_key(k): val v = compilers[k]` |
| `src/compiler_rust/lib/std/src/verification/models/contracts.spl:587` | `captured_values` | `ContractExpr` (HIGH) | HIGH | result flows onward (arg/expr) | `if captured_values.contains_key(k): val v = captured_values[k]` |
| `src/compiler_rust/lib/std/src/verification/models/tensor_constraint.spl:224` | `bindings` | `Dim` (HIGH) | HIGH | result flows onward (arg/expr) | `if bindings.contains_key(k): val v = bindings[k]` |
| `src/compiler_rust/lib/std/src/verification/models/tensor_constraint.spl:227` | `named_dims` | `Dim` (HIGH) | HIGH | result flows onward (arg/expr) | `if named_dims.contains_key(k): val v = named_dims[k]` |
| `src/compiler_rust/lib/std/src/verification/models/type_inference.spl:427` | `mappings` | `Type` (HIGH) | HIGH | result flows onward (arg/expr) | `if mappings.contains_key(k): val v = mappings[k]` |
| `src/compiler_rust/lib/std/src/vscode/dap.spl:456` | `sessions` | `DebugSession` (HIGH) | HIGH | result flows onward (arg/expr) | `if sessions.contains_key(k): val v = sessions[k]` |
| `src/compiler_rust/lib/std/src/vscode/wasm_lsp.spl:208` | `documents` | `TextDocument` (HIGH) | HIGH | result flows onward (arg/expr) | `if documents.contains_key(k): val v = documents[k]` |
| `src/lib/gc_async_mut/lsp/handlers/verification.spl:150` | `symbols` | `VerifiedSymbol` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/lib/gc_async_mut/security/auth/context_propagation.spl:35` | `contexts` | `SecurityContext` (HIGH) | HIGH | result flows onward (arg/expr) | `if contexts.contains_key(k): val v = contexts[k]` |
| `src/lib/nogc_async_mut/database/db_registry.spl:46` | `sdn_databases` | `SdnDatabase` (HIGH) | HIGH | result flows onward (arg/expr) | `if sdn_databases.contains_key(k): val v = sdn_databases[k]` |
| `src/lib/nogc_async_mut/database/db_registry.spl:49` | `vector_databases` | `VectorDatabase` (HIGH) | HIGH | result flows onward (arg/expr) | `if vector_databases.contains_key(k): val v = vector_databases[k]` |
| `src/lib/nogc_async_mut/debug/remote/breakpoint_manager.spl:258` | `breakpoints` | `BreakpointInfo` (HIGH) | HIGH | result flows onward (arg/expr) | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_async_mut/lsp/handlers/verification.spl:150` | `symbols` | `VerifiedSymbol` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/lib/nogc_async_mut/mcp/session.spl:177` | `sessions` | `DebugSession` (HIGH) | HIGH | result flows onward (arg/expr) | `if sessions.contains_key(k): val v = sessions[k]` |
| `src/lib/nogc_async_mut/mcp/tasks.spl:99` | `tasks` | `TaskInfo` (HIGH) | HIGH | result flows onward (arg/expr) | `if tasks.contains_key(k): val v = tasks[k]` |
| `src/lib/nogc_async_mut/process_set/manager.spl:132` | `workers` | `WorkerProcess` (HIGH) | HIGH | result flows onward (arg/expr) | `if workers.contains_key(k): val v = workers[k]` |
| `src/lib/nogc_async_mut/security/auth/context_propagation.spl:35` | `contexts` | `SecurityContext` (HIGH) | HIGH | result flows onward (arg/expr) | `if contexts.contains_key(k): val v = contexts[k]` |
| `src/lib/nogc_async_mut/security/auth/context_propagation.spl:74` | `contexts` | `SecurityContext` (HIGH) | HIGH | result flows onward (arg/expr) | `if contexts.contains_key(k): val v = contexts[k]` |
| `src/lib/nogc_sync_mut/database/db_registry.spl:46` | `sdn_databases` | `SdnDatabase` (HIGH) | HIGH | result flows onward (arg/expr) | `if sdn_databases.contains_key(k): val v = sdn_databases[k]` |
| `src/lib/nogc_sync_mut/database/db_registry.spl:49` | `vector_databases` | `VectorDatabase` (HIGH) | HIGH | result flows onward (arg/expr) | `if vector_databases.contains_key(k): val v = vector_databases[k]` |
| `src/lib/nogc_sync_mut/db/dbfs_engine/file_meta.spl:96` | `entries` | `HintEntry` (HIGH) | HIGH | get() result returned to caller | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/db/dbfs_engine/inline_data.spl:29` | `entries` | `InlineEntry` (HIGH) | HIGH | result flows onward (arg/expr) | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/debug/remote/breakpoint_manager.spl:258` | `breakpoints` | `BreakpointInfo` (HIGH) | HIGH | result flows onward (arg/expr) | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_sync_mut/engine/audio/audio_group.spl:157` | `groups` | `AudioGroup` (HIGH) | HIGH | result flows onward (arg/expr) | `if groups.contains_key(k): val v = groups[k]` |
| `src/lib/nogc_sync_mut/lsp/handlers/verification.spl:150` | `symbols` | `VerifiedSymbol` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/lib/nogc_sync_mut/security/auth/context_propagation.spl:35` | `contexts` | `SecurityContext` (HIGH) | HIGH | result flows onward (arg/expr) | `if contexts.contains_key(k): val v = contexts[k]` |
| `src/lib/nogc_sync_mut/security/auth/context_propagation.spl:76` | `contexts` | `SecurityContext` (HIGH) | HIGH | result flows onward (arg/expr) | `if contexts.contains_key(k): val v = contexts[k]` |
| `src/lib/nogc_sync_mut/security/types.spl:366` | `sessions` | `RemoteSecuritySession` (HIGH) | HIGH | result flows onward (arg/expr) | `if sessions.contains_key(k): val v = sessions[k]` |
| `src/lib/nogc_sync_mut/testing/attributes.spl:132` | `test_metadata` | `TestMeta` (HIGH) | HIGH | result flows onward (arg/expr) | `if test_metadata.contains_key(k): val v = test_metadata[k]` |
| `src/app/debug/remote/breakpoint_manager.spl:258` | `breakpoints` | `BreakpointInfo` (HIGH) | HIGH | result flows onward (arg/expr) | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/app/interpreter/async_runtime/actor_scheduler.spl:715` | `actors` | `ActorContext` (HIGH) | HIGH | result flows onward (arg/expr) | `if actors.contains_key(k): val v = actors[k]` |
| `src/app/interpreter/core/contract.spl:44` | `captures` | `Value` (HIGH) | HIGH | result flows onward (arg/expr) | `if captures.contains_key(k): val v = captures[k]` |
| `src/app/interpreter/core/environment.spl:81` | `bindings` | `Binding` (HIGH) | HIGH | returned at line 83 | `if bindings.contains_key(k): val v = bindings[k]` |
| `src/app/interpreter/ffi/bridge.spl:26` | `functions` | `NativeFunction` (HIGH) | HIGH | get() result returned to caller | `if functions.contains_key(k): val v = functions[k]` |
| `src/app/interpreter/ffi/extern.spl:33` | `symbols` | `Symbol` (HIGH) | HIGH | result flows onward (arg/expr) | `if symbols.contains_key(k): val v = symbols[k]` |
| `src/app/interpreter/helpers/imports.spl:26` | `exports` | `Value` (HIGH) | HIGH | get() result returned to caller | `if exports.contains_key(k): val v = exports[k]` |
| `src/app/interpreter/helpers/imports.spl:49` | `modules` | `Module` (HIGH) | HIGH | get() result returned to caller | `if modules.contains_key(k): val v = modules[k]` |
| `src/app/interpreter/helpers/macros.spl:62` | `macros` | `Macro` (HIGH) | HIGH | get() result returned to caller | `if macros.contains_key(k): val v = macros[k]` |
| `src/app/interpreter/memory/refc_binary.spl:599` | `binaries` | `RefcBinary` (HIGH) | HIGH | result flows onward (arg/expr) | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/compiler/00.common/effects.spl:126` | `effects` | `EffectTag` (HIGH) | MEDIUM | nil-compare at line 127 | `if effects.contains_key(k): val v = effects[k]` |
| `src/compiler/00.common/effects.spl:131` | `builtins` | `EffectTag` (HIGH) | MEDIUM | nil-compare at line 132 | `if builtins.contains_key(k): val v = builtins[k]` |
| `src/compiler/20.hir/hir_lowering/module_surface.spl:260` | `modules` | `Module` (HIGH) | MEDIUM | nil-compare at line 261 | `if modules.contains_key(k): val v = modules[k]` |
| `src/compiler/30.types/type_system/builtin_registry.spl:79` | `entries` | `BuiltinEntry` (HIGH) | MEDIUM | nil-compare at line 80 | `if entries.contains_key(k): val v = entries[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:306` | `specialization_cache` | `CompiledCode` (HIGH) | MEDIUM | nil-compare at line 307 | `if specialization_cache.contains_key(k): val v = specialization_cache[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:368` | `specialization_cache` | `CompiledCode` (HIGH) | MEDIUM | nil-compare at line 369 | `if specialization_cache.contains_key(k): val v = specialization_cache[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:430` | `specialization_cache` | `CompiledCode` (HIGH) | MEDIUM | nil-compare at line 431 | `if specialization_cache.contains_key(k): val v = specialization_cache[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:492` | `specialization_cache` | `CompiledCode` (HIGH) | MEDIUM | nil-compare at line 493 | `if specialization_cache.contains_key(k): val v = specialization_cache[k]` |
| `src/compiler/40.mono/monomorphize/deferred.spl:572` | `template_cache` | `GenericTemplate` (HIGH) | MEDIUM | nil-compare at line 573 | `if template_cache.contains_key(k): val v = template_cache[k]` |
| `src/compiler/55.borrow/borrow_check/borrow_graph.spl:409` | `point_borrows` | `BorrowSet` (HIGH) | MEDIUM | nil-compare at line 410 | `if point_borrows.contains_key(k): val v = point_borrows[k]` |
| `src/compiler/70.backend/backend/vhdl_codegen_helpers.spl:187` | `active_function_by_name` | `MirFunction` (MED) | MEDIUM | nil-compare at line 188 | `if active_function_by_name.contains_key(k): val v = active_function_by_name[k]` |
| `src/compiler/70.backend/backend/vhdl_validation.spl:521` | `active_function_by_name` | `MirFunction` (MED) | MEDIUM | bound to known; no direct deref found in next 14 lines | `if active_function_by_name.contains_key(k): val v = active_function_by_name[k]` |
| `src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:278` | `active_function_by_name` | `MirFunction` (MED) | MEDIUM | bound to known; no direct deref found in next 14 lines | `if active_function_by_name.contains_key(k): val v = active_function_by_name[k]` |
| `src/compiler_rust/lib/std/src/verification/cache.spl:142` | `entries` | `CacheEntry` (HIGH) | MEDIUM | nil-compare only | `if entries.contains_key(k): val v = entries[k]` |
| `src/compiler_rust/lib/std/src/verification/cache.spl:189` | `entries` | `CacheEntry` (HIGH) | MEDIUM | nil-compare only | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_async_mut/actors/actor.spl:412` | `actors` | `ActorContext` (HIGH) | MEDIUM | nil-compare at line 413 | `if actors.contains_key(k): val v = actors[k]` |
| `src/lib/nogc_async_mut/actors/actor.spl:482` | `actors` | `ActorContext` (HIGH) | MEDIUM | nil-compare at line 483 | `if actors.contains_key(k): val v = actors[k]` |
| `src/lib/nogc_async_mut/actors/actor.spl:509` | `actors` | `ActorContext` (HIGH) | MEDIUM | nil-compare at line 510 | `if actors.contains_key(k): val v = actors[k]` |
| `src/lib/nogc_async_mut/actors/actor.spl:542` | `actors` | `ActorContext` (HIGH) | MEDIUM | nil-compare at line 543 | `if actors.contains_key(k): val v = actors[k]` |
| `src/lib/nogc_async_mut/debug/remote/breakpoint_manager.spl:196` | `breakpoints` | `BreakpointInfo` (HIGH) | MEDIUM | nil-compare at line 197 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_async_mut/failsafe/ratelimit.spl:98` | `client_requests` | `Count` (HIGH) | MEDIUM | bound to current; no direct deref found in next 14 lines | `if client_requests.contains_key(k): val v = client_requests[k]` |
| `src/lib/nogc_async_mut/http_server/h2_connection.spl:533` | `streams` | `H2Stream` (HIGH) | MEDIUM | bound to cstream; no direct deref found in next 14 lines | `if streams.contains_key(k): val v = streams[k]` |
| `src/lib/nogc_async_mut/http_server/h2_connection.spl:626` | `streams` | `H2Stream` (HIGH) | MEDIUM | bound to stream; no direct deref found in next 14 lines | `if streams.contains_key(k): val v = streams[k]` |
| `src/lib/nogc_async_mut/http_server/h2_connection.spl:648` | `streams` | `H2Stream` (HIGH) | MEDIUM | bound to existing; no direct deref found in next 14 lines | `if streams.contains_key(k): val v = streams[k]` |
| `src/lib/nogc_async_mut/http_server/h2_connection.spl:737` | `streams` | `H2Stream` (HIGH) | MEDIUM | bound to done_stream; no direct deref found in next 14 lines | `if streams.contains_key(k): val v = streams[k]` |
| `src/lib/nogc_async_mut/http_server/h2_connection.spl:754` | `streams` | `H2Stream` (HIGH) | MEDIUM | bound to stream; no direct deref found in next 14 lines | `if streams.contains_key(k): val v = streams[k]` |
| `src/lib/nogc_async_mut/http_server/h2_connection.spl:786` | `streams` | `H2Stream` (HIGH) | MEDIUM | bound to stream; no direct deref found in next 14 lines | `if streams.contains_key(k): val v = streams[k]` |
| `src/lib/nogc_async_mut/http_server/response_cache.spl:32` | `entries` | `CacheEntry` (HIGH) | MEDIUM | bound to entry; no direct deref found in next 14 lines | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_async_mut/http_server/server.spl:72` | `_workers` | `Worker` (HIGH) | MEDIUM | bound to worker; no direct deref found in next 14 lines | `if _workers.contains_key(k): val v = _workers[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:369` | `h2_connections` | `H2Connection` (HIGH) | MEDIUM | nil-compare only | `if h2_connections.contains_key(k): val v = h2_connections[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:445` | `h2_connections` | `H2Connection` (HIGH) | MEDIUM | bound to h2conn; no direct deref found in next 14 lines | `if h2_connections.contains_key(k): val v = h2_connections[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:478` | `tls_sessions` | `TlsSessionState` (HIGH) | MEDIUM | bound to tls_session; no direct deref found in next 14 lines | `if tls_sessions.contains_key(k): val v = tls_sessions[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:522` | `connections` | `Connection` (HIGH) | MEDIUM | bound to conn_tls; no direct deref found in next 14 lines | `if connections.contains_key(k): val v = connections[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:549` | `connections` | `Connection` (HIGH) | MEDIUM | bound to conn; no direct deref found in next 14 lines | `if connections.contains_key(k): val v = connections[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:584` | `connections` | `Connection` (HIGH) | MEDIUM | bound to conn; no direct deref found in next 14 lines | `if connections.contains_key(k): val v = connections[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:629` | `connections` | `Connection` (HIGH) | MEDIUM | bound to conn; no direct deref found in next 14 lines | `if connections.contains_key(k): val v = connections[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:784` | `connections` | `Connection` (HIGH) | MEDIUM | bound to conn; no direct deref found in next 14 lines | `if connections.contains_key(k): val v = connections[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:791` | `tls_sessions` | `TlsSessionState` (HIGH) | MEDIUM | bound to tls_session_send; no direct deref found in next 14 lines | `if tls_sessions.contains_key(k): val v = tls_sessions[k]` |
| `src/lib/nogc_async_mut/http_server/worker.spl:933` | `h2_connections` | `H2Connection` (HIGH) | MEDIUM | bound to h2conn; no direct deref found in next 14 lines | `if h2_connections.contains_key(k): val v = h2_connections[k]` |
| `src/lib/nogc_async_mut/mcp/session.spl:128` | `subscriptions` | `Bool` (HIGH) | MEDIUM | nil-compare only | `if subscriptions.contains_key(k): val v = subscriptions[k]` |
| `src/lib/nogc_async_mut/process_set/manager.spl:137` | `workers` | `WorkerProcess` (HIGH) | MEDIUM | nil-compare at line 138 | `if workers.contains_key(k): val v = workers[k]` |
| `src/lib/nogc_async_mut/process_set/manager.spl:169` | `local_handlers` | `HandlerTable` (HIGH) | MEDIUM | nil-compare at line 170 | `if local_handlers.contains_key(k): val v = local_handlers[k]` |
| `src/lib/nogc_async_mut/process_set/manager.spl:181` | `local_handlers` | `HandlerTable` (HIGH) | MEDIUM | nil-compare at line 182 | `if local_handlers.contains_key(k): val v = local_handlers[k]` |
| `src/lib/nogc_async_mut/process_set/manager.spl:207` | `local_handlers` | `HandlerTable` (HIGH) | MEDIUM | nil-compare at line 208 | `if local_handlers.contains_key(k): val v = local_handlers[k]` |
| `src/lib/nogc_async_mut/process_set/manager.spl:219` | `local_handlers` | `HandlerTable` (HIGH) | MEDIUM | nil-compare at line 220 | `if local_handlers.contains_key(k): val v = local_handlers[k]` |
| `src/lib/nogc_sync_mut/db/dbfs_engine/file_meta.spl:117` | `entries` | `HintEntry` (HIGH) | MEDIUM | bound to entry; no direct deref found in next 14 lines | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/db/dbfs_engine/file_meta.spl:68` | `entries` | `HintEntry` (HIGH) | MEDIUM | bound to existing; no direct deref found in next 14 lines | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/db/dbfs_engine/file_meta.spl:83` | `entries` | `HintEntry` (HIGH) | MEDIUM | bound to entry; no direct deref found in next 14 lines | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/db/dbfs_engine/inline_data.spl:35` | `entries` | `InlineEntry` (HIGH) | MEDIUM | nil-compare only | `if entries.contains_key(k): val v = entries[k]` |
| `src/lib/nogc_sync_mut/debug/remote/breakpoint_manager.spl:196` | `breakpoints` | `BreakpointInfo` (HIGH) | MEDIUM | nil-compare at line 197 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/lib/nogc_sync_mut/diag.spl:313` | `_g_timer_stats` | `_TimerStat` (HIGH) | MEDIUM | nil-compare at line 314 | `if _g_timer_stats.contains_key(k): val v = _g_timer_stats[k]` |
| `src/lib/nogc_sync_mut/diag.spl:333` | `_g_timer_stats` | `_TimerStat` (HIGH) | MEDIUM | nil-compare at line 334 | `if _g_timer_stats.contains_key(k): val v = _g_timer_stats[k]` |
| `src/lib/nogc_sync_mut/failsafe/ratelimit.spl:98` | `client_requests` | `Count` (HIGH) | MEDIUM | bound to current; no direct deref found in next 14 lines | `if client_requests.contains_key(k): val v = client_requests[k]` |
| `src/lib/nogc_sync_mut/web_framework/rbac.spl:78` | `roles` | `Role` (HIGH) | MEDIUM | nil-compare at line 79 | `if roles.contains_key(k): val v = roles[k]` |
| `src/lib/nogc_sync_mut/web_framework/rbac.spl:98` | `roles` | `Role` (HIGH) | MEDIUM | nil-compare at line 99 | `if roles.contains_key(k): val v = roles[k]` |
| `src/os/compositor/layout_manager.spl:100` | `_layout_stage_positions` | `WindowLayout` (HIGH) | MEDIUM | nil-compare at line 101 | `if _layout_stage_positions.contains_key(k): val v = _layout_stage_positions[k]` |
| `src/app/debug/remote/breakpoint_manager.spl:196` | `breakpoints` | `BreakpointInfo` (HIGH) | MEDIUM | nil-compare at line 197 | `if breakpoints.contains_key(k): val v = breakpoints[k]` |
| `src/app/interpreter/memory/refc_binary.spl:610` | `binaries` | `RefcBinary` (HIGH) | MEDIUM | nil-compare only | `if binaries.contains_key(k): val v = binaries[k]` |
| `src/app/office/sheets/spreadsheet.spl:108` | `cells` | `Cell` (HIGH) | MEDIUM | nil-compare at line 109 | `if cells.contains_key(k): val v = cells[k]` |
| `src/app/office/sheets/spreadsheet.spl:43` | `cells` | `Cell` (HIGH) | MEDIUM | nil-compare at line 44 | `if cells.contains_key(k): val v = cells[k]` |

## 6. LOW-confidence sites (262) — manual triage required

The receiver name is also declared as a non-Dict type (List/array/struct) somewhere in the repo, so the resolution may be a false positive. Notably **all 31 hits in `src/lib/common/js/builtins/object.spl` are List indexing** (`properties: [JsProperty]`, `src/lib/common/js/types/js_types.spl:31`) and are **not** exposed.

| File | LOW-confidence hits |
|---|---|
| `src/lib/common/js/builtins/object.spl` | 31 |
| `src/app/office/word/table_ops.spl` | 29 |
| `src/lib/common/js/engine/gc.spl` | 14 |
| `src/lib/common/js/builtins/array.spl` | 14 |
| `src/lib/common/js/engine/jit.spl` | 10 |
| `src/compiler_rust/lib/std/src/tooling/compiler/rust.spl` | 10 |
| `src/lib/gc_async_mut/js/engine/interpreter_eval.spl` | 8 |
| `src/app/interpreter/call/dispatch.spl` | 8 |
| `src/lib/nogc_async_mut/js/engine/interpreter_eval.spl` | 7 |
| `src/lib/editor/services/md_document_decor.spl` | 6 |
| `src/app/md_lsp/md_lsp_workspace.spl` | 6 |
| `src/lib/nogc_sync_mut/dns/parse.spl` | 5 |
| `src/lib/nogc_async_mut/dns/parse.spl` | 5 |
| `src/compiler_rust/lib/std/src/vscode/workspace.spl` | 5 |
| `src/compiler_rust/lib/std/src/type_checker/type_inference.spl` | 5 |
| `src/compiler_rust/lib/std/src/tooling/testing/runner.spl` | 5 |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/coverage.spl` | 4 |
| `src/app/interpreter/helpers/debug_spec.spl` | 4 |
| `src/lib/nogc_sync_mut/dap/adapter/lldb_dap.spl` | 3 |
| `src/lib/nogc_async_mut/js/engine/interpreter_async.spl` | 3 |
| `src/lib/gc_async_mut/js/engine/interpreter_async.spl` | 3 |
| `src/compiler_rust/lib/std/src/vscode/tasks.spl` | 3 |
| `src/compiler_rust/lib/std/examples/ml/train_example.spl` | 3 |
| `src/compiler_rust/lib/std/examples/ml/config_example.spl` | 3 |
| `src/app/pkg/manifest.spl` | 3 |
| `src/app/office/sheets/merge.spl` | 3 |
| `src/lib/nogc_sync_mut/compositor/damage.spl` | 2 |
| `src/lib/nogc_async_mut/js/engine/interpreter_exec.spl` | 2 |
| `src/lib/nogc_async_mut/compositor/damage.spl` | 2 |
| `src/lib/gc_async_mut/js/engine/interpreter_exec.spl` | 2 |
| `src/lib/gc_async_mut/gpu/browser_engine/net/ws_handshake.spl` | 2 |
| `src/lib/gc_async_mut/compositor/damage.spl` | 2 |
| `src/lib/common/json/serializer.spl` | 2 |
| `src/lib/common/js/engine/runtime.spl` | 2 |
| `src/lib/common/js/engine/bytecode_compiler.spl` | 2 |
| `src/compiler_rust/lib/std/src/vscode/webview.spl` | 2 |
| `src/compiler_rust/lib/std/src/tooling/core/errors_reporting.spl` | 2 |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/provider.spl` | 2 |
| `src/app/release/github.spl` | 2 |
| `src/app/pkg/lock.spl` | 2 |
| `src/app/office/sheets/sync.spl` | 2 |
| `src/lib/nogc_sync_mut/dap/breakpoints.spl` | 1 |
| `src/lib/nogc_sync_mut/compositor/scroll.spl` | 1 |
| `src/lib/nogc_sync_mut/compositor/rasterizer.spl` | 1 |
| `src/lib/nogc_async_mut/js/engine/interpreter_string_methods.spl` | 1 |
| `src/lib/nogc_async_mut/js/engine/interpreter_eval_member.spl` | 1 |
| `src/lib/nogc_async_mut/http_server/config.spl` | 1 |
| `src/lib/nogc_async_mut/dns/resolver.spl` | 1 |
| `src/lib/nogc_async_mut/dap/breakpoints.spl` | 1 |
| `src/lib/nogc_async_mut/compositor/scroll.spl` | 1 |
| `src/lib/nogc_async_mut/compositor/rasterizer.spl` | 1 |
| `src/lib/gc_async_mut/js/engine/interpreter_string_methods.spl` | 1 |
| `src/lib/gc_async_mut/js/engine/interpreter_eval_member.spl` | 1 |
| `src/lib/gc_async_mut/gpu/browser_engine/net/ws_utils.spl` | 1 |
| `src/lib/gc_async_mut/compositor/scroll.spl` | 1 |
| `src/lib/gc_async_mut/compositor/rasterizer.spl` | 1 |
| `src/lib/common/wfc.spl` | 1 |
| `src/lib/common/js/engine/vm_object_store.spl` | 1 |
| `src/lib/common/js/builtins/promise.spl` | 1 |
| `src/lib/common/encoding/yaml.spl` | 1 |
| `src/lib/common/encoding/ini.spl` | 1 |
| `src/compiler_rust/lib/std/src/type_checker/type_inference_v4.spl` | 1 |
| `src/compiler_rust/lib/std/src/type_checker/type_inference_v3.spl` | 1 |
| `src/compiler_rust/lib/std/src/type_checker/type_inference_v2.spl` | 1 |
| `src/compiler_rust/lib/std/src/type_checker/type_inference_simple.spl` | 1 |
| `src/compiler_rust/lib/std/src/tooling/testing/aggregation.spl` | 1 |
| `src/compiler_rust/lib/std/src/tooling/compiler/symbol_analysis.spl` | 1 |
| `src/app/web_stack_sample/app.spl` | 1 |
| `src/app/office/word/toc.spl` | 1 |
| `src/app/model3d/main.spl` | 1 |
| `src/app/md_lsp/md_lsp_handler.spl` | 1 |
| `src/app/interpreter/ffi/extern.spl` | 1 |
| `src/app/dap/breakpoints.spl` | 1 |

## 7. LOW severity — scalar-valued `Dict.get()` (651 sites)

`V` is `text`/`i64`/`i32`/`bool`/`f64`/… . These do **not** crash; they return the still-boxed value (`7` → `56`). Silent wrong-number bugs, and equally worth converting to `contains_key` + `d[k]`.

By tier: `src/lib` 402, `src/compiler` 129, `src/compiler_rust` 74, `src/app` 46.

Top 25 files:

| File | scalar-`get` sites |
|---|---|
| `src/lib/nogc_sync_mut/database/test.spl` | 23 |
| `src/lib/nogc_async_mut/database/test.spl` | 23 |
| `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` | 22 |
| `src/lib/nogc_sync_mut/database/checker.spl` | 20 |
| `src/lib/gc_async_mut/pure/test/tensor_ops_spec.spl` | 19 |
| `src/lib/nogc_sync_mut/database/bug.spl` | 14 |
| `src/lib/nogc_async_mut/database/bug.spl` | 14 |
| `src/lib/common/science_math/math_block.spl` | 14 |
| `src/compiler/70.backend/vhdl_constraints.spl` | 14 |
| `src/lib/nogc_sync_mut/database/vector/store.spl` | 13 |
| `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl` | 13 |
| `src/lib/nogc_sync_mut/database/feature.spl` | 12 |
| `src/lib/nogc_async_mut/database/feature.spl` | 12 |
| `src/app/web_stack_sample/app.spl` | 12 |
| `src/compiler_rust/lib/std/src/tooling/dashboard/query.spl` | 10 |
| `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 9 |
| `src/lib/nogc_sync_mut/database/test_extended/queries.spl` | 8 |
| `src/lib/nogc_sync_mut/database/test_extended/database.spl` | 8 |
| `src/lib/nogc_sync_mut/database/test_extended/database_queries.spl` | 8 |
| `src/lib/nogc_sync_mut/database/core.spl` | 8 |
| `src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl` | 8 |
| `src/compiler/70.backend/backend/vhdl_validation.spl` | 8 |
| `src/compiler/50.mir/mir_lowering_stmts.spl` | 8 |
| `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` | 8 |
| `src/lib/nogc_sync_mut/diag.spl` | 7 |

## 8. Nil-receiver note

Per the task instruction, sites where the **receiver** may be nil are not over-reported:

- There are **zero** `?.get(` optional-chained calls in the corpus.
- Exactly one `Dict<…>?`-typed declaration exists (`baseline: Dict<text, BenchResult>?`); it does not appear in the confident set.
- More generally, the miss path (`nil` receiver contents, or a key that is absent) is **correct** under this defect. Only the **hit** path is dangerous — so a `Dict` that is usually empty is low-risk in practice but still needs the fix once it is populated.

## 9. Recommended remediation order

1. **`src/compiler/**` CRITICAL (11 sites)** — the monomorphizer, type checker, const-key checker, module resolver and VHDL backend are all on the compile path; these are the next stage-4-class segfaults.
2. **`src/app/interpreter/async_runtime/actor_scheduler.spl` (21 sites)** — densest single file, and every live-actor operation is affected.
3. **`src/os/compositor/host_compositor_core.spl` (2)** and the `src/lib` engine/database caches — these fail only on a **cache hit**, i.e. only under sustained load, which makes them look intermittent.
4. **HIGH (85)** — silent corruption is harder to debug than a segfault; treat as equally urgent once the crashes are gone.
5. **MEDIUM (60) / LOW severity (651)** — mechanical sweep once the above are done.

A repo-wide lint rule ("`.get(` on a `Dict` receiver is forbidden; use `contains_key` + indexed read") would prevent regression, and can be retired when the native codegen defect itself is fixed.
