# Architecture: runtime-api-block-sugar-plugins

**Phase:** 3-arch  
**Date:** 2026-04-28

---

## 1. Module Layout

### New files

| Path | Role |
|------|------|
| `src/lib/common/std/plugin/mod.spl` | Public `std.plugin` API — `load_plugin`, `register_block_plugin`, `register_desugar_rule_plugin`; wraps raw WFFI |
| `src/lib/common/std/plugin/__init__.spl` | Re-exports the public surface of `std.plugin` |
| `src/compiler/10.frontend/desugar/sugar_registry.spl` | `struct RuleRegistry`, `struct DesugarRule`, `fn rule_registry()` singleton, `fn register_desugar_rule(...)` |
| `src/compiler/10.frontend/plugin_startup.spl` | Startup entry point: scans discovery paths, parses each `.sdn` manifest, dispatches to `register_block` / `register_desugar_rule` / WFFI-based runtime-API registration |

### Modified files

| Path | Change | Key file:line anchor |
|------|--------|----------------------|
| `src/compiler/10.frontend/desugar/collection_desugar.spl` | After built-in rewrites in `fn desugar_collections`, consult `rule_registry()` table and fire matching rules | `collection_desugar.spl:42` (fn desugar_collections) |
| `src/compiler/10.frontend/frontend.spl` | Add import of `plugin_startup`; call `run_plugin_startup()` before `desugar_collections` call | `frontend.spl:39` (current `desugar_collections(expr_start, s_start)` call site) |
| `src/compiler/70.backend/backend/c_backend_translate_ops.spl` | `[STATIC-NEXT]` marker at matmul lowering site for static sugar fast-path | `c_backend_translate_ops.spl:145` (`__simple_runtime_matmul` emit) |
| `doc/04_architecture/sffi_bidirectional_interop.md` | New "Dynamic Plugin Surface" section appended (line 368 = current end) |
| `doc/01_research/local/sffi_dynamic_loading_2026-02-21.md` | Revise stale paragraph at lines 79-81: the table claiming `spl_dlopen`/`spl_dlsym`/`spl_wffi_call_i64` are `❌ whitelist` — they are now whitelisted at `mod.rs:1445-1452` |

---

## 2. Interfaces (signatures only)

### `std.plugin` public surface (`src/lib/common/std/plugin/mod.spl`)

```spl
# Load a .so plugin and register all entries declared in its manifest.
fn load_plugin(manifest_path: text) -> bool

# Register a single block definition from a plugin .so.
# block_class_name must resolve to a BlockDefinition impl via dlsym.
fn register_block_plugin(lib_path: text, block_class_name: text) -> bool

# Register a single desugar rule from a plugin .so.
# rule_symbol must point to a fn(i64) -> i64 rewrite function.
fn register_desugar_rule_plugin(lib_path: text, pattern_tag: i64, rule_symbol: text) -> bool

# Low-level: open a dynamic library and return its handle.
fn plugin_dlopen(path: text) -> i64

# Low-level: resolve a symbol in an open library handle.
fn plugin_dlsym(handle: i64, name: text) -> i64

# Low-level: call a 2-arg i64 function pointer (e.g. rt_demo_add).
fn plugin_call_i64_2(fptr: i64, a: i64, b: i64) -> i64
```

### `BlockDefinition` trait (already exists — cite as-is)

Located at `src/compiler/15.blocks/blocks/definition.spl:13`.  
v1 shape (80%): `fn kind() -> text`, `fn lexer_mode() -> i64`, `fn parse_payload(...) -> BlockValue`.  
**No changes to this trait in this feature.**

### `BlockRegistry` (already exists — cite as-is)

Located at `src/compiler/15.blocks/blocks/registry.spl:13`.  
`fn register_block(block_def: BlockDefinition)` at line 96-116.  
`fn block_registry() -> BlockRegistry` singleton.  
**No changes in this feature.** Plugin startup calls `register_block()` — same API.

### `RuleRegistry` + `DesugarRule` (new — `sugar_registry.spl`)

```spl
struct DesugarRule:
    pattern_tag: i64          # AST expr tag to match
    rewrite_fn: i64           # function pointer (i64 handle from dlsym)
    name: text                # human label for diagnostics

struct RuleRegistry:
    rules: [DesugarRule]

# Module-level singleton (initialized once at startup)
fn rule_registry() -> RuleRegistry

# Register a rule; no-op if pattern_tag already registered by same name
fn register_desugar_rule(tag: i64, fptr: i64, name: text)

# Consult registry for a given expr tag; returns rewritten node id or -1 if no rule matched
fn apply_sugar_rules(tag: i64, node: i64) -> i64
```

### Manifest schema (`.sdn` format — reuses existing `app.plugin` parser)

**Format choice:** `.sdn` (Simple Data Notation = the `.spl`-table option per pinned decision in state.md). Reuses the existing `parse_plugin_manifest_text` parser — no new format introduced.

`PluginEntry` already defined at `src/app/plugin/registry.spl:41-46`. The `.sdn` manifest extends the existing schema with two new optional fields per entry:

```
PluginEntry(
  name: "csv-block",
  library: "~/.simple/plugins/libcsv_block.so",
  version: "1.0",
  functions: ["rt_csv_parse"],
  classes: [],
  blocks: ["CsvBlockDef"],          # new: list of BlockDefinition class names
  desugar_rules: [                  # new: list of sugar rules
    DesugarRuleEntry(
      pattern_tag: 4096,            # numeric AST tag for matched expr kind
      symbol: "csv_desugar_rewrite",
      name: "csv-desugar"
    )
  ]
)
```

Parser reuse: `parse_plugin_manifest_text` from `src/app/plugin/__init__.spl` is extended to read `blocks` and `desugar_rules` fields. No new format introduced.

---

## 3. Data Flow

### Startup

1. `plugin_startup.spl::run_plugin_startup()` is called from `frontend.spl` before `desugar_collections`.
2. It scans two discovery paths in order: `<project>/.simple-plugins/*.sdn` (project), then `~/.simple/plugins/*.sdn` (user). Project entries take precedence by being registered last.
3. Each `.sdn` is parsed via `parse_plugin_manifest_text` (existing).
4. For each `PluginEntry`:
   - For each function in `functions`: calls `spl_dlopen(library)` + `spl_dlsym(handle, fn_name)`. This populates a module-level `(name→fptr)` table in `plugin_startup.spl`. Subsequent interpreter `rt_*` calls route through `dynamic_ffi::try_call_dynamic` (mod.rs:1457) which hits `library_for_symbol` in `plugin_manifest.rs`. If the manifest cache is not startup-wired (Phase 5 must verify), `plugin_startup` drives this directly via `wffi_call_N` wrappers.
   - For each name in `blocks`: `spl_dlsym(handle, block_class_name)` → constructs a `BlockDefinition` proxy → calls `register_block(proxy)`.
   - For each `DesugarRuleEntry` in `desugar_rules`: `spl_dlsym(handle, rule.symbol)` → calls `register_desugar_rule(rule.pattern_tag, fptr, rule.name)`.
5. **Block replace opt-in:** plugin blocks do not silently shadow built-ins. User source must `use plugin <name>` to activate a plugin's block under the built-in keyword. This is enforced at registry lookup: `block_registry()` returns built-in first unless an explicit opt-in is recorded in the registry.

### Per-call: `csv{}` block dispatch

User writes `csv { ... }`. Lexer calls `block_registry()` (already registry-driven via `outline_lexer.spl:84`) → finds `CsvBlockDef` (registered at startup) → enters CSV lexer mode → `parse_payload()` called on `CsvBlockDef` instance → returns `BlockValue`.

### Per-call: desugar rule firing (interpreter path — AC-3a/3b)

In `collection_desugar.spl::desugar_collections` (line 42), after the existing built-in rewrite arms, a new tail calls `apply_sugar_rules(tag, node)`. If the `RuleRegistry` has an entry for `tag`, it calls the registered `rewrite_fn` pointer via `spl_wffi_call_i64(fptr, [node], 1)`. The return value is the replacement node id (-1 = no match = leave node unchanged).

### Per-call: Cranelift JIT consultation (deferred — `[STATIC-NEXT]`)

The static fast-path hook is deferred to R2-broader. A `// [STATIC-NEXT]` comment is placed at `c_backend_translate_ops.spl:145` (matmul emit site) to mark the future insertion point where a compiled sugar-rule table would replace the runtime dispatch.

---

## 4. WFFI Calling-Convention Audit

**Variants that exist today** (grepped from `src/compiler/10.frontend/core/wffi/mod.spl`):

| Symbol | Signature |
|--------|-----------|
| `spl_dlopen` | `(path: text) -> i64` — lib handle |
| `spl_dlsym` | `(handle: i64, name: text) -> i64` — function pointer |
| `spl_wffi_call_i64` | `(fptr: i64, args: [i64], nargs: i64) -> i64` |
| `wffi_call_0` … `wffi_call_8` | convenience wrappers for 0–8 i64 args |
| `wffi_call_bool_0`, `wffi_call_bool_1` | return i64≠0 as bool |

**No f64, pointer-typed, or void-return variants exist.**

**AC-1 demo `rt_demo_add(i64, i64) -> i64`:** Fully covered by `wffi_call_2(handle, a, b)`.

**AC-3b `rt_gemm_add`:** A realistic GEMM signature is `(double* A, double* B, double* C, i64 m, i64 n, i64 k) -> void`. Pointer args fit in i64 (64-bit cast). The void return maps to ignoring the i64 result. However, **f64 scalar alpha/beta are not representable** without bit-reinterpret. AC-3b's demo must use an all-integer-or-pointer signature (e.g. no float scalars) to stay within current WFFI. If float scalars are needed, that requires a new `spl_wffi_call_f64` extern — **out-of-scope for this feature** per hard constraint. See `## Risks`.

---

## 5. Integration Points (exact insertion sites)

| File | Line | Insertion |
|------|------|-----------|
| `src/compiler/10.frontend/frontend.spl` | 39 (before `desugar_collections(expr_start, s_start)`) | Add `run_plugin_startup()` call |
| `src/compiler/10.frontend/desugar/collection_desugar.spl` | 42 (`fn desugar_collections` body end) | Add `apply_sugar_rules(tag, node)` consultation loop |
| `src/compiler/70.backend/backend/c_backend_translate_ops.spl` | 145 (matmul emit) | Add `// [STATIC-NEXT]: sugar rule table consultation for fused ops` |
| `src/compiler/15.blocks/blocks/registry.spl` | 41 (`BlockRegistry::default()`) | Add `// [STATIC-NEXT]: manifest-loaded blocks already in registry via plugin_startup` comment |
| `doc/04_architecture/sffi_bidirectional_interop.md` | 368 (end of file) | Append "Dynamic Plugin Surface" section |
| `doc/01_research/local/sffi_dynamic_loading_2026-02-21.md` | 79-81 (stale whitelist table) | Add correction note: `spl_dlopen/dlsym/wffi_call_i64` are whitelisted as of current binary (mod.rs:1445-1452) |

---

## 6. `[STATIC-NEXT]` Markers — Specific Addresses

| Role | File | Line | Description |
|------|------|------|-------------|
| (i) Rule-registry struct definition | `src/compiler/10.frontend/desugar/sugar_registry.spl` | Line 5 (above `struct RuleRegistry` — new file, line 5 is first struct) | `// [STATIC-NEXT]: replace Vec<DesugarRule> with a compile-time baked rule table in R2-broader` |
| (ii) Interpreter consultation site | `src/compiler/10.frontend/desugar/collection_desugar.spl` | After line 201 (last existing rewrite) | `// [STATIC-NEXT]: apply_sugar_rules call here; in R2-broader replace with inlined specialised lowering` |
| (iii) Cranelift / C-backend consultation site | `src/compiler/70.backend/backend/c_backend_translate_ops.spl` | Line 145 (matmul emit) | `// [STATIC-NEXT]: sugar rule table consultation for fused ops (AC-3b static path, R2-broader)` |

---

## 7. Risks / Unresolved

**R1 — WFFI f64 gap (AC-3b).**  
Only `spl_wffi_call_i64` exists. AC-3b's `rt_gemm_add` demo must use pointer args only (no float scalars). If the demo design requires f64 alpha/beta, a follow-up bug must be filed for `spl_wffi_call_f64` — it cannot be added in this feature per the hard constraint.

**R2 — Manifest cache startup wiring (AC-1 fallback path).**  
Phase 5 must verify whether `PLUGIN_MANIFEST_CACHE` in `plugin_manifest.rs` is populated at interpreter startup or only at compile time. If not startup-wired, `plugin_startup.spl` must drive WFFI directly via `wffi_call_N` (the primary path per pinned decisions). The Rust fallback (`try_call_dynamic`) is secondary.

**R3 — Block opt-in UX (AC-2).**  
The opt-in phrase "use plugin `<name>`" in the pinned decision maps to a regular module import: `use plugin.csv_block` or similar dotted-path. The existing `parse_use_decl` parser (`parser_decls_use.spl:23`) handles any dotted path — no new grammar is needed. Phase 5 must confirm that `use` of a plugin-registered block keyword activates the replace lookup correctly at the registry level. If the registry needs a new lookup mode, that is a registry change only (no grammar change, no Rust touch).

**R4 — Cranelift STATIC-NEXT site unverified.**  
The Rust Cranelift backend (`cranelift.rs`, `instr/body.rs`) works on MIR, not AST. Desugar fires at the AST level in the Simple (self-hosted) compiler (`collection_desugar.spl`). The `[STATIC-NEXT]` Cranelift site is placed at `c_backend_translate_ops.spl:145` (the Simple-side C-backend), not in the Rust Cranelift files, because the sugar rule table must fire before MIR generation. If the project later targets Cranelift JIT directly (not via C codegen), Phase 5 must locate the equivalent MIR lowering seam.

**R5 — `app.plugin` vs `std.plugin` duplication.**  
`src/app/plugin/` already has manifest parsing and a `PluginEntry` type. `std.plugin` wraps WFFI. Phase 5 must ensure the two modules share `PluginEntry` from `app.plugin.registry` rather than duplicating it.

---

## 8. AC Mapping

| AC | Architectural element |
|----|-----------------------|
| AC-1 (Runtime API plugin) | `plugin_startup.spl` scans discovery paths, parses `.sdn` manifests, calls `spl_dlopen`/`spl_dlsym` via `std.plugin.plugin_dlopen`/`plugin_dlsym`; `dynamic_ffi::try_call_dynamic` routes interpreter `rt_*` calls to the opened library |
| AC-2 (Custom block plugin) | `plugin_startup.spl` calls `register_block(proxy)` for each `blocks` entry; `block_registry()` is already used by `outline_lexer.spl:84`; `use plugin <name>` opt-in enforced at registry lookup |
| AC-3a (sugar plugin proof) | `sugar_registry.spl` `RuleRegistry` + `register_desugar_rule`; `collection_desugar.spl` tail calls `apply_sugar_rules`; trivial rule (`?:` → `if/else`) loaded from manifest at startup |
| AC-3b (PERF-SUGAR-002 wedge demo) | Same `RuleRegistry` path; `rt_gemm_add` symbol resolved via `plugin_dlsym` at startup; `[STATIC-NEXT]` marker at `c_backend_translate_ops.spl:145`; JIT verification deferred to R2-broader |
| AC-4 (Pure-Simple-first) | All new code in `.spl`; WFFI externs already whitelisted (`mod.rs:1445-1452`); zero Rust seed touch |
| AC-5 (SFFI doc updated) | New "Dynamic Plugin Surface" section appended to `sffi_bidirectional_interop.md:368`; stale paragraph in `sffi_dynamic_loading_2026-02-21.md:79-81` corrected |
| AC-6 (No regression) | `plugin_startup.spl` is no-op if no manifests found; existing `BlockRegistry::default()` and built-in desugar arms are unchanged |
| AC-7 (Verify per code-style) | No `skip()`, no TODO→NOTE; if `use plugin` grammar requires compiler change, file concrete bug/FR instead of normalizing workaround |

---

## Dependency Map

```
std.plugin.mod
  -> wffi/mod.spl (spl_dlopen, spl_dlsym, wffi_call_N)

plugin_startup  [src/compiler/10.frontend/plugin_startup.spl]
  -> std.plugin.mod (load, dlopen, dlsym)
  -> app.plugin.registry (PluginEntry, parse_plugin_manifest_text)
  -> compiler.blocks.blocks.registry (register_block, block_registry)
  -> compiler.frontend.desugar.sugar_registry (register_desugar_rule)

collection_desugar
  -> sugar_registry (apply_sugar_rules, rule_registry)

frontend.spl
  -> plugin_startup (run_plugin_startup)
  -> collection_desugar (desugar_collections)

sugar_registry
  -> wffi/mod.spl (spl_wffi_call_i64 for firing rewrite_fn)
```

No circular dependencies: `sugar_registry` does not import `collection_desugar`; `plugin_startup` does not import `frontend`.
