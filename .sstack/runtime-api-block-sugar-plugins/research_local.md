# Local Research Brief — runtime-api-block-sugar-plugins

**Phase:** 2-research (local analyst)
**Date:** 2026-04-28

---

## 1. SFFI Runtime-API Plugin Surface

### What exists

**Plugin manifest infrastructure (Rust side):**
- `src/compiler_rust/compiler/src/plugin_manifest.rs` — `PLUGIN_MANIFEST_CACHE`,
  `library_for_symbol(name)`, `manifest_error()`, `resolve_manifest_class()`,
  `try_call_manifest_library()`, `try_call_manifest_class_method()`.
- `src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs:697` —
  `try_call_dynamic(name, args)`: resolution order: (1) manifest library lookup
  via `library_for_symbol`, (2) main `libsimple_runtime` dlsym, (3) satellite
  libs by `rt_PREFIX_*` convention.
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1457-1459` —
  fallback arm in the dispatch match calls `dynamic_ffi::try_call_dynamic`
  for any `rt_*` name not in the built-in table.
- WFFI (`spl_dlopen`/`spl_dlsym`/`spl_wffi_call_i64`) **is** whitelisted at
  `mod.rs:1445-1452` — contradicts the Feb-2026 research doc which said they
  were blocked.

**Plugin CLI (Simple side):**
- `src/app/plugin/loader.spl` — `plugin_library_exists(entry)`.
- `src/app/plugin/main.spl` — `simple plugin install <manifest.sdn>`,
  `simple plugin list`, `simple plugin remove <name>`.
- `src/app/plugin/__init__.spl` — exports `load_plugin_manifest`,
  `parse_plugin_manifest_text`, `save_plugin_manifest`, `merge_plugin_entries`.

**WFFI Simple bindings:**
- `src/compiler/10.frontend/core/wffi/mod.spl:14-17` —
  `extern fn spl_dlopen`, `extern fn spl_dlsym`, `extern fn spl_wffi_call_i64`
  with `wffi_load`/`wffi_call_N` wrappers.

### What's missing / the gap for AC-1

The `try_call_dynamic` path routes an unknown `rt_*` name through the manifest
cache (`library_for_symbol`). The critical open question: does dropping a
`.sdn` manifest + `.so` via `simple plugin install` populate
`PLUGIN_MANIFEST_CACHE` before the first extern call? This requires verifying
that `plugin_manifest.rs` reads the on-disk manifest at interpreter startup
(not only at compile time). If startup wiring exists, AC-1 demo may require
**zero source change**. If it is only wired at compile-time build, a one-line
startup hook is needed in the interpreter init path — but still no new compiled-in
`rt_*` symbol is needed.

---

## 2. Block Registry Surface

### What exists (substantially landed)

- `src/compiler/15.blocks/blocks/registry.spl:13` — `struct BlockRegistry`.
- `src/compiler/15.blocks/blocks/registry.spl:41-65` — `BlockRegistry::default()`
  hardcodes `reg_register(reg, MathBlockDef())`, `LossBlockDef()`, `NogradBlockDef()`,
  `ShellBlockDef()`, `SqlBlockDef()`, `RegexBlockDef()`, `JsonBlockDef()`,
  `MarkdownBlockDef()`.
- `src/compiler/15.blocks/blocks/registry.spl:96-116` — global `block_registry()`
  singleton + `register_block(block_def)` public API.
- `src/compiler/15.blocks/blocks/definition.spl:13` — `trait BlockDefinition` with
  `fn kind()`, `fn lexer_mode()`, `fn parse_payload()`.
- `src/compiler/15.blocks/blocks/builtin_blocks_math.spl:147,216,279` —
  `MathBlockDef`, `LossBlockDef`, `NogradBlockDef` already implement the trait.
- `src/compiler/15.blocks/blocks/easy.spl` — `define_block` / `define_const_block`
  simplified API.
- `src/compiler/15.blocks/blocks/unified_registry.spl` — `UnifiedRegistry` merging
  blocks + literal prefixes, used by `UnifiedRegistry::from_config(literals_config, block_registry)`.
- `src/compiler/10.frontend/treesitter/outline_lexer.spl:12,37,84` —
  `OutlineLexer` holds a `BlockRegistry` field, initialized via `block_registry()`.

### The gap for AC-2

The `block_registry()` global is initialized only from hardcoded `BlockRegistry::default()`.
There is no manifest-driven loader that reads a `.spl` plugin file or `.sdn` manifest
at startup and calls `register_block()`. The lexer/parser dispatch is already
registry-driven in `outline_lexer.spl`; the gap is purely "who populates the registry
at startup". AC-2 needs a startup hook (in the compiler init path) that reads a
plugin manifest, instantiates each named `BlockDefinition`, and calls `register_block`.

The anchor doc's `lexer.spl:682-808` citation is stale — blocks have been migrated
to `src/compiler/15.blocks/` and the outline-lexer uses `BlockRegistry`. No code
change is needed to the lexer or parser dispatch themselves.

---

## 3. Sugar/Desugar Plugin Surface

### Pipeline location

Desugar runs at the AST level, before type-checking, in:
- `src/compiler/10.frontend/desugar/collection_desugar.spl:42` —
  `fn desugar_collections(start_from, stmt_start)` loops over `expr_tag` arena and
  dispatches to hand-coded `try_rewrite_assign` (line 77),
  `try_rewrite_compound_assign` (line 142), `try_rewrite_chars_iter_*` (lines 177,190).
- Other passes: `placeholder_lambda.spl`, `desugar_async.spl` — specialized,
  not generalizable to a rule table.

### What's a table vs. hand-coded

`collection_desugar.spl` is entirely hand-coded `if tag == EXPR_ASSIGN` match arms.
There is no rule-table or registry. The `A @ B + v → rt_gemm_add` pattern
(PERF-SUGAR-002) is not yet implemented; there is no math-block expression-fusion pass.

### The seam for AC-3

The seam is `fn desugar_collections`: it could be augmented with a
`_sugar_rules: [(pattern_tag, rewrite_fn)]` table consulted after the built-in
checks. A new `register_desugar_rule(tag, fn)` in the same module (or a sibling
`sugar_registry.spl`) is the minimum hook. The `[STATIC-NEXT]` marker can annotate
the table entry that corresponds to a future Cranelift-lowered fast path.

No sugar registry exists yet — this is the most greenfield of the three ACs.

---

## 4. Reusable Components

- `src/app/plugin/` — manifest install/list/remove CLI + `PluginEntry` type.
- `src/compiler_rust/compiler/src/plugin_manifest.rs` — `PLUGIN_MANIFEST_CACHE`,
  `library_for_symbol`, `try_call_manifest_library` (Rust, already wired in interpreter).
- `src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs` —
  `try_call_dynamic` fallback arm (Rust).
- `src/compiler/10.frontend/core/wffi/mod.spl` — `wffi_load`/`wffi_call_N` Simple
  wrappers (whitelisted in interpreter as of current binary).
- `src/compiler/15.blocks/blocks/registry.spl` — `BlockRegistry`, `register_block`,
  `block_registry()` singleton.
- `src/compiler/15.blocks/blocks/definition.spl` — `trait BlockDefinition`.
- `src/compiler/15.blocks/blocks/easy.spl` — simplified `define_block` API.
- `src/compiler/15.blocks/blocks/unified_registry.spl` — `UnifiedRegistry` (blocks+literals).
- `src/compiler/10.frontend/desugar/collection_desugar.spl` — existing AST-level
  desugar pass (the seam for AC-3).

---

## 5. Constraints

- Interpreter mode only for test verification (`feedback_compile_mode_false_greens.md`).
- `.spl` execution is default; SMF cache only behind `SIMPLE_MCP_USE_CACHE=1`
  (`feedback_mcp_cache_off_by_default.md`).
- No `skip()`, no weakened assertions, no TODO→NOTE (`feedback_no_coverups.md`).
- No source change in `src/compiler_rust/` unless bootstrap explicitly cannot
  resolve the plugin path (`feedback_extern_bootstrap_rebuild.md`).
- Block plugin manifest shape must be minimal: keyword + lexer_mode + parser_fn
  (the 80% case per `custom_blocks_user_friendly_api.md`).
- jj VCS, work on main only, no branches (`vcs.md`).
- No over-engineering — implement what the AC requires, nothing more (`code-style.md`).

---

## 6. Risks / Unknowns

- **Manifest startup wiring (AC-1):** Unknown whether `plugin_manifest.rs`
  `PLUGIN_MANIFEST_CACHE` is loaded at interpreter startup or only at compile time.
  If startup wiring is absent, a small Rust change is needed — but it is a one-liner
  in the interpreter init, not a new `rt_*` extern. Phase 3 must resolve this before
  implementation.
- **Doc staleness — WFFI whitelist:** `sffi_dynamic_loading_2026-02-21.md` says
  `spl_dlopen` is blocked (❌ whitelist); `mod.rs:1445-1452` shows it is now
  whitelisted. All Phase 3 plans must use the current code, not the Feb-2026 research.
- **Block registry startup hook location:** `block_registry()` is called from
  `outline_lexer.spl:84`. Plugin entries must be loaded before first `block_registry()`
  call. The compiler init sequence must be checked to find the right injection point.
- **No sugar rule table:** AC-3 is fully greenfield. A `sugar_registry.spl` must be
  designed and wired into `collection_desugar.spl` — the only prior art is the
  hand-coded `try_rewrite_*` functions.
- **Math-block lowering gap:** PERF-SUGAR-002 (`A @ B + v → rt_gemm_add`) is not
  implemented; the `c_backend_translate_ops.spl:145` matmul lowering handles `@` but
  no fusion. The AC-3 demo plugin may need a new `rt_gemm_add` extern — confirm
  whether this violates AC-4 (pure-Simple-first) or whether `spl_wffi_call_i64`
  can bridge it without a new compiled-in symbol.
- **`app/plugin/registry.spl` location:** `plugin_main.spl` imports from
  `app.plugin.registry` but this file was not found during search. Verify it exists
  and contains `PluginEntry` type definition before Phase 5.
