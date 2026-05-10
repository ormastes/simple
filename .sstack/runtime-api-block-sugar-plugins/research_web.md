# Web Research: Plugin Extension Patterns
_Phase 2 external/web analyst output — runtime-api-block-sugar-plugins_

---

## 1. Per-System Reference Table

| System | Class | Discovery mechanism | Manifest format | Dyn-load, no host rebuild? | Runtime cost note |
|--------|-------|--------------------|-----------------|-----------------------------|-------------------|
| **Lua C modules / LuaRocks** | A | `require("name")` walks `package.cpath`; calls `dlopen` + resolves `luaopen_<name>` via `dlsym` | Rockspec (Lua source file declaring `build.type`, source paths) | Y — Lua VM unchanged; only the `.so` must exist on cpath | `dlopen` on first `require`; subsequent calls hit `package.loaded` cache; no VM cost |
| **Python entry_points** | A | `importlib.metadata.entry_points(group=...)` reads `.dist-info/entry_points.txt` at runtime without importing the plugin | INI-style `entry_points.txt` (group + `name = module:attr`); also declarable in `pyproject.toml [project.entry-points]` | Y — advertise-don't-load: metadata is read before any import; plugin loaded only on explicit `.load()` call | INI parse + filesystem scan at discovery; actual import deferred until `.load()` |
| **Erlang NIFs** | A | `erlang:load_nif(Path, LoadInfo)` called from module's `-on_load`; BEAM resolves all `ERL_NIF_INIT`-registered function descriptors into the module's dispatch table | No separate manifest file; descriptor is the `ErlNifFunc[]` array + `ERL_NIF_INIT` macro embedded in the `.so` | Y — BEAM unchanged; `.so` is built separately and loaded at module init | Zero-context-switch call path (fastest BEAM FFI); crash in NIF kills entire VM process |
| **Racket `#lang` / `#reader`** | B | `#reader <module-path>` or `#lang <name>` resolved to `<name>/lang/reader` module or a `reader` submodule; module is `require`'d dynamically | No separate manifest; the reader module itself is the manifest — must export `read` and `read-syntax` functions | Y — Racket runtime unchanged; reader module loaded on first encounter of `#lang` | Module load on first `#lang` use; subsequent loads hit module cache; reader runs in-process |
| **Lean 4 Lake `plugins`** | B | Lake config (`lakefile.toml` `plugins` array) lists `.so` dynlib targets; passed as `lean --plugin <path>` flags at elaboration time; initializer function called on load | TOML `lakefile.toml` `[[lean_lib]]` / `plugins = [...]` | Y (since Lean 4.20.0) — lean binary unchanged; elab extensions compiled as separate `.so` and loaded at startup | Per-plugin `dlopen` at elaboration start; elab extensions run inside the lean process with full type-system access |
| **Tree-sitter external scanners** | B | Scanner is compiled *into* the parser `.so` (as `scanner.c` in the same grammar project); parser `.so` is loaded by the host editor/tool via `dlopen` | No separate manifest; scanner symbols follow `tree_sitter_<lang>_external_scanner_{create,destroy,scan,...}` convention | Y (caveat) — tree-sitter core library unchanged; but scanner is bundled inside the parser `.so`, not a separate drop-in plugin | Scanner called inline during lex phase; must be C (non-C no longer supported); a buggy scanner corrupts parse state silently |
| **Rust proc-macros / Watt** | C | Cargo builds proc-macro crate as a `dylib`; rustc `dlopen`s it at *consumer compile time*; exports `#[proc_macro]` annotated fns. Watt variant: macro logic compiled to Wasm, executed by a tiny Wasm runtime at compile time | Cargo.toml `[lib] proc-macro = true`; no runtime manifest | Y (host = rustc unchanged) — but expansion happens at consumer *build* time, not program runtime; Watt adds sandboxing + determinism at ~3s one-time cost | Native dylib: no overhead except compile-time cost. Watt: full Wasm sandbox; macro output is pure token→token; cannot access filesystem |
| **Julia macros / `@generated`** | C | Macros defined with `macro` keyword; registered in module table at `include`/`import` time. `@generated` functions register a specialisation callback; JIT calls it on first dispatch for each type-tuple | No manifest; macros are code (Julia source); `@generated` code is a quoted `Expr` returned from a normal function body | Y — julia binary unchanged; macros/generated fns loaded by `using MyMacroModule` | Macro: pure parse-time AST rewrite (zero runtime cost). `@generated`: specialisation cached per type-tuple; subsequent calls hit compiled specialisation |

---

## 2. Pattern Catalogue

**P1 — Symbol-convention dispatch (dlopen + dlsym by name)**
One line: host calls `dlopen(path)` then `dlsym(handle, "known_prefix_<name>")` to bind a native function; no host rebuild needed.
Applies to: AC-1.
Top tradeoff: crashes in the loaded code kill the host process unless isolated (Wasm/process sandbox). The Erlang `ERL_NIF_INIT` descriptor variant adds arity + function-pointer table in one call, which is cleaner for multiple-function plugins.

**P2 — Advertise-don't-load manifest (metadata file separate from implementation)**
One line: a lightweight metadata file (INI, TOML, Lua source) describes what the plugin provides; the host reads it at startup without importing/executing the plugin, then loads on demand.
Applies to: AC-1, AC-2, AC-3.
Top tradeoff: manifest can diverge from actual plugin ABI if not validated at load time; requires a versioning/compat check step.

**P3 — Module-path reader protocol (export a fixed interface, discover by path)**
One line: host resolves block/reader name to a module path; requires the module to export a known set of functions (`read`, `parse`, `desugar`, etc.); Racket `#reader` and Lean `--plugin` both use this shape.
Applies to: AC-2.
Top tradeoff: requires a trusted module resolution path; name collisions between plugins have no built-in arbitration.

**P4 — Stub-override pattern (declare in host, override on load)**
One line: host declares a stub (`nif_error` / `package.cpath` fallback) so the function exists at compile time; the plugin replaces it at load; this is exactly SFFI Direction-B's extern-lookup model.
Applies to: AC-1, AC-3.
Top tradeoff: stub must have compatible ABI; if the plugin is absent the stub must fail gracefully, not silently succeed.

**P5 — Two-phase desugar (AST rewrite now, type-aware specialisation later)**
One line: Julia's macro/`@generated` split: macros fire at parse time with no type info; `@generated` fires at first-dispatch with full types; maps cleanly onto "dynamic-load sugar now, static-baked fast path later."
Applies to: AC-3.
Top tradeoff: the two dispatch points must be wired separately; if the pipeline has only one rewrite pass, the deferred specialisation path has nowhere to hook.

---

## 3. Anti-Patterns

**AP1 — Re-link-the-VM-on-load.** Early Lua distributions required recompiling the Lua interpreter with the extension statically linked. LuaRocks / `package.cpath` + `dlopen` replaced this. Source: lua-users wiki "Building Modules" (http://lua-users.org/wiki/BuildingModules).

**AP2 — Dylib proc-macros with unrestricted filesystem access.** Rust's native proc-macro dylib model gives macros full `std` access, enabling supply-chain attacks and non-deterministic output. Flagged in the Watt pre-RFC as a known hazard; Watt's Wasm host was proposed as a fix. Source: https://internals.rust-lang.org/t/pre-rfc-sandboxed-deterministic-reproducible-efficient-wasm-compilation-of-proc-macros/19359

**AP3 — Fork-the-parser-per-dialect.** Classic Scheme/Common Lisp history: each DSL shipped a forked reader, breaking tool interop. Racket replaced this with `#lang` module-path indirection so the core reader is never forked. Source: "Creating Languages in Racket," ACM Queue (https://queue.acm.org/detail.cfm?id=2068896).

---

## 4. Specific Recommendations per AC

**AC-1 (Runtime API plugin):**
Closest precedent — Erlang NIF (`ERL_NIF_INIT` descriptor + `erlang:load_nif/2`). The descriptor-table-in-the-.so approach maps onto SFFI Direction-B's existing extern registry: the manifest names the `.so` path; at startup the loader does `dlopen` + iterates the descriptor to bind symbol → extern slot. The Lua `luaopen_<name>` naming convention is a lightweight alternative if only one entry point per plugin is needed.
Pattern: P1 (symbol-convention dispatch) + P4 (stub-override).

**AC-2 (Custom block plugin):**
Closest precedent — Racket `#lang`/`#reader` (module-path protocol: fixed export shape, discovery by path, no host rebuild). Lean 4 Lake `plugins` field is secondary confirmation that a TOML/manifest listing of `.so` dynlibs for elaboration extensions is proven practice.
Pattern: P3 (module-path reader protocol) + P2 (advertise-don't-load manifest).

**AC-3 (Sugar plugin, dynamic-load now):**
Closest precedent — Julia macros + `@generated`: macros = dynamic AST-rewrite at parse time (your "dynamic-load now" requirement); `@generated` = type-aware specialised codegen cached per type-tuple (your deferred static fast path). Watt is secondary: same token-in/token-out contract over a sandboxed transport, confirming the interface boundary is sound.
Pattern: P5 (two-phase desugar) + P4 (stub-override for the static-baked `// [STATIC-NEXT]` slot).

---

## 5. Risks / Unknowns from External Research

- **Crash isolation:** Lua, Erlang NIF, and Lean plugins all run in-process; a buggy native plugin kills the host. Simple must decide per plugin class whether in-process (fast, dangerous) or subprocess/Wasm sandbox (safe, ~3s overhead) is acceptable. Erlang's own docs say "use with extreme care."
- **Sugar-rule dispatch split:** Julia uses two separate compile-pipeline hooks (macro expansion vs. `@generated` specialisation). It is unknown whether Simple's current pipeline has equivalent split points for interpreter vs. Cranelift JIT; if not, AC-3's deferred static path has nowhere to hook without a pipeline change.
- **Load-ordering dependency:** A sugar rule (AC-3) that rewrites to an `rt_*` call introduced by a runtime-API plugin (AC-1) must be loaded after that plugin. None of the surveyed systems solve cross-plugin dependency ordering automatically; all rely on manifest declaration order or explicit `depends_on` fields.
- **Manifest format choice is open:** Python uses INI, Lean uses TOML, Lua uses Lua-source. For Simple a `.spl`-source manifest fits the pure-Simple-first rule but adds a bootstrap ordering problem (manifest is parsed by the compiler being extended). A declarative file (TOML/JSON) avoids that. This is not resolved by external precedent alone.
- **ABI stability:** Tree-sitter requires C for external scanners; Lean plugins must match the Lean ABI. For Simple, the SFFI Direction-B extern registry ABI must be pinned before plugins can be distributed separately from the compiler.

---

## 6. Sources

1. Lua loadlib (dlopen / `luaopen_` convention): https://www.lua.org/source/5.4/loadlib.c.html
2. Lua C extensions wiki: http://lua-users.org/wiki/BuildingModules
3. LuaRocks package manager: https://luarocks.org/
4. Python entry-points specification: https://packaging.python.org/en/latest/specifications/entry-points/
5. Python creating and discovering plugins guide: https://packaging.python.org/en/latest/guides/creating-and-discovering-plugins/
6. Erlang NIF system docs: https://www.erlang.org/doc/system/nif.html
7. Erlang erl_nif API: https://www.erlang.org/doc/apps/erts/erl_nif.html
8. Racket guide — reader extensions: https://docs.racket-lang.org/guide/hash-reader.html
9. Racket guide — `#lang` reader: https://docs.racket-lang.org/guide/hash-lang_reader.html
10. Creating Languages in Racket (ACM Queue): https://queue.acm.org/detail.cfm?id=2068896
11. Lean 4 metaprogramming book — macros: https://leanprover-community.github.io/lean4-metaprogramming-book/main/06_macros.html
12. Lean 4 reference — Lake build system: https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/
13. Lean 4.20.0 release notes (dynlib/plugin ordering fix): https://lean-lang.org/doc/reference/latest/releases/v4.20.0/
14. Tree-sitter external scanners: https://tree-sitter.github.io/tree-sitter/creating-parsers/4-external-scanners.html
15. Rust `watt` crate (Wasm proc-macro runtime): https://github.com/dtolnay/watt
16. Watt pre-RFC — sandboxed Wasm proc-macros: https://internals.rust-lang.org/t/pre-rfc-sandboxed-deterministic-reproducible-efficient-wasm-compilation-of-proc-macros/19359
17. Julia metaprogramming docs: https://docs.julialang.org/en/v1/manual/metaprogramming/
