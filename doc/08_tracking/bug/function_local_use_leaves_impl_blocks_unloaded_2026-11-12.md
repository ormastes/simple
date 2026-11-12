# Function-local lazy `use` leaves impl blocks unloaded (`method parse_outline not found`) (2026-11-12)

- **Status:** OPEN — tagged workaround landed (PR #8435/#8443); loader fix pending
- **Severity:** P2 (every structural MCP `source_open` failed on the real server path)
- **Area:** seed interpreter module loader (function-local `use` of a type whose
  methods live in an `impl` block); `src/compiler/10.frontend/treesitter.spl`,
  `src/compiler/90.tools/source_outline_v1.spl`, `src/app/source_view/service.spl`

## Symptom

A `use compiler.frontend.treesitter.outline.{TreeSitter}` written INSIDE a
function body loads the struct only. The `impl TreeSitter:` block that owns
`parse_outline` / `parse_top_level_item` (in the façade module
`compiler.frontend.treesitter`) is never loaded, so the first method call fails:

```
semantic: ...: method `parse_outline` not found on type `TreeSitter`
```

On the seed-served MCP server (`bin/simple.exe run src/app/mcp/main.spl`) the
lazy source-tool boundary imported the outline provider this way, so EVERY
`source_open` in `outline`/`focused` mode answered an error while the raw mode
and the in-process `dispatch_tool` specs stayed green (the spec file's own
module-level imports had already loaded the impl block).

## Repro

`test/01_unit/compiler/99.loader/function_local_use_leaves_impl_unloaded_spec.spl`
(`@tag:in-development`; seed-run 2026-11-12: executed=1 passed=0 failed=1,
failing with the exact message above).

## Workaround (tagged, in tree)

1. `treesitter.spl` exports a free entry `treesitter_parse_outline_v1(parser)`
   living in the module that owns the impl block.
2. `source_outline_v1.spl` imports it at MODULE level, so any route that
   reaches the provider loads the methods.
3. `service.spl` imports the provider at module level (comment marks it on
   purpose).

Prevention spec (passing, seed-run 2/2):
`test/01_unit/compiler/99.loader/module_level_use_loads_impl_prevention_spec.spl`
— covers the free-entry route and the exact MCP shape (function-local import of
the provider).

## Fix direction

Loader: when a function-local `use` binds a type, also load the owning
module's `impl` blocks for that type (same as a module-level `use`). The seed
side lives in the Rust interpreter module loader (not contained in a
pure-Simple change); the self-hosted loader must match. Remove the module-level
comments in `service.spl` and `source_outline_v1.spl` once the repro spec is
green and the `@tag:in-development` header is dropped.
