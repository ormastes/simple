# Seed: `xs.map(&:trim)` returns an empty list in natively built code (2026-11-21)

**Status:** OPEN (seed codegen). Source workaround in place.

## Symptom
`SdnTable.parse` (`src/lib/nogc_sync_mut/database/core.spl`) built columns with
`raw_cols.map(&:trim)`. In a binary built by the Rust seed (Phase 1,
`native-build --backend llvm`), that call returned `[]`, so every SDN table
parsed with 0 columns. Every row then fell into the overwide-legacy
`__opaque_tail` path, and `row.get("key")` was nil for all rows.

Visible effect: simple-mcp's `.simple/ctx/stats.sdn` was overwritten on every
bump (load returned `{}`), so `simple_ctx_stats` always reported 0 calls.

## Repro (seed-built, 74 modules)
```
use std.database.core.{parse_sdn_table}
fn main():
    val t = parse_sdn_table("ctx_stats | key, value |\n    search_calls, 1\n")
    # seed-built: t.columns.len() == 0; row.fields == {"__opaque_tail": "search_calls, 1"}
```

## Workaround
Explicit `for` loop with `push(raw_col.trim())`, tagged
`@workaround bug=seed_map_symbol_ref_trim_empty_2026_11_21`. Ten other
`.map(&:...)` call sites in `src/lib` and `src/app` are not on the MCP paths
and are unchanged. Remove the workaround once the seed lowers `&:method` map
references correctly, or once the MCP servers are built by a Phase 2+ compiler.
