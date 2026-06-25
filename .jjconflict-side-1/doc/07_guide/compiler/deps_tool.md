# deps Tool — Dependency Analysis

Date: 2026-06-10.
Source: `src/app/deps/` (main.spl, scanner.spl, deep_report.spl).
Cycle detection: `src/compiler/00.common/dependency/graph.spl`
(`importgraph_add_edge`, `importgraph_find_cycles` — iterative DFS modeled on
`call_graph.spl`).
CLI dispatch: `src/app/cli/main_part2.spl` + Rust seed command table (one
sanctioned seed change; binary refreshed + stripped).
Specs: `test/01_unit/app/deps/deps_tool_spec.spl` (17 green),
`test/01_unit/app/deps/deps_deep_spec.spl` (14 green).

## Usage

```
bin/simple deps fast   <entry.spl>   # per-import transitive count + cycles
bin/simple deps normal <entry.spl>   # adds exclusive vs shared per import
bin/simple deps deep   <entry.spl>   # full closure: script/smf/native sections
```

## fast mode

Per direct import:
- transitive file count
- sorted file list
- CYCLES section — e.g.
  `src/app/mcp/assistant/session_store.spl <-> session_store_part1/2.spl`

Use this first: immediate signal on cycle existence and closure size before any
refactor.

## normal mode

Everything fast produces, plus per import:
- exclusive count (files only reachable via this import)
- shared count (files also reachable via another import)
- overlap breakdown between siblings

Use this to decide which import is worth narrowing and which dependency is
genuinely shared.

## deep mode

Input: full transitive closure (`[text]` of resolved file paths).

Three sections in every report (method printed in report header):

| Section | Content |
|---------|---------|
| SCRIPT  | exported interface symbols + code/blank/comment line counts per module |
| SMF     | sibling `.smf` artifact existence + bytes |
| NATIVE  | bytes per module — `.smf` artifact size when present, else `48 bytes/code_line` documented estimate |

## Case study: hub-import cost

`deep_report.spl` originally imported `app.stats.line_counter`, which re-exports
through the `app.io` hub (`export use x.*`). That hub pulls the full compiler
tree, including interpreter-unparseable linker modules, breaking the tool at
startup. Fix: inline a local counter (5 lines) instead.

Lesson: a hub module with `export use x.*` makes a single-symbol import cost
hundreds of files — exactly what `deps normal` exposes in the exclusive/shared
breakdown. Avoid hub imports for single symbols. Use direct submodule imports.

## Measurement knobs

```bash
SIMPLE_LOADER_TRACE=1 bin/simple deps fast src/app/mcp/main.spl
SIMPLE_PROFILE=1      bin/simple deps normal src/app/mcp/main.spl
```

## Cross-references

- TL;DR: `doc/07_guide/compiler/deps_tool_tldr.md`
- MCP startup perf guide: `doc/07_guide/app/mcp/startup_performance.md`
- Lazy parsing prior art: `doc/01_research/compiler/parser/lazy_parsing_prior_art.md`
- Dependency analysis plan: `doc/03_plan/compiler/dependency_analysis/plan.md`
- Graph implementation: `src/compiler/00.common/dependency/graph.spl`
