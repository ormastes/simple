# Plan: Dependency Analysis Tool + Handshake Perf + Lazy Parsing

Date: 2026-06-10
SPipe lane: `.spipe/dep-analysis-handshake-perf/state.md`
Status: Wave 1 complete; Wave 2 in progress

## 1. Research ground truth (2026-06-10)

- Module resolution: `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl`
  (`resolve_module_path`), transitive loading in `module_loader_core.spl`
  (`load_module`, `load_module_parse_only`, `loaded_module_file_paths`).
- Cycle infra: `src/compiler/00.common/dependency/graph.spl` has `ImportGraph`/
  `ImportEdge`/`CyclicDependencyError` structs with algorithms explicitly
  deferred ("will be added in later tasks"); `src/compiler/10.frontend/core/
  call_graph.spl` has the iterative-DFS back-edge pattern to copy. Rust side
  has `compiler_rust/dependency_tracker/src/graph.rs` (`check_cycles`,
  `topological_order`) — reference semantics, do not modify (fix .spl first).
- CLI registration: import in `src/app/cli/main_part1.spl`, dispatch branch in
  `src/app/cli/main_part2.spl` (`todo-scan` pattern, ~line 264).
- Deep-mode building blocks: SMF reader (`src/compiler/70.backend/linker/
  smf_reader.spl`, `smf_reader_memory_part1/2.spl` incl. `read_elf_object`),
  ELF section sizes (`elf_inspect.spl`), symbol sizes + reachability
  (`symbol_analysis.spl`), line counts (`src/app/stats/line_counter.spl`),
  closure (Rust `collect_imported_module_paths`; Simple-side loader closure).
- Lazy parsing: treesitter outline parser already skips bodies
  (`src/compiler/10.frontend/treesitter/outline.spl`, `BlockSkipPolicy`,
  `body_span`); deferred-module system exists (`register_deferred_module`,
  `try_force_any_deferred_for` triggered from `eval_ident`). `bin/simple run`
  startup is dominated by the **Rust seed** eager whole-file parse of every
  import — Simple-side lazy mode lands in the self-hosted lane first.
  Prior art: `doc/01_research/compiler/parser/lazy_parsing_prior_art.md`
  (V8 preparse, SpiderMonkey stencil, scope-metadata pitfall, indent-fence
  advantage, PIFE rule, .pyc-style cache).
- Handshake cost (interpreter oracle 476/553 ms): top import subtrees of
  `src/app/mcp/main.spl` — `dap_bridge → std.nogc_sync_mut.debug.remote`
  (~162 files, never used in handshake), `std.cli.log_modes` (~55),
  `std.log` (~14, 1 symbol used), `mcp_sdk.core.mod` fan-out (pulls shell/
  validation eagerly). Primitive hotspot: `mcp_sdk/core/json.spl` per-char
  `substring(i,i+1)` loops (`char_at`/`skip_ws`/`read_string_end`/
  `read_nested_end`), O(n·m) `find_text`, 6-chain `unescape`.

## 2. Design rules

- D1 Reuse compiler infra: complete `importgraph_add_edge` / cycle detection
  inside `00.common/dependency/graph.spl` (the planned home), modeled on
  `call_graph.spl` DFS; the deps app consumes it — no duplicate graph code.
- D2 Deps tool = `bin/simple deps <fast|normal|deep> <file>` in
  `src/app/deps/`; path resolution via `resolve_module_path`; `use`-statement
  scanning is the edge source (text-level scan, same grammar the loader uses).
- D3 Deep mode contract: input is a resolved closure `[text]` of file paths;
  three reporters (script: interfaces+lines; smf: artifact set; native:
  bytes/module via SMF symtab symbol sizes, method documented) — so it can be
  built in parallel with the graph core.
- D4 Handshake perf must not change startup arch: interface cache, probe
  cache, lazy registry, rt-forward gates all stay; improvements come from
  (a) import-graph reduction, (b) primitive json hot-loop fixes, (c) later
  lazy parsing.
- D5 Lazy parsing: two modes, whole-file default unchanged; lazy mode bridges
  treesitter outline (`fast_mode`, `body_span`) into the Simple-side module
  loader with body materialization on first call; equivalence spec + measured
  benchmark. Rust-seed parser is NOT modified in this lane.

## 3. Waves (model-tiered, disjoint file scopes)

Wave 1 (parallel Sonnet) — DONE 2026-06-10:
- W1-A DONE — `importgraph_add_edge`/`importgraph_find_cycles` in graph.spl;
  `src/app/deps/` (main.spl, scanner.spl); CLI dispatch; 17 green specs.
- W1-B DONE — `src/app/deps/deep_report.spl`; SCRIPT/SMF/NATIVE sections;
  14 green specs; hub-import case study (app.io → local counter fix).
- W1-C DONE — `find_text` → native `index_of`; 85× on 2 KB payload;
  benchmark `test/05_perf/mcp_json_perf_spec.spl`.
- W1-D DONE — `src/app/mcp/` narrowed: 61→49 modules, 130→72 ms load,
  handshake ~0.52 s (was ~0.55 s); dap_bridge dead re-import removed.

Wave 2 (after W1) — IN PROGRESS (replanned 2026-06-10 into small parallel
tasks; phase 1 tasks touch NEW files only so they can run alongside the
E0410 export-sweep agents that own existing src/compiler, src/app, src/lib
files; shared-file wiring edits land in the orchestrator integration pass):

Phase 1 (parallel now):
- [ ] W2-A1 (Sonnet, new test files only) — lazy-parse groundwork specs:
      (a) equivalence spec: treesitter outline (`fast_mode`/`body_span`)
      signature extraction vs full parse over a fixed sample of real
      modules — same fn/class/export surface; (b) parse-time benchmark
      outline-vs-full (pattern: `test/05_perf/mcp_json_perf_spec.spl`).
- [ ] W2-A2 (full-strength, new module only) — lazy loader bridge in NEW
      `src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl`:
      outline-parse module, register body spans for on-first-call
      materialization via the existing deferred-module system, gated by
      `SIMPLE_LAZY_PARSE=1`; whole-file path untouched. Returns exact
      wiring diff for `module_loader_core.spl` (applied in integration).
- [ ] W2-B1 (Sonnet, read-only) — run `bin/simple deps normal|deep` over
      the handshake closure (`src/app/mcp/main.spl`); rank reduction
      candidates by files/bytes removed; verify top candidates by actual
      symbol-usage grep; return top 3 with exact refactor steps.

Phase 2 (integration, after E0410 sweeps land):
- [ ] W2-B2 (Sonnet) — land ≥1 verified reduction refactor from W2-B1
      (AC-6); re-run deps to show the delta.
- [ ] W2-A3 (orchestrator) — apply lazy-mode wiring to
      `module_loader_core.spl`; run equivalence spec + benchmark (AC-4).
- [ ] W2-D (orchestrator) — re-measure handshake-complete budget (AC-5);
      advance `.spipe/dep-analysis-handshake-perf` phase.
- W2-C docs/guides/spipe-skill updates + tldrs (Sonnet) — DONE.

Continuous: jj commit per agent batch (explicit paths), pull/rebase, push with
origin file-count guard.

## 4. Acceptance

Mirrors `.spipe/dep-analysis-handshake-perf/state.md` AC-1..AC-7.
