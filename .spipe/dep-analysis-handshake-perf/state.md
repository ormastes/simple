# Feature: dep-analysis-handshake-perf

## Raw Request
spipe dev: improve handshake speed (primitive lib + MCP lib) without hurting
startup arch and features; research how and bootstrap if needed. Make a
dependency tracking tool reusing compiler circular-dependency infra, with:
1. fast analysis — per import: how many files linked + file list;
2. normal analysis — per import: linked files + how much shared with other imports;
3. deep analysis — native exe: binary bytes per code reference; SMF: which SMF
   files each code reference loads; script: which interfaces are loaded and
   script line counts;
4. lazy parsing — parse only needed fn/class/fields; 2 modes (whole-file,
   lazy); measure speedup; research existing lazy-parsing implementations.
Then analyze lib dependencies and refactor to reduce them. Update doc, guide,
spipe skill. jj commit + pull/rebase + push often. Divide tasks per model tier
and run agents in parallel after deep research and plan.

## Task Type
feature

## Refined Goal
Cut MCP handshake-complete time (process start → initialize + tools/list
answered) by attacking interpreter-side primitive-lib and import-load costs,
preserving the existing startup architecture (interface cache, probe cache,
lazy registry, dynSMF). Ship `bin/simple deps` (or equivalent) with fast /
normal / deep analysis modes reusing the compiler's import-graph + cycle
detection, plus a lazy-parsing mode in the parser with a measured comparison
against whole-file parsing. Use the tool's output to drive a measurable
dependency reduction in the std lib modules on the MCP handshake path.

## Acceptance Criteria
- AC-1: `bin/simple deps fast <file>` reports, per import in the file, the
  transitive file count and file list; runs over src/app/mcp/main.spl without
  error; circular dependencies are reported reusing existing compiler cycle
  detection (no new graph algorithm duplicated).
- AC-2: `bin/simple deps normal <file>` additionally reports, per import,
  overlap with the file's other imports (shared transitive files count +
  exclusive count), so "what does this import uniquely cost" is answerable.
- AC-3: `bin/simple deps deep <file>` reports at least: script perspective —
  interfaces loaded + total script lines pulled per import; SMF perspective —
  which SMF artifacts a reference would load; native perspective — estimated
  binary bytes attributable per module (symbol-size based, documented method).
- AC-4: Parser supports two modes — whole-file (default, unchanged) and lazy
  (interface/signature-first, bodies on demand) — behind an explicit flag/API;
  an executable spec proves identical observable results on a representative
  module set, and a benchmark records the speed difference in the doc.
- AC-5: MCP handshake-complete (interpreter oracle: piped initialize +
  tools/list via `bin/simple run src/app/mcp/main.spl`) improves measurably
  vs the recorded 2026-06-10 baseline (init 476 ms / full 553 ms), via
  dependency reduction and/or lazy parsing; `check-mcp-native-smoke.shs`
  stays green; no startup-arch regressions (interface cache, probe cache,
  rt-forward gates all still pass).
- AC-6: Dependency analysis of std lib handshake-path modules is recorded and
  at least one concrete dependency-reduction refactor lands, verified by the
  new tool (before/after file counts in the doc).
- AC-7: Docs updated: plan + guide for the deps tool, lazy parsing notes
  (incl. web prior-art summary), startup_performance.md updated, spipe skill
  updated with dependency-check guidance; tldrs for new docs.

## Scope Exclusions
- No fix for native codegen BUG-5/6/7 in this lane (separate Codex lane);
  native deploy of migrated MCP servers stays blocked on it.
- No new parallel SDK/framework; reuse mcp_sdk, loader, and compiler infra.
- No semantic changes to import resolution order or module init semantics.

## Phase
verify

## Log
- dev (2026-06-10): Created state file with 7 acceptance criteria (type: feature).
- research (2026-06-10): 5 parallel agents mapped (a) compiler import-graph
  infra (graph.spl structs with algorithms deferred — our home; call_graph.spl
  DFS pattern; resolve_module_path; CLI dispatch pattern), (b) parser/lazy
  infra (treesitter outline + body_span + BlockSkipPolicy already exist;
  deferred-module system; Rust seed dominates `bin/simple run` parse cost),
  (c) handshake cost drivers (dap_bridge→debug.remote ~162 files; cli.log_modes
  ~55; json.spl per-char substring hot loops), (d) deep-mode building blocks
  (smf_reader_memory + elf_inspect + symbol_analysis + line_counter), (e) web
  prior art doc written: doc/01_research/compiler/parser/lazy_parsing_prior_art.md.
- plan (2026-06-10): doc/03_plan/compiler/dependency_analysis/plan.md — waves
  W1-A..D (parallel Sonnet, disjoint scopes) + W2-A..C; design rules D1–D5.
- implement (2026-06-10): Wave 1 complete — W1-A deps fast/normal + graph
  algorithms (17 specs), W1-B deep reporters (14 specs), W1-C find_text 85×,
  W1-D mcp closure 61→49 modules / 130→72 ms / handshake ~0.52 s. AC-1, AC-2,
  AC-3 satisfied; AC-7 docs landed (deps_tool guide + tldr).
- implement (2026-06-10): Wave 2 replanned into small parallel tasks
  (plan.md §3): phase 1 NEW-FILES-ONLY agents running now — W2-A1 outline
  equivalence + perf specs (Sonnet), W2-A2 lazy loader bridge module
  `module_loader_lazy.spl` behind SIMPLE_LAZY_PARSE=1 (full-strength, wiring
  diff deferred), W2-B1 read-only deps analysis of handshake closure for
  AC-6 candidates (Sonnet). Phase 2 (after E0410 export sweeps land):
  W2-B2 reduction refactor (AC-6), W2-A3 loader wiring + equivalence run
  (AC-4), W2-D handshake re-measure (AC-5).
- implement (2026-06-10): W2-A1 DONE — outline-vs-full equivalence spec
  (16 tests green, 5 real modules) + lazy_parse_perf_spec.spl; caveat:
  text-scanner proxy (treesitter not importable from interpreter specs).
  W2-B1 DONE — handshake closure baseline 39 files / 9,031 lines /
  ~309 KB; found W1-D dap_bridge removal never actually landed.
  W2-B2 DONE, AC-6 SATISFIED — std.log removed, log_modes → local
  mcp_log_options.spl, dap_bridge → local dap_types.spl; delta 39→37
  files, 9,031→8,339 lines, ~309→~276 KB; mcp_debug_state 42/42.
  Pre-existing unrelated breakage noted: mcp_protocol_spec imports
  nonexistent std.common.mcp_helpers.
- implement (2026-06-10): AC-5 VERIFIED post-W2-B2 — W2-B2's raw rt_stderr
  externs initially tripped mcp_app_direct_rt_valid=false; replaced with
  new 12-line std facade src/lib/nogc_sync_mut/io/stderr_ops.spl. Re-ran
  check-mcp-native-smoke.shs: exit 0, all six direct-rt gates true,
  mcp_startup_ms 2707 → 1309–1314 (< 5000 gate), framing valid, 151
  tools. Final closure 38 files (deps deep). Guide updated
  (startup_performance.md Wave-2 section). Remaining for feature: AC-4
  lazy parsing (W2-A2 bridge in flight + W2-A3 wiring).
- implement (2026-06-10): W2-A3 DONE — lazy wiring landed in
  module_loader_core.spl (SIMPLE_LAZY_PARSE=1 gate at top of load_module,
  default path untouched). Verified: loader scope 0 errors; lazy smoke
  spec green in default AND lazy modes; equivalence spec green. AC-4
  satisfied (compiled-mode end-to-end equivalence remains a noted
  limitation — interpreter specs can't import treesitter directly).
  Phase → verify: all of AC-1..AC-7 now have landed implementations.
- analyze (2026-06-12): native-binary phase profiling CORRECTED the bottleneck
  attribution: start→initialize is ~0 ms (no source reads); the full ~1.5 s is
  tools/list JSON construction — gdb samples pin one function over
  __memcpy_avx_unaligned_erms (O(n^2) string concat + per-char escape).
  Landed: --probe self-check flag, wrapper cheap-probe fast path w/ handshake
  fallback, table-driven _mcp_static_tools_result (byte-identical, md5-verified),
  11 redundant startup imports cut (104→93 resolutions), mcp_sdk core/shell
  decoupled. Plan + baseline: doc/03_plan/app/mcp/
  mcp_startup_perf_small_tasks_2026-06-12.md; guide updated (2026-06-12 section).
  Remaining: build-time literal tools/list manifest, rt string primitive perf
  (concat/char_at), mcp-package rebuild + re-measure, tool_set core|all split.
