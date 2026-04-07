# Simple Language Compiler - Development Guide

**Also available as:** [AGENTS.md](AGENTS.md) (redirect to this file)

Impl in simple unless it has big performance differences.

**Primary compiler implementation is in Simple.** Bootstrap uses a Rust seed and produces a self-hosted Simple compiler.

### Binary Architecture

| Binary | Path | Role | Source |
|--------|------|------|--------|
| **Real binary** | `bin/release/simple` (`.exe` on Windows) | Full interpreter/compiler (production) — **fully self-sufficient** | Compiled from Simple source by Simple compiler |
| **Platform binaries** | `bin/release/<triple>/simple` | Per-platform release binaries (x86_64-pc-windows-msvc, etc.) | Same as above, organized by target triple |

- **Rust seed (dev bootstrap)** — build with `cargo build --profile bootstrap -p simple-driver` in `src/compiler_rust`; output at `src/compiler_rust/target/bootstrap/simple` (`.exe` on Windows). Use it to (a) compile the pure Simple compiler + essential libs, then (b) recompile with the freshly built Simple binary to get the final self-hosted `bin/simple`.
- **NEVER copy the Rust bootstrap binary to `bin/release/simple`** — `bin/release/simple` is the **self-hosted** binary compiled by Simple itself. The Rust bootstrap is only a seed for bootstrapping; it goes to `src/compiler_rust/target/bootstrap/simple`, not to `bin/release/`.
- **Bootstrap entry points**: `src/app/cli/main.spl` (full CLI), `src/app/cli/bootstrap_main.spl` (minimal entry for staged bootstrap — used by `bootstrap-windows.sh` and CI)

- **`bin/release/simple` is fully self-sufficient** — all compilation, interpretation, file execution, and test running happens **in-process** via direct function calls (`aot_c_file()`, `compile_native()`, `interpret_file()`, `aot_vhdl_file()`). No subprocess calls to `bin/simple` or `bin/release/simple`.
- The only external tool calls are system tools: `clang`/`clang++`/`cl.exe`/`clang-cl`, `gcc`, `mold`/`lld`/`lld-link`/`link.exe`/`ld`, `llc`, `uname`/`cmd`, `which`/`where`

---

## Agents (Task Tool)

Use these agent definitions when spawning Task subagents. Located in `.claude/agents/`.

| Agent | Use When | Key Skills |
|-------|----------|------------|
| **code** | Writing/editing Simple code, implementing features | `/coding`, `/design`, `/sffi` |
| **test** | Writing tests, fixing test failures, analyzing results | `/test`, `/sspec` |
| **debug** | Investigating bugs, tracing errors, profiling | `/debug` |
| **debug-analyst** | Interactive debugging with DAP+LSP enrichment | `/debug-lsp`, `/debug` |
| **explore** | Finding files, understanding structure, researching | `/research`, `/architecture` |
| **docs** | Writing research/design/guide docs, reports | `/doc`, `/todo` |
| **vcs** | Committing, pushing, syncing, viewing history (jj/git) | `/sync` |
| **infra** | MCP servers, database library, stdlib, SFFI | `/mcp`, `/database`, `/stdlib`, `/sffi` |
| **build** | Building project, creating releases | `/release` |
| **ml** | Machine learning features, neural networks | `/deeplearning` |
| **t32** | Installing T32 MCP, CMM LSP plugin setup | `/t32` |
| **sstack/*** | SStack phase agents (intake, research, arch, spec, implement, refactor, verify, ship) | `/sstack` |

**Usage pattern:** When spawning a Task, include the relevant agent context:
```
Read .claude/agents/code.md and use its rules to implement <feature>
```

---

## Cooperative Phase Dev

Claude owns **Step 1 (research)** and **Step 5 (design quality)** in multi-LLM cooperative pipeline:
```
Step 1: Claude /research  →  Step 2: Codex $research  →  Step 3: Gemini /design (UI)
→  Step 4: Codex $design (arch)  →  Step 5: Claude /design (quality)
```
Solo mode: `/research` → `/design` → `/impl` → `/verify` → `/release` (fully self-sufficient)
See: `doc/guide/llm_cooperative_dev_phase.md`

---

## Skills Reference

Invoke with `/skill-name` for detailed guidance. Located in `.claude/skills/`.

| Skill | Purpose |
|-------|---------|
| `sstack` | SStack pipeline — 8-phase BDD/TDD + fresh orchestrators + specialized roles (sub-40% context) |
| `sync` | Pull/rebase/push with file-count safety, worktree-aware |
| `test` | Test writing, methodology, and container testing (safe/isolated runs) |
| `sspec` | SSpec BDD framework - matchers, hooks, structure |
| `coding` | Simple language rules, coding standards |
| `impl` | End-to-end implementation workflow from requirements through VCS sync |
| `agents` | Agent loop iteration patterns and multi-agent team orchestration |
| `ui` | TUI/GUI mockup design |
| `arch` | Architecture + system test design |
| `design` | Detail design — data structures, algorithms, module interactions |
| `architecture` | Compiler pipeline, module structure |
| `research` | Step 1: Local+domain research with agent teams (Claude) |
| `research_codex` | Step 2: Forked agent research + requirement selection (Codex plugin) |
| `gemini_ui_design` | Step 3: TUI/GUI design generation (Gemini plugin) |
| `verify` | Production readiness verification (Claude + MCP agent plugin) |
| `debug` | Debugging, tracing, fault detection |
| `debug-lsp` | DAP+LSP tool chaining for debug session analysis |
| `refactor` | Code quality refactoring workflow and verification checklist |
| `stdlib` | Stdlib module development |
| `todo` | TODO/FIXME comment format |
| `doc` | Documentation writing workflow — all 10 doc types, relationship model |
| `deeplearning` | ML pipeline operators, dimension checking |
| `sffi` | FFI wrapper patterns |
| `database` | BugDB, TestDB, FeatureDB, query builder |
| `mcp` | MCP server implementation |
| `release` | Release process and versioning |
| `cuda` | GPU/CUDA/SIMD programming, kernel syntax, GPU memory |
| `t32` | TRACE32 setup, `scripts/t32q.shs` container lifecycle, GUI reopen flow, RCL/GDB interfaces, PRACTICE scripts, probe troubleshooting |
| `worktree` | JJ workspace isolation and parallel working-copy workflow |
| `rule` | Engineering rules, doc folder map, ADR process |
| `sstack` | SStack orchestrator -- Superpowers+GSD+GStack 8-phase pipeline |

**Full Syntax Reference:** `doc/07_guide/quick_reference/syntax_quick_reference.md`
**SSpec Template:** `.claude/templates/sspec_template.spl`
**Doc Model:** `doc/FILE.md` — PLAN → REQ → FEATURE → TESTS relationship

---

## Critical Rules

### Version Control
- Use **jj** (Jujutsu) as primary VCS, colocated with git
- **NEVER create branches** - work directly on `main`
- Commit: `jj commit -m "message"` (auto-tracks all changes, no staging needed)
- Push: `jj bookmark set main -r @- && jj git push --bookmark main`
- Fetch: `jj git fetch && jj rebase -d main@origin`

### Language
- **ALL code in `.spl` or `.shs`** - No Python, no Bash (except 3 bootstrap scripts in `scripts/`)
- **Scripts:** Use `.shs` for shell scripts that need to remain shell (e.g., container entrypoints)
- **Generics:** `<>` not `[]` - `Option<T>`, `List<Int>`
- **Pattern binding:** `if val` not `if let`
- **Constructors:** `Point(x: 3, y: 4)` not `.new()`
- **`?` is operator only** - never in names. Use `.?` over `is_*` predicates
- **NO inheritance** - `class Child(Parent)` is NOT supported. Use composition, alias forwarding, traits, or mixins instead
- **SDN format** for all config/data files, not JSON/YAML

### Tests
- **NEVER skip/ignore** failing tests without user approval
- **Built-in matchers only:** `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`
- **Interpreter mode limitation:** Test runner only verifies file loading, NOT `it` block execution
- **Live API tests:** `test/system/llm_caret_live_comprehensive_spec.spl` requires `CLAUDECODE=` env var
- **Test costs:** Live LLM tests cost ~$1-2 per run, use sparingly

### TODOs
- **NEVER convert TODO/FIXME to NOTE** - that hides work, not resolves it
- Either **implement** the TODO or **delete the code entirely** if it's not needed
- If a TODO cannot be implemented yet, leave it as TODO

### Code Style
- **NEVER over-engineer** - only make requested changes
- **NEVER add unused code** - delete completely
- **DO NOT ADD REPORT TO GIT** unless requested
- For MCP, LSP, and tool-server work, design must review startup path, hot request paths, cache or index strategy, invalidation strategy, and startup/latency/RSS targets
- Production wrappers should execute cached compiled artifacts rather than raw source entrypoints
- Repeated full-tree scans, repeated rereads, shell-outs, and retry sleeps in hot request handlers require explicit design justification and verification evidence
- Verify perf-sensitive tooling with warm startup time, representative request latency, and max RSS on realistic fixtures

---

### AI CLI Plugin Distribution
- Claude plugins: `tools/claude-plugin/` (local marketplace, packaging script)
- Gemini extension: `gemini-extension.json` (auto-discovered via `gemini-cli-extension` GitHub topic)
- MCP registry: `tools/mcp-registry/` (npm wrapper for native binary)
- Guide: `doc/07_guide/tooling/ai_cli_registration.md`

### MCP Servers (`.mcp.json`)
| Server | Binary/Command | Purpose |
|--------|---------------|---------|
| `simple-mcp` | `bin/simple_mcp_server` | Simple language compiler MCP |
| `simple-lsp-mcp` | `bin/simple_lsp_mcp_server` | Simple LSP via MCP bridge |
| `t32-mcp` | `bin/t32_mcp_server` | TRACE32 debugger MCP (fast-start wrapper) |
| `t32-lsp-mcp` | `bin/t32_lsp_mcp_server` | TRACE32 CMM LSP via MCP |

---

## Setup

```bash
# Create bin/simple symlink (auto-detects platform triple)
scripts/setup.sh
# Windows CMD: scripts\setup.cmd

# Install MCP config (auto-detects OS)
sh config/mcp/install.shs
# Windows without sh: manually copy config/mcp/win/.mcp.json to .mcp.json
```

---

## Quick Commands

```bash
# Build
bin/simple build                    # Debug build
bin/simple build --release          # Release build

# Test
bin/simple test                     # All tests
bin/simple test path/to/spec.spl   # Single file
bin/simple test --list              # List tests
bin/simple test --only-slow         # Slow tests

# Container Testing (safe/isolated) - see `/test` skill for full details
scripts/local-container-test.shs unit                     # Unit tests in container
scripts/local-container-test.shs quick path/to/spec.spl  # Single test
scripts/ci-test.sh                                       # CI-style execution

# Quality
bin/simple build lint               # Linter
bin/simple build fmt                # Formatter
bin/simple build check              # All checks
bin/simple build --warn-docs        # Check documentation coverage

# Documentation Coverage
bin/simple stats                    # Show doc coverage in stats
bin/simple stats --json             # JSON with doc metrics
bin/simple doc-coverage             # Terminal coverage report
bin/simple doc-coverage --format=md # Markdown report
bin/simple doc-coverage --missing   # Show undocumented items

# Tools
bin/simple fix file.spl --dry-run   # Preview fixes
bin/simple todo-scan                # Update TODO tracking
bin/simple bug-add --id=X           # Add bug
bin/simple bug-gen                  # Generate bug report

# Bootstrap (Rust seed → Simple → Self-host)
# Stage 1: Build Rust seed
cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver
# Stage 2: Compile Simple compiler with Rust seed
src/compiler_rust/target/bootstrap/simple native-build \
  --entry src/app/cli/bootstrap_main.spl -o build/bootstrap/simple_stage2
# Stage 3: Self-host recompile
build/bootstrap/simple_stage2 native-build \
  --entry src/app/cli/main.spl -o bin/release/simple
# Windows: use bootstrap-windows.sh (handles .exe, MSVC/MinGW detection)
scripts/bootstrap/bootstrap-windows.sh
# Linux/FreeBSD: use bootstrap-from-scratch.sh
scripts/bootstrap/bootstrap-from-scratch.sh

# LLM Integration Testing (requires claude CLI + auth, ~$1-2 per run)
CLAUDECODE= bin/simple test test/system/llm_caret_live_comprehensive_spec.spl
```

**Live LLM Tests:** The comprehensive test suite (`test/system/llm_caret_live_comprehensive_spec.spl`) makes **22 real Claude API calls** covering:
- Single-shot responses (5 tests)
- System prompt adherence (2 tests)
- Multi-turn conversations with session resume (6 turns, 5 tests)
- Code tutor progressive Q&A (5 turns, 4 tests)
- Shopping list state tracking (5 turns, 4 tests)
- Edge cases (2 tests)

**Note:** Interpreter mode test runner only verifies file loading. The `it` block bodies don't execute in interpreter mode, so live tests appear as "1 passed, 6ms" but don't make real API calls. Use compiled mode for actual execution.

---

## Syntax Essentials

```simple
val name = "Alice"                    # Immutable (preferred)
name := "Alice"                       # Walrus operator (:= is val synonym)
var count = 0                         # Mutable

print "Hello, {name}!"               # String interpolation (default)
print r"raw: \d+"                     # Raw string (no interpolation)

fn square(x):
    x * x                             # Implicit return

# Type aliases (working)
type Point2D = Point                  # Type alias
alias Optional = Option               # Class alias

# Function aliases (NOT YET IMPLEMENTED - use delegation instead)
fn println(msg): print(msg)           # Delegation workaround

class Point:
    x: i64
    y: i64
    fn get_x() -> i64: self.x        # Immutable method (self implicit)
    me move(dx: i64):                 # Mutable method ('me' keyword)
        self.x = self.x + dx
    static fn origin() -> Point:      # Static method
        Point(x: 0, y: 0)

match value:
    Some(x): process(x)
    nil: ()                           # Unit value

pass_todo                             # TODO marker (not yet implemented)
pass_do_nothing                       # Intentional no-op
pass_dn                              # Alias for pass_do_nothing
pass                                  # Generic no-op (use specific variants)

user?.name ?? "Anonymous"             # Optional chaining + coalescing
items.map(\x: x * 2)                 # Lambda
items.map(_ * 2)                     # Placeholder lambda (_ = param)
items.map(_1 * 10)                   # Numbered placeholder (_1, _2)
words.map(&:len)                     # Method reference (&:method)
[for x in 0..10 if x % 2 == 0: x]   # Comprehension
```

**Operators:** `|>` pipe, `>>` compose, `~>` layer connect, `**` power, `m{ x^2 }` math blocks

See `doc/guide/quick_reference/syntax_quick_reference.md` for complete reference.

---

## Project Structure

```
src/
  app/              # Applications (cli, build, mcp, mcp_jj, io, test_runner_new, desugar)
  lib/              # Standard library — `use std.X` resolves here (resolver searches lib/*/ subdirs)
    common/         # Pure functions, no mutation (text, math, json, crypto, encoding, etc.)
    nogc_sync_mut/  # Sync mutable, no GC (ffi, fs, net, http, database, mcp, spec, etc.)
    nogc_async_mut/ # Async mutable, no GC (actors, async, threads, generators, etc.)
    gc_async_mut/   # GC + async (gpu, cuda, torch, pure ML library)
    nogc_async_mut_noalloc/  # Baremetal, execution, memory, qemu
  runtime/          # Native runtime and support libraries
  compiler/         # Unified compiler — numbered layers (NN.name/ prefix stripped for imports)
    00.common/      # Error types, config, effects, visibility, diagnostics, registry
    10.frontend/    # Lexer, parser, AST, treesitter, desugar, parser types
    15.blocks/      # Block definition system (22 files)
    20.hir/         # HIR types, definitions, lowering, inference
    25.traits/      # Trait def, impl, solver, coherence, validation
    30.types/       # Type inference, type system, dimension constraints, phase files
    35.semantics/   # Semantic analysis, lint, macro check, resolve, const eval
    40.mono/        # Monomorphization (18 files), instantiation
    50.mir/         # MIR types, data, instructions, lowering, serialization
    55.borrow/      # Borrow checking, GC analysis
    60.mir_opt/     # MIR optimization passes (17 files)
    70.backend/     # Backends (LLVM, C, Cranelift, WASM, CUDA, Vulkan, Native), linker
    80.driver/      # Driver, pipeline, project, build mode, incremental
    85.mdsoc/       # MDSOC (virtual capsules, feature, transform, weaving, adapters)
    90.tools/       # API surface, coverage, query, symbol analyzer, AOP
    95.interp/      # Interpreter, MIR interpreter, execution
    99.loader/      # Module resolver, loader
  i18n/             # Internationalization
test/               # Test files (lib, app, compiler, benchmarks)
doc/                # Documentation (numbered folders, see below)
    01_research/      # Research (local impl analysis, domain/external)
    02_requirements/   # Requirements (feature, nfr, ui)
    03_plan/          # Plans (arch, design, sys_test, agent_tasks)
    04_architecture/  # Architecture (ADRs, rules, formats)
    05_design/        # Design documents
    06_spec/          # SSpec-generated specs (mirrors src/ structure)
    07_guide/         # User guides, tutorials
    08_tracking/      # Bug, test, todo, task, build tracking
    09_report/        # Implementation reports
    10_metrics/       # Dashboards, coverage
    archive/          # Historical/deprecated docs
bin/                # Binaries (simple wrapper, release/simple = real binary)
build/bootstrap/    # Bootstrap artifacts (stage2/, stage3/, full/)
tools/              # Development tools (docker containers, windows/ build helpers)
scripts/            # Bootstrap bash scripts (3 only)
.claude/            # Agents, skills, templates
```

**Import namespace:** `use std.X` and `use lib.X` both resolve from `src/lib/`. The module resolver rewrites `std` → `lib` internally. Prefer `use std.X` in new code.

**Detailed Structure:** See [`doc/04_architecture/file_class_structure.md`](doc/04_architecture/file_class_structure.md) for comprehensive codebase inventory (2,649 files, 623K lines, duplication analysis, refactoring recommendations).

**Glossary:** See [`doc/04_architecture/glossary.md`](doc/04_architecture/glossary.md) for key concepts (Crate, Virtual Crate, Linker Wrapper, SMF, Bootstrap, Frontend sharing).

---

## Auto-Generated Docs

Updated automatically:

| What | Where | When |
|------|-------|------|
| Features | `doc/06_spec/generated/feature.md` | Every test run |
| Pending | `doc/06_spec/generated/pending_feature.md` | Every test run |
| Test results | `doc/08_tracking/test/test_result.md` | Every test run |
| Build status | `doc/08_tracking/build/recent_build.md` | Every build |
| TODOs | `doc/TODO.md` | `bin/simple todo-scan` |
| Bugs | `doc/08_tracking/bug/bug_report.md` | `bin/simple bug-gen` |

---

## SFFI (Simple FFI)

**Runtime pattern**: `extern fn rt_*` -> `fn wrapper()`
**External library pattern**: C++/Rust FFI -> `extern fn` -> Simple API

```simple
extern fn rt_file_read_text(path: text) -> text
fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

Main module: `src/lib/ffi/mod.spl`. See `/sffi` skill.

---

## Runtime Limitations (CRITICAL)

See code agent for full list. Key issues:
- **Error handling:** Use `Result<T, E>` + `?` operator (no try/catch/throw keywords — by design)
- **Multi-line booleans** - wrap in parentheses: `if (a and\n   b):` works
- **Nested closure capture** - can READ outer vars, CANNOT MODIFY (module closures work fine)
- **Chained methods broken** - use intermediate `var`
- **NO inheritance** - `class Child(Parent)` is NOT supported (by design — use composition, alias forwarding, traits, mixins)
- **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`
