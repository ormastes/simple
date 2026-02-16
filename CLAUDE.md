# Simple Language Compiler - Development Guide

**Also available as:** [AGENTS.md](AGENTS.md) (redirect to this file)

Impl in simple unless it has big performance differences.

**100% Pure Simple** - No Rust source. Pre-built runtime at `bin/release/simple` (33MB).

---

## Agents (Task Tool)

Use these agent definitions when spawning Task subagents. Located in `.claude/agents/`.

| Agent | Use When | Key Skills |
|-------|----------|------------|
| **code** | Writing/editing Simple code, implementing features | `/coding`, `/design`, `/sffi` |
| **test** | Writing tests, fixing test failures, analyzing results | `/test`, `/sspec` |
| **debug** | Investigating bugs, tracing errors, profiling | `/debug` |
| **explore** | Finding files, understanding structure, researching | `/research`, `/architecture` |
| **docs** | Writing research/design/guide docs, reports | `/doc`, `/todo` |
| **vcs** | Committing, pushing, viewing history (jj) | `/versioning` |
| **infra** | MCP servers, database library, stdlib, SFFI | `/mcp`, `/database`, `/stdlib`, `/sffi` |
| **build** | Building project, creating releases | `/release` |
| **ml** | Machine learning features, neural networks | `/deeplearning` |

**Usage pattern:** When spawning a Task, include the relevant agent context:
```
Read .claude/agents/code.md and use its rules to implement <feature>
```

---

## Skills Reference

Invoke with `/skill-name` for detailed guidance. Located in `.claude/skills/`.

| Skill | Purpose |
|-------|---------|
| `versioning` | Jujutsu (jj) workflow - **NOT git!** |
| `test` | Test writing and methodology |
| `sspec` | SSpec BDD framework - matchers, hooks, structure |
| `coding` | Simple language rules, coding standards |
| `design` | Design patterns, type system |
| `architecture` | Compiler pipeline, module structure |
| `research` | Codebase exploration techniques |
| `debug` | Debugging, tracing, fault detection |
| `stdlib` | Stdlib module development |
| `todo` | TODO/FIXME comment format |
| `doc` | Documentation writing workflow |
| `deeplearning` | ML pipeline operators, dimension checking |
| `sffi` | FFI wrapper patterns (two/three-tier) |
| `database` | BugDB, TestDB, FeatureDB, query builder |
| `mcp` | MCP server implementation |
| `release` | Release process and versioning |

**Full Syntax Reference:** `doc/guide/syntax_quick_reference.md`
**SSpec Template:** `.claude/templates/sspec_template.spl`

---

## Critical Rules

### Version Control
- **NEVER use git** - use `jj` (see `/versioning` or vcs agent)
- **NEVER create branches** - work directly on `main`
- Push: `jj bookmark set main -r @ && jj git push --bookmark main`

### Language
- **ALL code in `.spl` or `.ssh`** - No Python, no Bash (except 3 bootstrap scripts in `scripts/`)
- **Scripts:** Use `.ssh` for shell scripts that need to remain shell (e.g., container entrypoints)
- **Generics:** `<>` not `[]` - `Option<T>`, `List<Int>`
- **Pattern binding:** `if val` not `if let`
- **Constructors:** `Point(x: 3, y: 4)` not `.new()`
- **`?` is operator only** - never in names. Use `.?` over `is_*` predicates
- **SDN format** for all config/data files, not JSON/YAML

### Tests
- **NEVER skip/ignore** failing tests without user approval
- **Built-in matchers only:** `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`
- **Interpreter mode limitation:** Test runner only verifies file loading, NOT `it` block execution
- **Live API tests:** `test/system/llm_caret_live_comprehensive_spec.spl` requires `CLAUDECODE=` env var
- **Test costs:** Live LLM tests cost ~$1-2 per run, use sparingly

### Code Style
- **NEVER over-engineer** - only make requested changes
- **NEVER add unused code** - delete completely
- **DO NOT ADD REPORT TO JJ** unless requested

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

# Container Testing (isolated, reproducible)
docker build -t simple-test-isolation:latest -f tools/docker/Dockerfile.test-isolation .
docker run --rm -v $(pwd):/workspace:ro --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test                   # All tests in container
docker run --rm -v $(pwd):/workspace:ro --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/unit/        # Unit tests only

# Docker Compose (easiest for local development)
docker-compose -f config/docker-compose.yml up unit-tests         # Unit tests
docker-compose -f config/docker-compose.yml up integration-tests  # Integration tests
docker-compose -f config/docker-compose.yml up system-tests       # System tests
docker-compose -f config/docker-compose.yml up all-tests          # All tests parallel
docker-compose -f config/docker-compose.yml run dev-shell         # Interactive shell

# Helper Scripts
scripts/local-container-test.sh unit        # Unit tests in container
scripts/local-container-test.sh quick path/to/spec.spl  # Single test
scripts/local-container-test.sh shell       # Interactive debugging
scripts/ci-test.sh                          # CI-style execution

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
[for x in 0..10 if x % 2 == 0: x]   # Comprehension
```

**Operators:** `|>` pipe, `>>` compose, `~>` layer connect, `**` power, `m{ x^2 }` math blocks

See `doc/guide/syntax_quick_reference.md` for complete reference.

---

## Project Structure

```
src/
  app/          # Applications (cli, build, mcp, mcp_jj, io, test_runner_new, desugar)
  lib/          # Libraries (database)
  std/          # Standard library (spec, text, math, path, array, platform)
  core/         # Core Simple library (tokens, types, ast, mir, lexer, parser)
  compiler/     # Compiler source (seed, native)
test/           # Test files (std, lib, app, compiler, benchmarks)
doc/            # Documentation (report, design, guide, research, feature, test, bug)
bin/            # Binaries (simple, release/simple)
tools/          # Development tools (seed bootstrap compiler, docker containers)
scripts/        # Bootstrap bash scripts (3 only)
.claude/        # Agents, skills, templates
```

**Detailed Structure:** See [`doc/architecture/file_class_structure.md`](doc/architecture/file_class_structure.md) for comprehensive codebase inventory (2,649 files, 623K lines, duplication analysis, refactoring recommendations).

---

## Auto-Generated Docs

Updated automatically:

| What | Where | When |
|------|-------|------|
| Features | `doc/feature/feature.md` | Every test run |
| Pending | `doc/feature/pending_feature.md` | Every test run |
| Test results | `doc/test/test_result.md` | Every test run |
| Build status | `doc/build/recent_build.md` | Every build |
| TODOs | `doc/TODO.md` | `bin/simple todo-scan` |
| Bugs | `doc/bug/bug_report.md` | `bin/simple bug-gen` |

---

## SFFI (Simple FFI)

**Two-Tier** (Runtime): `extern fn rt_*` -> `fn wrapper()`
**Three-Tier** (External): C++/Rust FFI -> `extern fn` -> Simple API

```simple
extern fn rt_file_read_text(path: text) -> text
fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

Main module: `src/app/io/mod.spl`. See `/sffi` skill.

---

## Runtime Limitations (CRITICAL)

See MEMORY.md and code agent for full list. Key issues:
- **NO try/catch/throw** - use Option pattern (`var error = nil`)
- **NO generics at runtime** - `<>` syntax fails in interpreter
- **Multi-line booleans** - wrap in parentheses: `if (a and\n   b):` works
- **Nested closure capture** - can READ outer vars, CANNOT MODIFY (module closures work fine)
- **Chained methods broken** - use intermediate `var`
- **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`

---

## Container Testing Troubleshooting

### Quick Fixes

**Container not found:** `docker build -t simple-test-isolation:latest -f tools/docker/Dockerfile.test-isolation .`
**Permission denied:** `chmod +x bin/release/simple` or `sudo usermod -aG docker $USER && newgrp docker`
**Out of memory:** Increase `--memory=512m` to `--memory=1g` or `--memory=2g`
**Timeout errors:** Use correct profile: `--profile=slow` (10 min) or `--profile=intensive` (30 min)
**Tests pass locally, fail in CI:** Run exact CI command: `scripts/ci-test.sh test/unit/`

### Common Issues

1. **Volume mount not working (Windows):**
   - PowerShell: `docker run -v ${PWD}:/workspace:ro ...`
   - CMD: `docker run -v %cd%:/workspace:ro ...`

2. **Container build fails:**
   - Check runtime exists: `ls -lh bin/release/simple` (should be ~33MB)
   - If missing: `scripts/install.sh` or download from releases

3. **jq not installed (parse errors):**
   - Ubuntu: `sudo apt install jq`
   - macOS: `brew install jq`

4. **Docker daemon not running:**
   - Linux: `sudo systemctl start docker`
   - macOS/Windows: Start Docker Desktop

### Docker Compose Quick Reference

```bash
# Run specific test tier
docker-compose -f config/docker-compose.yml up unit-tests
docker-compose -f config/docker-compose.yml up integration-tests
docker-compose -f config/docker-compose.yml up system-tests

# Interactive debugging
docker-compose -f config/docker-compose.yml run dev-shell
# Inside: simple test test/unit/failing_spec.spl --verbose

# Rebuild after Dockerfile changes
docker-compose build --no-cache

# Clean up
docker-compose down
docker system prune -a  # Remove all containers/images
```

### See Also

- **Full Guide:** `doc/guide/container_testing.md`
- **Resource Limits:** `doc/guide/resource_limits.md`
- **Test Config:** `simple.test.sdn`
