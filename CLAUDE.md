# Simple Language Compiler - Development Guide

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
- **ALL code in `.spl`** - No Python, no Bash (except 3 bootstrap scripts in `script/`)
- **Generics:** `<>` not `[]` - `Option<T>`, `List<Int>`
- **Pattern binding:** `if val` not `if let`
- **Constructors:** `Point(x: 3, y: 4)` not `.new()`
- **`?` is operator only** - never in names. Use `.?` over `is_*` predicates
- **SDN format** for all config/data files, not JSON/YAML

### Tests
- **NEVER skip/ignore** failing tests without user approval
- **Built-in matchers only:** `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`

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

# Quality
bin/simple build lint               # Linter
bin/simple build fmt                # Formatter
bin/simple build check              # All checks

# Tools
bin/simple fix file.spl --dry-run   # Preview fixes
bin/simple todo-scan                # Update TODO tracking
bin/simple bug-add --id=X           # Add bug
bin/simple bug-gen                  # Generate bug report
```

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
  std/          # Standard library (spec, string, math, path, array, platform)
  core/         # Core Simple library (tokens, types, ast, mir, lexer, parser)
  compiler/     # Compiler source (seed, native)
test/           # Test files (std, lib, app, compiler)
doc/            # Documentation (report, design, guide, research, feature, test, bug)
bin/            # Binaries (simple, release/simple)
seed/           # C/C++ seed compiler sources (seed.c, runtime.c/h, startup CRT)
script/         # Bootstrap bash scripts (3 only)
.claude/        # Agents, skills, templates
```

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
- **NO multi-line booleans** - use intermediate variables
- **Closure capture broken** - can READ outer vars, CANNOT MODIFY
- **Module closures broken** - imported fns can't access module state
- **Chained methods broken** - use intermediate `var`
- **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`
