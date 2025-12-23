# Simple Language Features

**Last Updated:** 2025-12-23
**Recent Update:** Completed Missing Language Features & Formatting/Lint (See [MISSING_FEATURES_COMPLETE.md](../report/MISSING_FEATURES_COMPLETE.md))

## Feature Table Format

All feature tables use this standardized 8-column format:

```markdown
| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #NNN | Name | 3 | ✅/📋 | R/S/S+R | [doc](path) | `path/` | `path/` |
```

**Column Reference:**

| Column | Description | Example Values |
|--------|-------------|----------------|
| **Feature ID** | Unique identifier (`#NNN`) | `#100`, `#700` |
| **Feature** | Short feature name | `TCP sockets`, `PostgreSQL driver` |
| **Difficulty** | Implementation complexity (1-5) | `1` Trivial, `2` Easy, `3` Medium, `4` Hard, `5` Very Hard |
| **Status** | `✅` Complete, `📋` Planned | |
| **Impl** | Implementation: `R` Rust, `S` Simple, `S+R` Both | |
| **Doc** | Link to spec/design doc, or `-` | `[spec/types.md](spec/types.md)` |
| **S-Test** | Simple test path, or `-` | `std_lib/test/unit/net/` |
| **R-Test** | Rust test path, or `-` | `src/runtime/tests/` |

---

## Feature ID Ranges

| Range | Category | Status |
|-------|----------|--------|
| #1-#9 | Infrastructure (Lexer, Parser, AST, HIR, MIR, GC, Pkg, SMF) | ✅ Complete |
| #10-#24 | Core Language (Types, Functions, Structs, Actors, Async) | ✅ Complete |
| #25-#29 | Memory & Pointers | ✅ Complete |
| #30-#49 | Type Inference, Associated Types, Effects | ✅ Complete |
| #50-#56 | Union Types | ✅ Complete |
| #60-#66 | Async State Machine | ✅ Complete |
| #70-#74 | Interpreter Enhancements | ✅ Complete |
| #95-#103 | Codegen (Outlining, Generators, LLVM) | ✅ Complete |
| #110-#157 | Concurrency (Channels, Generators, Executor, Actors, Futures) | ✅ Complete |
| #160-#172 | Pattern Matching | ✅ Complete |
| #180-#197 | Testing - BDD & Doctest | ✅ Complete |
| #200-#217 | Unit Types | ✅ Complete |
| #220-#225 | Networking | ✅ Complete |
| #230-#241 | Mock Library | ✅ Complete |
| #250-#258 | CLI Features | ✅ Complete |
| #300-#311 | GPU/SIMD | ✅ Complete |
| #400-#406 | Contracts | ✅ Complete |
| #510-#519 | UI Framework | ✅ Complete |
| #520-#536 | Web Framework | ✅ Complete (17/17) |
| #600-#610 | SDN + Gherkin DSL | ✅ Complete (11/11) |
| #700-#713 | Database & Persistence (DB + SQP) | ✅ Complete (14/14) |
| #800-#824 | Build & Linker Optimization | ✅ Complete (25/25) |
| #825-#849 | Infrastructure & Dependencies | ✅ Complete |
| #850-#879 | Simple Stdlib - Infra APIs | ✅ Complete (30/30) |
| #880-#919 | LLM-Friendly Features | 📋 Planned |
| #920-#935 | Test Coverage Infrastructure | ✅ Complete |
| #936-#945 | Architecture Test Library | ✅ Complete |
| #950-#970 | Formal Verification | ✅ Complete |
| #980-#999 | Code Quality & Documentation | ✅ Complete |
| #1000-#1050 | AOP & Unified Predicates | 🔄 In Progress (45/51, 88%) |
| #1051-#1060 | SDN Self-Hosting | ✅ Complete → [feature_done_9.md](feature_done_9.md) |
| #1061-#1103 | Missing Language Features | ✅ Complete → [feature_done_9.md](feature_done_9.md) |
| #1104-#1115 | Concurrency Modes | ✅ Complete (12/12) |
| #1116-#1130 | FFI/ABI Interface | ✅ Complete |
| #1131-#1145 | Formatting & Lints | ✅ Complete → [feature_done_9.md](feature_done_9.md) |
| #1146-#1155 | Trait Coherence | ✅ Complete → [feature_done_9.md](feature_done_9.md) |
| #1156-#1179 | Tree-sitter Implementation | 📋 Planned |
| #1180-#1199 | Multi-Language Tooling | 📋 Planned |
| #1200-#1209 | Language Model Server | 📋 Planned |
| #1210-#1299 | MCP (Minimal Code Preview) | 📋 Planned |
| #1300-#1324 | Metaprogramming (Macros, DSL, Decorators) | ✅ Complete (25/25) |
| #1325-#1329 | Pattern Matching Safety | ✅ Complete (5/5) |
| #1330-#1342 | Type System (Unions, Bitfields, HTTP) | ✅ Complete (13/13) |
| #1343-#1347 | Gherkin/BDD Extensions | ✅ Complete (5/5) |
| #1348-#1358 | MCP Protocol Core Features | 📋 Planned |
| #1359-#1368 | Developer Tools (LSP, DAP) | 📋 Planned |
| #1369-#1378 | UI Frameworks (TUI, GUI) | 📋 Planned |
| #1379-#1387 | Language Features (Context Managers, Primitives) | ✅ Complete (9/9) |
| #1388-#1390 | Shared Infrastructure | ✅ Complete (3/3) |
| #1391-#1395 | Advanced Contract Features | 📋 Planned |
| #1396-#1403 | Mock Library Fluent API | ✅ Complete (8/8) |

---

## Summary Statistics

**Overall Progress:** 56% (363/647 active features complete, 81 archived in feature_done_9.md)

**Recent Completions (2025-12-23):**
All recently completed features have been archived to [feature_done_9.md](feature_done_9.md):
- ✅ **Pattern Matching Safety (#1325-1329)** - 5/5 features, 750+ lines, 18 tests (JUST COMPLETED)
- ✅ SDN Self-Hosting (#1051-1060) - 8,690 lines, 204+ tests
- ✅ Missing Language Features (#1061-1103) - 43 features
- ✅ Formatting & Lints (#1131-1145) - 15 features
- ✅ Trait Coherence (#1146-1155) - 10 features, production ready
- ✅ **Metaprogramming (#1300-1324)** - 25/25 features, 100% complete! 🎉
  - **#1304**: One-pass LL(1) macro compilation (488 lines, 12 tests)
- ✅ Mock Library Fluent API (#1396-1403) - 8 features, 700+ lines, 19 tests (12 unit + 7 examples)
- ✅ **Type System Enhancements (#1330-1342)** - 13 features, 1,100+ lines, 39 tests (COMPLETE)

| Category | Total | Complete | Planned |
|----------|-------|----------|---------|
| Core Language | 47 | 47 | 0 |
| Codegen | 5 | 5 | 0 |
| Testing & CLI | 4 | 4 | 0 |
| Concurrency Runtime | 4 | 4 | 0 |
| Contracts | 6 | 6 | 0 |
| Extended - Units | 16 | 16 | 0 |
| Extended - Networking | 6 | 6 | 0 |
| Advanced - Effects | 6 | 6 | 0 |
| Advanced - UI | 3 | 3 | 0 |
| Advanced - GPU/SIMD | 19 | 19 | 0 |
| **SDN + Gherkin DSL** | 11 | 11 | 0 |
| **Database & Persistence** | 14 | 14 | 0 |
| **Web Framework** | 17 | 17 | 0 |
| **Build & Linker Optimization** | 25 | 25 | 0 |
| **Infrastructure & Dependencies** | 25 | 25 | 0 |
| **Simple Stdlib - Infra APIs** | 30 | 30 | 0 |
| **LLM-Friendly Features** | 40 | 0 | 40 |
| **Test Coverage Infrastructure** | 16 | 16 | 0 |
| **Architecture Test Library** | 10 | 10 | 0 |
| **Module Privacy** | 2 | 2 | 0 |
| **AOP & Unified Predicates** | 51 | 25 | 26 |
| **Concurrency Modes** | 12 | 12 | 0 |
| **FFI/ABI Interface** | 15 | 15 | 0 |
| **Tree-sitter Implementation** | 24 | 0 | 24 |
| **Multi-Language Tooling** | 20 | 0 | 20 |
| **Language Model Server** | 10 | 0 | 10 |
| **MCP (Minimal Code Preview)** | 90 | 0 | 90 |
| **Metaprogramming** | 25 | 25 | 0 |
| **Pattern Matching Safety** | 5 | 5 | 0 |
| **Type System Enhancements** | 13 | 13 | 0 |
| **Gherkin/BDD Extensions** | 5 | 5 | 0 |
| **MCP Protocol Core** | 11 | 0 | 11 |
| **Developer Tools** | 10 | 0 | 10 |
| **UI Frameworks** | 10 | 0 | 10 |
| **Language Features (Misc)** | 9 | 9 | 0 |
| **Shared Infrastructure** | 3 | 3 | 0 |
| **Advanced Contracts** | 5 | 0 | 5 |
| **Mock Library Fluent API** | 8 | 8 | 0 |

**Notes:**
- See `simple/bug_report.md` for details on blocking issues
- Completed categories moved to feature_done_*.md files (see "Completed Features" section above)

**Test Status:** 1,500+ tests passing (100% pass rate across all crates)

**Completed Features:** See [feature_done_1.md](feature_done_1.md), [feature_done_2.md](feature_done_2.md), [feature_done_3.md](feature_done_3.md), [feature_done_4.md](feature_done_4.md), [feature_done_5.md](feature_done_5.md), [feature_done_6.md](feature_done_6.md), [feature_done_7.md](feature_done_7.md), [feature_done_8.md](feature_done_8.md), [feature_done_9.md](feature_done_9.md)

---

## Planned Features

### LLM-Friendly Features (#880-919) 📋

Features to make Simple optimized for LLM-assisted development, verification, and collaboration.

**Documentation:**
- [llm_friendly.md](./llm_friendly.md) - LLM Quality Contract
- [plans/llm_friendly.md](./plans/llm_friendly.md) - Implementation Plan

#### Capability-Based Effects (#880-884)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #880 | `module requires[cap]` | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #881 | `@pure` / `@io` / `@net` | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #882 | Capability propagation | 4 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #883 | Forbidden effect errors | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #884 | Stdlib effect annotations | 2 | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/effects/` | - |

**Example:**
```simple
module app.domain requires[pure]:
    # Only pure functions - no I/O allowed
    use core.math.*     # OK
    use io.fs.*         # ERROR: fs capability not declared

@io @net
fn fetch_and_save(url: str, path: str):
    let data = http.get(url)?   # Requires @net
    fs.write(path, data)?       # Requires @io
```

#### AST/IR Export (#885-889)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #885 | `--emit-ast` | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #886 | `--emit-hir` | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #887 | `--emit-mir` | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #888 | `--error-format=json` | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #889 | Semantic diff tool | 4 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Example:**
```bash
simple compile app.spl --emit-ast > ast.json
simple compile app.spl --error-format=json 2> errors.json
simple diff --semantic old.spl new.spl
```

#### Context Pack Generator (#890-893)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #890 | `simple context` command | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #891 | Dependency symbol extraction | 4 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #892 | Markdown context format | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #893 | JSON context format | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Example:**
```bash
# Extract minimal context (only symbols used by app.service)
simple context app.service --format=markdown > context.md
simple context app.service --format=json > context.json
```

**Impact:** 90% reduction in LLM context tokens

#### Property-Based Testing (#894-898)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #894 | `@property_test` decorator | 3 | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | `src/compiler/tests/` |
| #895 | Input generators | 3 | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |
| #896 | Shrinking on failure | 4 | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | `src/runtime/tests/` |
| #897 | Configurable iterations | 2 | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |
| #898 | Generator combinators | 3 | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |

**Example:**
```simple
use testing.property.*

@property_test(iterations: 1000)
fn test_sort_idempotent(input: [i64]):
    expect(sort(sort(input))).to_equal(sort(input))

@property_test
fn test_reverse_reverse(input: [i64]):
    expect(reverse(reverse(input))).to_equal(input)
```

#### Snapshot/Golden Tests (#899-902)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #899 | `@snapshot_test` decorator | 3 | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/snapshot/` | `src/compiler/tests/` |
| #900 | Snapshot storage | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #901 | `--snapshot-update` flag | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #902 | Multi-format snapshots | 3 | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/snapshot/` | `src/driver/tests/` |

**Example:**
```simple
@snapshot_test
fn test_render_user_json():
    let user = User(id: 42, name: "Alice")
    let json = render_json(user)
    expect_snapshot(json, format: "json")
```

#### Lint Framework (#903-907)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #903 | Lint rule trait | 3 | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/lint/` | - |
| #904 | Built-in rules | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #905 | Configurable severity | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #906 | `simple lint` command | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #907 | Auto-fix suggestions | 4 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Configuration (`simple.toml`):**
```toml
[lint]
unchecked_indexing = "deny"
global_mutable_state = "deny"
magic_numbers = "warn"

[lint.rules]
max_function_length = 50
max_nesting_depth = 4
```

#### Canonical Formatter (#908-910)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #908 | `simple fmt` command | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #909 | Single correct style | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/parser/tests/` |
| #910 | Format-on-save integration | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |

**Impact:** Eliminates stylistic variance; LLM output is predictable

#### Build & Audit Infrastructure (#911-915)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #911 | Deterministic build mode | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #912 | Replay logs | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #913 | `@generated_by` provenance | 2 | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/audit/` | `src/compiler/tests/` |
| #914 | API surface lock file | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #915 | Spec coverage metric | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |

**Example:**
```simple
# Auto-generated provenance annotation
@generated_by(tool: "claude", prompt_hash: "abc123", version: "3.5")
fn calculate_tax(amount: i64) -> i64:
    ...
```

#### Sandboxed Execution (#916-919)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #916 | Resource limits | 3 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #917 | Network isolation | 4 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #918 | Filesystem isolation | 4 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #919 | `simple run --sandbox` | 2 | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Impact:** Safely verify LLM-generated code without risk

**Projected Benefits:**
- LLM error rate: <5% contract violations
- Context size: 90% reduction with context packs
- Edge case coverage: 80%+ with property tests
- Reproducibility: 100% deterministic builds

---

### AOP & Unified Predicates (#1000-1049) 📋

Unified predicate grammar for AOP weaving, hybrid DI, mocking, and architecture rules.

**Documentation:**
- [research/aop.md](../research/aop.md) - Full AOP specification

**Relationship to Existing Features:**
- **Mock Library (#230-241)**: Existing fluent mock API for unit tests. AOP mocking (#1021-1025) adds trait-boundary mocking via DI predicates - both coexist.
- **Architecture Test (#936-945)**: Existing Rust-based arch validation. AOP arch rules (#1035-1041) adds in-source `forbid`/`allow` rules with unified predicates.

#### Phase 1: Predicate Grammar (#1000-1005)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1000 | `pc{...}` syntactic island (lexer mode) | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1001 | Predicate operators (!, &, \|, grouping) | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1002 | Pattern wildcards (*, **, prefix*, *suffix) | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1003 | Signature pattern `ret_pat qname_pat(arg_pats)` | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1004 | `..` argument wildcard | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1005 | Allowed introducer validation (`on`, `bind on`, `forbid`, `allow`) | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |

**Grammar (EBNF):**
```
expr        ::= or_expr
or_expr     ::= and_expr ( '|' and_expr )*
and_expr    ::= not_expr ( '&' not_expr )*
not_expr    ::= '!' not_expr | primary
primary     ::= selector | '(' expr ')'
selector    ::= name '(' args? ')'
pattern     ::= seg ('.' seg)*
seg         ::= IDENT | '*' | '**' | IDENT '*' | '*' IDENT
signature   ::= ret_pat ' ' qname_pat '(' arg_pats ')'
```

#### Phase 2: Context Validation (#1006-1008)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1006 | Weaving selector set (execution/within/attr/effect/test/decision/condition) | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1007 | DI/Mock selector set (type/within/attr only) | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1008 | Illegal selector in context diagnostic | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Selector Sets by Context:**
```
+------------------------------------------------------------------+
| Context      | Allowed Selectors                                  |
+------------------------------------------------------------------+
| Weaving      | execution, within, attr, effect, test, decision,  |
|              | condition, call (link-time), init (runtime)        |
| DI/Mock      | type, within, attr                                 |
| Architecture | import, depend, use, export, config, within, attr  |
+------------------------------------------------------------------+
```

#### Phase 3: Hybrid DI (#1009-1016)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1009 | Typed dependency graph (compiler-built) | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1010 | SDN `di:` section with profiles | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/sdn/tests/` |
| #1011 | `bind on pc{...} -> Impl scope priority` syntax | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1012 | `@sys.inject` constructor injection | 3 | 📋 | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/di/` | `src/compiler/tests/` |
| #1013 | Per-parameter `@sys.inject` | 3 | 📋 | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/di/` | `src/compiler/tests/` |
| #1014 | Priority/specificity/stable-order resolution | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1015 | Ambiguous binding diagnostic | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1016 | Release profile freeze (direct wiring) | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**SDN Schema:**
```sdn
di:
  mode: hybrid
  profiles:
    production:
      - bind on pc{ type(UserRepository) } -> SqlUserRepository scope Singleton priority 10
    test:
      - bind on pc{ type(Clock) } -> ClockMock scope Singleton priority 100
```

**Specificity Scoring:**
```
literal segment:     +2
prefix/suffix (*):   +1
single wildcard:      0
multi-segment (**): -2
negation (!):        -1
```

#### Phase 4: Constructor Injection (#1017-1019)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1017 | All-params-injectable rule for constructor `@sys.inject` | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1018 | Parameter-level diagnostic for unresolvable deps | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1019 | No mixing constructor vs per-param injection | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Example:**
```simple
class OrderService:
    repo: OrderRepository
    clock: Clock

    @sys.inject
    fn new(repo: OrderRepository, clock: Clock) -> Self:
        return Self { repo: repo, clock: clock }
```

#### Phase 5: AOP Mocking (#1020-1025)

**Note:** Complements existing Mock Library (#230-241). AOP mocking uses trait-boundary + DI binding selection.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1020 | `mock Name implements Trait:` syntax | 3 | 📋 | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/mock/` | `src/parser/tests/` |
| #1021 | `expect method() -> Type:` syntax | 2 | 📋 | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/mock/` | `src/parser/tests/` |
| #1022 | `@sys.test_only` decorator enforcement | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1023 | Mock binding via DI predicates (test profile) | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1024 | Illegal mock in non-test diagnostic | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1025 | Illegal Mock* binding outside test profile | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Example:**
```simple
@sys.test_only
mock ClockMock implements Clock:
    expect now() -> Time:
        return Time.from_unix(0)

# SDN binding
profiles:
  test:
    - bind on pc{ type(Clock) } -> ClockMock scope Singleton priority 100
```

**Safety Rules:**
- `mock` keyword illegal outside `test/` directory
- `Mock*` bindings illegal outside test profile

#### Phase 6: Architecture Rules (#1026-1033)

**Note:** Extends existing Architecture Test Library (#936-945) with in-source predicates.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1026 | `arch_rules:` block syntax | 2 | 📋 | S+R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1027 | `forbid pc{...}` rule | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1028 | `allow pc{...}` rule | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1029 | `import(from_pattern, to_pattern)` selector | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1030 | `depend(from_pattern, to_pattern)` selector | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1031 | `use(pattern)` selector | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1032 | `export(pattern)` selector | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1033 | `config(STRING)` selector | 2 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**SDN Validation Hooks:**
| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1034 | Release build MUST NOT select test profile | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1035 | Release MUST NOT enable runtime interceptors | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Example:**
```simple
arch_rules:
    forbid pc{ import(within(domain.**), within(infrastructure.**)) }
    forbid pc{ depend(within(domain.**), within(infrastructure.**)) }
    forbid pc{ use(Container) & within(domain.**) }
    forbid pc{ config("profiles.test") & attr(release) }
```

#### Phase 7: Compile-Time Weaving (#1036-1042)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1036 | `execution(signature)` join point | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1037 | `within(pattern)` join point | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1038 | `attr(IDENT)` join point | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1039 | `effect(effect_set)` join point | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1040 | `test(IDENT)` join point | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1041 | `decision()`/`condition()` join points (coverage) | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1042 | Zero-overhead when aspects.enabled = [] | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Advice Forms:**
| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1043 | `before` advice | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1044 | `after_success` advice | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1045 | `after_error` advice | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1046 | Advice priority ordering | 3 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Ordering:** Higher priority → earlier for `before`, later for `after_*`, outermost for `around`.

#### Phase 8: Link-Time & Runtime Backends (Optional) (#1047-1050)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1047 | `call(signature)` link-time selector | 4 | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Backend Comparison:**
```
+------------------------------------------------------------------+
| Backend      | Selectors                 | around | Optimization  |
+------------------------------------------------------------------+
| Compile-time | execution, within, attr,  | No     | Best          |
|              | effect, test, decision,   |        |               |
|              | condition                 |        |               |
| Link-time    | + call(signature)         | No     | Good          |
| Runtime/DI   | + init(pattern)           | Yes    | Proxy overhead|
+------------------------------------------------------------------+
```

**Implementation Order (from doc):**
1. `pc{...}` lexical island and predicate parser (#1000-1005)
2. Context validation tables (#1006-1008)
3. Hybrid DI binding resolution (#1009-1016)
4. Constructor injection with `@sys.inject` (#1017-1019)
5. Mock lowering for `mock implements Trait` (#1020-1025)
6. Architecture rule engine + SDN validation (#1026-1035)
7. Compile-time weaving join points (#1036-1046)
8. Optional link-time and runtime backends (#1047-1050)

---

### Concurrency Modes (#1107-1118) 📋

Safety modes for concurrency: actor (Erlang-style), lock_base (Rust-style), unsafe.

**Documentation:**
- [spec/language_enhancement.md](../spec/language_enhancement.md) - Section 4: Concurrency Modes

#### Mode System (#1107-1110)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|

**Mode Comparison:**
```
+------------------------------------------------------------------+
| Mode       | Shared State | mut T | Mutex | Atomic | Data Races  |
+------------------------------------------------------------------+
| actor      | ❌ No        | ❌    | ❌    | ❌     | Impossible  |
| lock_base  | ✅ Yes       | ✅    | ✅    | ✅     | Runtime trap|
| unsafe     | ✅ Yes       | ✅    | ✅    | ✅     | Undefined   |
+------------------------------------------------------------------+
```

#### GC Support for Concurrent Collections (#1108-1112)

Native concurrent libraries with GC-managed objects. Uses crossbeam, dashmap, and mimalloc with GC write barriers.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|

**Implementation Notes:**
- Uses **dashmap** (Rust alternative to libcuckoo/libcds) for concurrent hash map
- Uses **crossbeam::queue::SegQueue** (Rust alternative to moodycamel) for concurrent queue
- Uses **parking_lot::Mutex** + Vec for concurrent stack (strict LIFO semantics)
- Uses **mimalloc** (already in workspace) for fast allocation
- All collections support GC write barriers via `TraceConcurrent` trait
- 15+ tests passing in `src/runtime/src/concurrent/`

**Example:**
```simple
#[concurrency_mode(lock_base)]
mod gc_concurrent

use infra.concurrent.ConcurrentMap

struct User:
    name: str
    age: i64

fn main():
    let users = ConcurrentMap[str, User].new()
    users.insert("alice", User(name: "Alice", age: 30))

    spawn \:
        let user = users.get("alice")
        print(user.name)  # GC keeps object alive across threads
```

#### Mode Enforcement (#1113-1115)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1114 | Compile error for `Mutex` in actor mode | 3 | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1115 | Warning for unsafe in release build | 2 | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |

---

### Tree-sitter Implementation (#1156-1179) 📋

Tree-sitter parser implementation **written in Simple language** (self-hosted prerequisite for MCP).

**Documentation:**
- [Tree-sitter Documentation](https://tree-sitter.github.io/tree-sitter/)
- Implementation: `simple/std_lib/src/treesitter/` (written in Simple)

**Why Tree-sitter First:**
- MCP needs robust multi-language parsing
- Tree-sitter provides incremental, error-tolerant parsing
- Self-hosting: Parser written in Simple language itself
- Enables multi-language tooling support

#### Tree-sitter Core (#1156-1165)

Core Tree-sitter runtime implemented in Simple.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1156 | Tree-sitter runtime core | 5 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1157 | Parser state machine | 5 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1158 | Lexer integration | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1159 | Parse tree construction | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1160 | Incremental parsing | 5 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1161 | Error recovery | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1162 | Tree query system | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1163 | Syntax highlighting queries | 3 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1164 | Tree-sitter CLI tools | 3 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1165 | Performance optimization | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |

#### Language Grammar Support (#1166-1179)

Tree-sitter grammars for multiple languages (all written in Simple).

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1166 | Simple/Basic language grammar | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1167 | Rust grammar | 5 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1168 | Python grammar | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1169 | Ruby grammar | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1170 | Erlang grammar | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1171 | JavaScript/TypeScript grammar | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1172 | Go grammar | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1173 | C/C++ grammar | 5 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1174 | Grammar compilation pipeline | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1175 | Grammar testing framework | 3 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1176 | Language detection | 3 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1177 | Multi-language workspace support | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1178 | Grammar hot-reload | 3 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |
| #1179 | External parser bindings | 4 | 📋 | S | [treesitter.md](../spec/treesitter.md) | `std_lib/test/treesitter/` | - |

**Example:**
```simple
# Tree-sitter implementation in Simple language
use treesitter.{Parser, Query, Language}

let parser = Parser.new()
parser.set_language(Language.rust())

let source = "fn main() { println!(\"Hello\"); }"
let tree = parser.parse(source)

# Query for function definitions
let query = Query.new("(function_item name: (identifier) @func)")
let matches = query.matches(tree)
```

**Implementation Location:**
- `simple/std_lib/src/treesitter/` - Core runtime (written in Simple)
- `simple/std_lib/src/treesitter/grammars/` - Language grammars

---

### Multi-Language Tooling (#1180-1199) 📋

Development tooling for multiple languages using Tree-sitter foundation.

**Documentation:**
- Builds on Tree-sitter (#1156-1179)
- Enables multi-language MCP support

#### Compiler & Build Tools (#1180-1185)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1180 | Multi-language compiler interface | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1181 | Incremental compilation support | 5 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1182 | Build system integration | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1183 | Dependency tracking | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1184 | Error aggregation across languages | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1185 | Watch mode & hot reload | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |

#### Testing Tools (#1186-1191)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1186 | Multi-language test runner | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1187 | Test discovery across languages | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1188 | Coverage reporting (multi-lang) | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1189 | Test result aggregation | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1190 | Parallel test execution | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1191 | Test filtering & selection | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |

#### Deployment Tools (#1192-1199)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1192 | Multi-language packaging | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1193 | Artifact bundling | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1194 | Deployment pipeline integration | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1195 | Container image generation | 4 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1196 | Binary stripping & optimization | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1197 | Release automation | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1198 | Version management | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |
| #1199 | Deploy configuration templates | 3 | 📋 | S | [tooling.md](../spec/tooling.md) | `std_lib/test/tooling/` | - |

**Example:**
```bash
# Compile multi-language project
simple build --watch

# Run tests across all languages
simple test --parallel

# Deploy with optimizations
simple deploy --target production --optimize
```

---

### Language Model Server (#1200-1209) 📋

Server infrastructure for handling MCP protocol requests and multi-language tooling integration.

**🎯 SELF-HOSTED: Language Server implemented in Simple language**

**Documentation:**
- [spec/basic_mcp.md](../spec/basic_mcp.md) - MCP Protocol Specification
- [plans/llm_friendly.md](../plans/llm_friendly.md) - Implementation Plan

**Key Features:**
- JSON-RPC transport layer for MCP protocol
- Session management and caching
- Multi-file workspace handling
- Incremental update support
- Authentication and authorization

**Prerequisites:**
- Tree-sitter implementation (#1156-1179) - Required for multi-language parsing
- Multi-language tooling (#1180-1199) - Required for compile/test/deploy

**Implementation:**
- Language: **Simple** (self-hosted)
- Location: `simple/std_lib/src/lms/`

#### Language Model Server Core (#1200-1209)

Core server infrastructure for handling MCP protocol requests.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1200 | Language model server protocol | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1201 | JSON-RPC transport layer | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1202 | Request/response handling | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1203 | Session management | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1204 | Error handling & diagnostics | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1205 | Caching layer for MCP views | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1206 | Incremental update support | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1207 | Multi-file workspace handling | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1208 | Authentication & authorization | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |
| #1209 | Server CLI (`simple lms start`) | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/lms/` | - |

**Example:**
```bash
# Start language model server
simple lms start --port 8080

# Server handles MCP protocol requests over JSON-RPC
```

---

### MCP (Minimal Code Preview) (#1210-1299) 📋

Minimal Code Preview protocol for LLM-optimized code understanding with collapsed outline format.

**🎯 SELF-HOSTED: MCP implementation in Simple language**

**Documentation:**
- [spec/basic_mcp.md](../spec/basic_mcp.md) - MCP Specification v1.0
- [guides/llm_friendly.md](../guides/llm_friendly.md) - LLM Quality Contract

**Key Benefits:**
- 90%+ token reduction via collapsed outline format
- Multi-language support (Simple, Rust, Python, Ruby, Erlang, etc.)
- Progressive disclosure (expand on demand)
- Virtual information (auto traits, AOP, coverage)
- Single JSON field format for minimal overhead
- Integrated compile/test/deploy tooling

**Prerequisites:**
- Language Model Server (#1200-1209) - Protocol transport layer
- Tree-sitter implementation (#1156-1179) - Multi-language parsing
- Multi-language tooling (#1180-1199) - Compile/test/deploy integration

**Implementation:**
- Language: **Simple** (self-hosted)
- Location: `simple/std_lib/src/mcp/`

#### MCP Core Features - Simple Language (#1210-1229)

Core MCP protocol implementation for Simple/Basic language folding.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1210 | Block-mark notation (`C>`, `F>`, `T>`, `P>`, `V•`) | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1211 | Collapsed outline generation | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1212 | Public API filtering | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1213 | `read_file(path, mode="mcp")` tool | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1214 | `expand_at(selector, what)` tool | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1215 | `goto_definition(symbol)` tool | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1216 | `search(query, filter)` tool | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1217 | Signature shrinking (params/return types) | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1218 | Body collapsing (`{ … }` inline) | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1219 | Class/struct member shrinking | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1220 | Virtual information extraction | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1221 | Auto trait detection (`Send`, `Sync`) | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1222 | AOP pointcut exposure | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1223 | JSON output format (single `text` field) | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1224 | Markdown document folding | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1225 | Log collapsing (INFO/WARN/ERROR counts) | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1226 | Diagnostic grouping | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1227 | `simple mcp <file>` CLI | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1228 | `--expand <symbol>` flag | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1229 | `--show-coverage` flag | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |

**Example:**
```bash
# Generate MCP outline
simple mcp app.spl
# Output: { "text": "C> pub class User { … }\nF> pub fn login { … }" }

# Expand specific symbol
simple mcp app.spl --expand UserService --what=all
```

#### MCP Multi-Language Support (#1230-1259)

MCP support for multiple programming languages using Tree-sitter.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1230 | Rust language MCP folding | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/rust/` | - |
| #1231 | Python language MCP folding | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/python/` | - |
| #1232 | Ruby language MCP folding | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/ruby/` | - |
| #1233 | Erlang language MCP folding | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/erlang/` | - |
| #1234 | JavaScript/TypeScript MCP folding | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/js/` | - |
| #1235 | Go language MCP folding | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/go/` | - |
| #1236 | C/C++ language MCP folding | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/c/` | - |
| #1237 | Language-specific virtual info | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1238 | Cross-language workspace | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1239 | Language auto-detection | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1240 | Multi-language search | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1241 | Language-specific folding rules | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1242 | Polyglot symbol resolution | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1243 | Foreign function interface folding | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1244 | Language interop visualization | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1245 | Custom language plugin system | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1246 | Language-specific diagnostics | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1247 | Multi-language coverage overlay | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1248 | Language conversion suggestions | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1249 | Polyglot refactoring tools | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1250 | Multi-language snippet extraction | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1251 | Language-specific context packs | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1252 | Polyglot documentation generation | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1253 | Cross-language dependency tracking | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1254 | Language benchmark comparisons | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1255 | Multi-language test correlation | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1256 | Polyglot profiling integration | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1257 | Language migration assistance | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1258 | Multi-language style enforcement | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1259 | Polyglot security scanning | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |

**Example:**
```bash
# MCP folding for Rust code
simple mcp main.rs --lang rust

# Multi-language workspace
simple mcp . --languages rust,python,simple

# Cross-language search
simple mcp --search "fn main" --languages all
```

#### MCP Tooling Integration (#1260-1279)

Integration with compile, test, and deploy tools.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1260 | `run_compile(target, flags)` tool | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1261 | `run_test(filter, parallel)` tool | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1262 | `run_deploy(target, config)` tool | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1263 | `read_task_log(task_id, group)` tool | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1264 | Task progress monitoring | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1265 | Build artifact inspection | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1266 | Test result visualization | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1267 | Deployment status tracking | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1268 | Error recovery & retry | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1269 | Pipeline configuration | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1270 | Incremental build support | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1271 | Test impact analysis | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1272 | Deployment rollback | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1273 | Build cache management | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1274 | Test parallelization | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1275 | Deployment health checks | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1276 | Build optimization suggestions | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1277 | Test coverage integration | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1278 | Deployment metrics | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1279 | CI/CD pipeline integration | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |

#### MCP Advanced Features (#1280-1299)

Advanced MCP features for optimization and extensibility.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1280 | Coverage overlay integration | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1281 | Block guide markers (`V• end`) | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1282 | Line number formatting (plain/zpad) | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1283 | Context pack integration | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1284 | Dependency symbol extraction | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1285 | Minimal context bundling | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1286 | Diff mode (changed symbols only) | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1287 | Blame integration (author/commit info) | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1288 | Cross-reference inlining (call sites) | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1289 | Binary protobuf format | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1290 | Streaming incremental MCP | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1291 | Semantic highlighting tokens | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1292 | MCP view caching & invalidation | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1293 | Workspace-wide symbol index | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1294 | Smart symbol filtering (relevance) | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1295 | MCP metadata customization | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1296 | Performance profiling for MCP | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1297 | Plugin architecture for MCP | 5 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1298 | MCP transformation pipeline | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1299 | Custom MCP output formats | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |

**Example:**
```bash
# Extract minimal context pack (90% token reduction)
simple context app.service --format=mcp > context.json

# Generate MCP with coverage
simple mcp app.spl --show-coverage

# Diff mode (changed symbols)
simple mcp app.spl --diff main..HEAD

# Multi-language compile + test + deploy
simple mcp --compile --test --deploy --languages rust,python
```

**MCP Summary:**
- Token reduction: 90%+ via collapsed outline format
- Block marks: `C>`, `F>`, `T>`, `P>`, `V•` for structure
- Format: Single JSON `text` field for LLM efficiency
- Disclosure: Progressive via tool calls (not inline hints)
- Virtual info: Auto traits, AOP, coverage overlay
- Languages: Simple, Rust, Python, Ruby, Erlang, Go, C/C++, JS/TS
- Tooling: Compile, test, deploy via MCP protocol

**Implementation Locations:**
- Language Server: `simple/std_lib/src/lms/` (self-hosted in Simple)
- MCP Core: `simple/std_lib/src/mcp/` (self-hosted in Simple)
- Tree-sitter: `simple/std_lib/src/treesitter/` (self-hosted in Simple)
- Multi-lang Tooling: `simple/std_lib/src/tooling/` (self-hosted in Simple)

**Related Features:**
- #1200-1209: Language Model Server (protocol transport)
- #1156-1179: Tree-sitter Implementation (parsing)
- #1180-1199: Multi-Language Tooling (compile/test/deploy)
- #890-893: Context Pack Generator (LLM-Friendly)
- #885-889: AST/IR Export (LLM-Friendly)

### Metaprogramming (#1300-1324) ✅

**Status:** 25/25 Complete (100%) - All features implemented! 🎉

**NOTE:** Features #1308-1324 are duplicates of #1069-1088 (completed Dec 2025). This range was created for organization but inadvertently duplicated existing feature IDs.

Advanced metaprogramming features including contract-first macros, DSL support, decorators, comprehensions, and pattern matching enhancements.

**Documentation:**
- [spec/macro.md](../spec/macro.md) - Contract-first macro specification
- [spec/metaprogramming.md](../spec/metaprogramming.md) - DSL, decorators, comprehensions

#### Contract-First Macros (#1300-1304) ✅

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1300 | `macro` keyword with contract syntax | 4 | ✅ | R | [macro.md](../spec/macro.md) | - | `src/parser/tests/` |
| #1301 | `const_eval:` and `emit:` blocks | 3 | ✅ | R | [macro.md](../spec/macro.md) | - | `src/compiler/tests/` |
| #1302 | Hygienic macro expansion | 5 | ✅ | R | [macro.md](../spec/macro.md) | - | `src/compiler/tests/` |
| #1303 | `intro`/`inject`/`returns` contract items | 4 | ✅ | R | [macro.md](../spec/macro.md) | - | `src/compiler/tests/` |
| #1304 | One-pass macro compilation (LL(1)) | 4 | ✅ | R | [macro.md](../spec/macro.md) | [one_pass_ll1_macros_status.md](../status/one_pass_ll1_macros_status.md) | `src/compiler/src/macro_validation.rs` |

**Description:** LL(1)-friendly macro system with compile-time symbol introduction. Macros declare effects in headers, enabling IDE autocomplete without expansion.

**Implementation Status:**
- ✅ Parser: Full macro syntax (`MacroDef`, contract items)
- ✅ Basic Expansion: Template substitution with `const_eval`/`emit`
- ✅ Hygienic Expansion: AST renaming via `MacroHygieneContext`
- ✅ Contract Processing: Complete infrastructure (390 lines, #1303)
- ✅ Integration: Wired into `expand_user_macro()` with thread-local registry (#1303)
- ✅ Symbol Registration: Optional auto-registration of introduced symbols
- ✅ **One-Pass Compilation**: Complete validation infrastructure (2025-12-23)
  - ✅ Ordering validation (macros defined before use) - E1402
  - ✅ Shadowing detection (intro symbols) - E1403
  - ✅ QIDENT template variable validation - E1406
  - ✅ Type annotation requirements - E1405
  - ✅ 12 unit tests passing

**Example:**
```simple
macro gen_axes(BASE: Str const, N: Int const) -> (
  intro axes:
    for i in 0..N:
      enclosing.class.fn "{BASE}{i}"(v: Vec[N]) -> Int
):
  emit axes:
    for i in 0..N:
      fn "{BASE}{i}"(v: Vec[N]) -> Int:
        return v[i]

class Vec3D:
  gen_axes!("axis", 3)  # Introduces: axis0(), axis1(), axis2()

  fn length(self) -> Float:
    self.axis0([1.0, 2.0, 3.0])  # ✅ IDE autocomplete works!
```

**Files:**
- `src/compiler/src/macro_validation.rs` (488 lines) - **NEW** Validation infrastructure
- `src/compiler/src/macro_contracts.rs` (390 lines) - Contract processing with shadowing detection
- `src/compiler/src/interpreter_macro.rs` - Pipeline integration
- `src/compiler/src/interpreter.rs` - Macro definition order tracking
- `src/compiler/src/error.rs` - E14xx error codes (E1401-E1406)
- `doc/report/MACRO_CONTRACTS_IMPLEMENTATION.md`
- `MACRO_CONTRACTS_COMPLETE.md`

#### DSL Support (#1305-1307)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1305 | `context obj:` block (implicit receiver) | 3 | ✅ | R+S | [metaprogramming.md](../spec/metaprogramming.md) | `simple/std_lib/src/core/dsl.spl` | `src/compiler/tests/context_blocks_test.rs` |
| #1306 | `method_missing` handler | 4 | ✅ | R+S | [metaprogramming.md](../spec/metaprogramming.md) | `simple/std_lib/src/core/dsl.spl` | `src/compiler/src/interpreter_context.rs` |
| #1307 | Fluent interface support | 2 | ✅ | S | [metaprogramming.md](../spec/metaprogramming.md) | `simple/std_lib/src/core/dsl.spl` | - |

**Example:**
```simple
context html:
    tag("h1", "Welcome")
    p "This is a DSL"
    div:
        span "Nested content"
```

#### Built-in Decorators (#1308-1311)

**Note:** Same as #1069-1072 (duplicate tracking)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1308 | `@cached` decorator (memoization) | 3 | ✅ | S | [metaprogramming.md](../spec/metaprogramming.md) | `simple/std_lib/src/core/decorators.spl` | Blocked† |
| #1309 | `@logged` decorator | 2 | ✅ | S | [metaprogramming.md](../spec/metaprogramming.md) | `simple/std_lib/src/core/decorators.spl` | Blocked† |
| #1310 | `@deprecated(message)` decorator | 2 | ✅ | S | [metaprogramming.md](../spec/metaprogramming.md) | `simple/std_lib/src/core/decorators.spl` | Blocked† |
| #1311 | `@timeout(seconds)` decorator | 3 | ✅ | S | [metaprogramming.md](../spec/metaprogramming.md) | `simple/std_lib/src/core/decorators.spl` | Blocked† |

**†** Tests blocked by BDD scoping bug (see `simple/bug_report.md`)

#### Comprehensions (#1312-1313)

**Note:** Same as #1078-1079 (duplicate tracking)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1312 | List comprehensions `[x*x for x in 0..10]` | 3 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1313 | Dict comprehensions `{x: x*x for x in 0..10}` | 3 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |

#### Enhanced Pattern Matching (#1314-1319)

**Note:** Same as #1085-1088 (duplicate tracking)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1314 | Match guards `case x if x > 0:` | 2 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1315 | Or patterns `case "quit" \| "exit":` | 2 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1316 | Range patterns `case 90..100: "A"` | 3 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1317 | `if let` syntax | 2 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1318 | `while let` syntax | 2 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1319 | Chained comparisons `if 0 < x < 10:` | 2 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |

#### Slicing & Spread (#1320-1324)

**Note:** Same as #1080-1082 (duplicate tracking)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1320 | Negative indexing `items[-1]` | 2 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/driver/tests/interpreter_collections.rs` |
| #1321 | Slice syntax `items[2:5]`, `items[::2]` | 3 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1322 | Tuple unpacking `let a, b = (1, 2)` | 2 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1323 | Rest patterns `let first, *rest = [1,2,3,4]` | 3 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1324 | Spread operators `[*a, *b]`, `{**d1, **d2}` | 3 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |

---

### Pattern Matching Safety (#1325-1329) ✅

Rust-level match safety guarantees for production-grade language.

**Status:** ✅ **COMPLETE** (5/5 features, 750+ lines, 18 tests)

**Documentation:**
- [PATTERN_MATCH_SAFETY.md](../../PATTERN_MATCH_SAFETY.md) - Complete implementation guide
- [spec/language_enhancement.md](../spec/language_enhancement.md) - Section 7

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1325 | Exhaustiveness checking (compile-time) | 4 | ✅ | R | [PATTERN_MATCH_SAFETY.md](../../PATTERN_MATCH_SAFETY.md) | `test_pattern_safety.spl` | `src/compiler/tests/` |
| #1326 | Unreachable arm detection | 3 | ✅ | R | [PATTERN_MATCH_SAFETY.md](../../PATTERN_MATCH_SAFETY.md) | `test_pattern_safety.spl` | `src/compiler/tests/` |
| #1327 | Tagged union support | 3 | ✅ | R | [PATTERN_MATCH_SAFETY.md](../../PATTERN_MATCH_SAFETY.md) | `test_pattern_safety.spl` | `src/compiler/tests/` |
| #1328 | Strong enum enforcement | 3 | ✅ | R | [PATTERN_MATCH_SAFETY.md](../../PATTERN_MATCH_SAFETY.md) | `test_pattern_safety.spl` | `src/compiler/tests/` |
| #1329 | Pattern subsumption analysis | 1 | ✅ | R | [PATTERN_MATCH_SAFETY.md](../../PATTERN_MATCH_SAFETY.md) | `test_pattern_safety.spl` | `src/compiler/tests/` |

**Key Features:**
- Exhaustiveness checking for enums and tagged unions
- Detection of unreachable pattern arms
- Strong enum support (no wildcards allowed)
- Pattern subsumption analysis for overlap detection
- Integration with interpreter for runtime warnings
- 18 comprehensive unit tests

**Implementation:** `src/compiler/src/pattern_analysis.rs` (406 lines)

---

### Type System Enhancements (#1330-1342) 📋

**Documentation:**
- [design/type_system_features.md](../design/type_system_features.md)
- [spec/web.md](../spec/web.md)

#### Union Types with Impl Blocks (#1330-1334)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1330 | Union type declarations | 4 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |
| #1331 | Discriminant storage and runtime | 4 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |
| #1332 | Impl blocks for unions | 3 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |
| #1333 | Variant-specific methods | 4 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |
| #1334 | Recursive union support | 4 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |

**Note:** Enums (#50-56) exist but lack associated data. Unions extend this with algebraic data types.

#### Bitfield Types (#1335-1339)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1335 | `bitfield Name(backing):` syntax | 3 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |
| #1336 | Field width and offset calculation | 3 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |
| #1337 | Automatic getter/setter (bit masking) | 3 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |
| #1338 | FFI compatibility (C struct packing) | 4 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |
| #1339 | Multi-bit fields | 3 | ✅ | R | [type_system_features.md](../design/type_system_features.md) | - | `src/type/tests/` |

**Example:**
```simple
bitfield StatusReg(u32):
    enabled: 1       # bit 0
    mode: 2          # bits 1-2
    priority: 4      # bits 3-6
    reserved: 25     # bits 7-31
```

#### HTTP Components (#1340-1342)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1340 | `StatusCode` enum | 2 | ✅ | R | [web.md](../spec/web.md) | - | `src/type/tests/` |
| #1341 | Fluent response builder API | 2 | ✅ | R | [web.md](../spec/web.md) | - | `src/type/tests/` |
| #1342 | Route parameter extraction | 3 | ✅ | R | [web.md](../spec/web.md) | - | `src/type/tests/` |

---

### Gherkin/BDD Extensions (#1343-1347) ✅ **COMPLETE**

Extended Gherkin DSL features for behavior-driven development.

**Documentation:**
- [spec/gherkin_dsl.md](../spec/gherkin_dsl.md)
- [statements/gherkin.rs](../../src/parser/src/statements/gherkin.rs)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1343 | `examples` table definitions | 2 | ✅ | R | [gherkin.rs](../../src/parser/src/statements/gherkin.rs) | - | `src/parser/src/statements/gherkin.rs` |
| #1344 | `context` step definitions | 3 | ✅ | R | [gherkin.rs](../../src/parser/src/statements/gherkin.rs) | - | `src/parser/src/statements/gherkin.rs` |
| #1345 | `scenario outline` with tables | 3 | ✅ | R | [gherkin.rs](../../src/parser/src/statements/gherkin.rs) | - | `src/parser/src/statements/gherkin.rs` |
| #1346 | Parameterized contexts | 3 | ✅ | R | [gherkin.rs](../../src/parser/src/statements/gherkin.rs) | - | `src/parser/src/statements/gherkin.rs` |
| #1347 | Multi-format docstrings | 2 | ✅ | R | [gherkin.rs](../../src/parser/src/statements/gherkin.rs) | - | `src/parser/src/statements/gherkin.rs` |

**Status:** Parser infrastructure complete for examples tables, context step definitions, scenario outlines with placeholder support.

---

### MCP Protocol Core Features (#1348-1358) 📋

Core MCP protocol implementation for token-efficient code representation.

**Documentation:**
- [spec/basic_mcp.md](../spec/basic_mcp.md)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1348 | Block-mark notation (`C>`, `F>`, `T>`, `P>`, `V•`) | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1349 | Progressive disclosure | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1350 | Virtual information overlays | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1351 | Single JSON `text` field format | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1352 | Expand-on-demand via MCP tools | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1353 | Public API outline filtering | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1354 | Dependency symbol extraction | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1355 | AOP pointcut visualization | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1356 | Coverage metric overlays | 3 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1357 | Signature shrinking and elision | 2 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |
| #1358 | Context-aware symbol filtering | 4 | 📋 | S | [basic_mcp.md](../spec/basic_mcp.md) | `std_lib/test/mcp/` | - |

**Description:** 90%+ token reduction via collapsed outline format. Shows public API by default; expand signatures/bodies on demand.

**Relationship to #1210-1299:**
- #1200-1209: Language Server infrastructure
- #1210-1299: Multi-language MCP support and tooling
- #1348-1358: Core MCP protocol features

---

### Developer Tools (#1359-1368) 📋

Language Server Protocol (LSP) and Debug Adapter Protocol (DAP) implementation.

**Documentation:**
- [plans/30_pending_features.md](../plans/30_pending_features.md)

#### Language Server Protocol (#1359-1365)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1359 | LSP implementation | 5 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/lsp/` | - |
| #1360 | Syntax highlighting | 2 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/lsp/` | - |
| #1361 | Auto-completion | 4 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/lsp/` | - |
| #1362 | Go to definition | 3 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/lsp/` | - |
| #1363 | Find references | 3 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/lsp/` | - |
| #1364 | Hover documentation | 2 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/lsp/` | - |
| #1365 | Error diagnostics | 3 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/lsp/` | - |

**Implementation:** Self-hosted in Simple language

#### Debug Adapter Protocol (#1366-1368)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1366 | DAP implementation | 5 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/dap/` | - |
| #1367 | Breakpoints and stepping | 4 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/dap/` | - |
| #1368 | Variable inspection | 4 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/dap/` | - |

---

### UI Frameworks (#1369-1378) 📋

Terminal UI (TUI) and GUI framework implementations.

**Documentation:**
- [plans/30_pending_features.md](../plans/30_pending_features.md)

#### Terminal UI Framework (#1369-1373)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1369 | Widget system (buttons, input, lists, tables) | 4 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/tui/` | - |
| #1370 | Layout engine (flex, grid) | 4 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/tui/` | - |
| #1371 | Event handling (keyboard, mouse) | 3 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/tui/` | - |
| #1372 | Styling (colors, borders, padding) | 3 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/tui/` | - |
| #1373 | Screen management | 3 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/tui/` | - |

**Example:**
```simple
use std.tui.*

app = App():
    layout = VBox():
        title = Text("Welcome").style(bold, color: blue)
        input = Input(placeholder: "Enter name...")
        button = Button("Submit").on_click(handle_submit)
    render(layout)
```

#### GUI Framework (#1374-1378)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1374 | Immediate Mode GUI (egui-style) | 5 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/gui/` | - |
| #1375 | Native widgets | 5 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/gui/` | - |
| #1376 | Web-based GUI (Electron-style) | 5 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/gui/` | - |
| #1377 | Hot reload support | 4 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/gui/` | - |
| #1378 | Cross-platform rendering | 5 | 📋 | S | [30_pending_features.md](../plans/30_pending_features.md) | `std_lib/test/gui/` | - |

---

### Language Features (Misc) (#1379-1387) 📋

Context managers, move closures, and primitive-as-object unification.

**Documentation:**
- [spec/metaprogramming.md](../spec/metaprogramming.md)
- [spec/primitive_as_obj.md](../spec/primitive_as_obj.md)

#### Context Managers (#1379-1380)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1379 | `with` statement and RAII | 3 | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/system/context/` | `src/compiler/tests/` |
| #1380 | `ContextManager` trait | 3 | ✅ | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/system/context/` | - |

**Example:**
```simple
with open("file.txt") as file:
    let content = file.read()
# file automatically closed
```

#### Move Closures (#1381)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1381 | `move \:` closure syntax | 3 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |

**Example:**
```simple
let data = [1, 2, 3]
actor.send(move \: process(data))  # data moved
```

#### Primitive-as-Object Unification (#1382-1387)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1382 | `[]` → `List[T]` auto-promotion | 2 | ✅ | S | [primitive_as_obj.md](../spec/primitive_as_obj.md) | `std_lib/test/system/primitives/` | - |
| #1383 | `[T; N]` → `Array[T, N]` fixed-size | 3 | ✅ | S | [primitive_as_obj.md](../spec/primitive_as_obj.md) | `std_lib/test/system/primitives/` | - |
| #1384 | `str` → `String` unification | 2 | ✅ | S | [primitive_as_obj.md](../spec/primitive_as_obj.md) | `std_lib/test/system/primitives/` | - |
| #1385 | Immutable `List[T]` as persistent linked list | 4 | ✅ | S | [primitive_as_obj.md](../spec/primitive_as_obj.md) | `std_lib/test/system/primitives/` | - |
| #1386 | Structural sharing for immutable collections | 4 | ✅ | S | [primitive_as_obj.md](../spec/primitive_as_obj.md) | `std_lib/test/system/primitives/` | - |
| #1387 | Integer/Float/Bool object methods | 2 | ✅ | S | [primitive_as_obj.md](../spec/primitive_as_obj.md) | `std_lib/test/system/primitives/` | - |

---

### Shared Infrastructure (#1388-1390) ✅ **COMPLETE**

Cross-crate diagnostic infrastructure improvements.

**Documentation:**
- [design/semantic_duplication_analysis.md](../design/semantic_duplication_analysis.md)
- [SHARED_INFRA_COMPLETION.md](SHARED_INFRA_COMPLETION.md)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1388 | Move `Diagnostic` to `simple_common` | 2 | ✅ | R | [diagnostic.rs](../../src/common/src/diagnostic.rs) | - | `src/common/src/diagnostic.rs` |
| #1389 | Cross-crate diagnostic infrastructure | 3 | ✅ | R | [diagnostic.rs](../../src/common/src/diagnostic.rs) | - | `src/parser/src/diagnostic.rs` |
| #1390 | Structured error reporting | 3 | ✅ | R | [diagnostic.rs](../../src/common/src/diagnostic.rs) | - | - |

**Completed:** Moved diagnostics from parser to common crate, enabling all crates to use structured error reporting without circular dependencies.

---

### Advanced Contract Features (#1391-1395) 📋

Extended contract system with preconditions, postconditions, and invariants.

**Documentation:**
- [spec/invariant.md](../spec/invariant.md)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1391 | `in:` precondition blocks | 2 | 📋 | S+R | [invariant.md](../spec/invariant.md) | `std_lib/test/system/contracts/` | `src/compiler/tests/` |
| #1392 | `out(ret):` postcondition blocks | 2 | 📋 | S+R | [invariant.md](../spec/invariant.md) | `std_lib/test/system/contracts/` | `src/compiler/tests/` |
| #1393 | `out_err(err):` error postconditions | 3 | 📋 | S+R | [invariant.md](../spec/invariant.md) | `std_lib/test/system/contracts/` | `src/compiler/tests/` |
| #1394 | `old(expr)` value snapshots | 4 | 📋 | S+R | [invariant.md](../spec/invariant.md) | `std_lib/test/system/contracts/` | `src/compiler/tests/` |
| #1395 | `invariant:` routine invariants | 3 | 📋 | S+R | [invariant.md](../spec/invariant.md) | `std_lib/test/system/contracts/` | `src/compiler/tests/` |

**Example:**
```simple
fn withdraw(amount: i64):
    in:
        amount > 0
        balance >= amount
    out(ret):
        ret == old(balance) - amount
    invariant:
        balance >= 0
    balance -= amount
    return balance
```

**Note:** Basic contracts (#400-406) tracked, but advanced features not listed.

---

### Mock Library Fluent API (#1396-1403) ✅ **COMPLETE**

RSpec/Mockito-style fluent API for mock objects. **Implemented in Rust** as `simple_mock_helper::fluent`.

**Documentation:**
- [spec/mock.md](../spec/mock.md)
- [FLUENT_API.md](../../src/util/simple_mock_helper/FLUENT_API.md)
- [IMPLEMENTATION_SUMMARY.md](../../src/util/simple_mock_helper/IMPLEMENTATION_SUMMARY.md)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1396 | `MockSetup` builder type | 3 | ✅ | R | [fluent.rs](../../src/util/simple_mock_helper/src/fluent.rs) | - | `src/util/simple_mock_helper/src/fluent.rs` |
| #1397 | `Spy` recording type | 3 | ✅ | R | [fluent.rs](../../src/util/simple_mock_helper/src/fluent.rs) | - | `src/util/simple_mock_helper/src/fluent.rs` |
| #1398 | `.when(method).with_args(args).returns(value)` | 3 | ✅ | R | [fluent.rs](../../src/util/simple_mock_helper/src/fluent.rs) | - | `src/util/simple_mock_helper/src/fluent.rs` |
| #1399 | `.method(name).was_called()` assertions | 2 | ✅ | R | [fluent.rs](../../src/util/simple_mock_helper/src/fluent.rs) | - | `src/util/simple_mock_helper/src/fluent.rs` |
| #1400 | `.times(n)` verification | 2 | ✅ | R | [fluent.rs](../../src/util/simple_mock_helper/src/fluent.rs) | - | `src/util/simple_mock_helper/src/fluent.rs` |
| #1401 | `.with_args(args)` verification | 3 | ✅ | R | [fluent.rs](../../src/util/simple_mock_helper/src/fluent.rs) | - | `src/util/simple_mock_helper/src/fluent.rs` |
| #1402 | Argument matchers (`Any`, `GreaterThan`, `Range`, `Pattern`) | 3 | ✅ | R | [fluent.rs](../../src/util/simple_mock_helper/src/fluent.rs) | - | `src/util/simple_mock_helper/src/fluent.rs` |
| #1403 | Deep call chain mocking | 4 | ✅ | R | [fluent.rs](../../src/util/simple_mock_helper/src/fluent.rs) | - | `src/util/simple_mock_helper/src/fluent.rs` |

**Example:**
```simple
let db = mock Database

db.when("query")
  .with(any(), gt(0))
  .returns([{id: 1, name: "Alice"}])

# ... test code ...

db.verify("query").calledTimes(2)
```

**Note:** Mock library (#230-241) exists, but fluent API not documented.

---

## Known Issues

| Issue | Description | Priority |
|-------|-------------|----------|
| Collection mutation | Array/List/Dict changes don't persist | High |
| Type annotation scope | Variables inaccessible after `let x: T = v` | Medium |
| Doctest framework | Requires List mutation and Set | Low |

---

## Next Priorities

### Immediate (Sprint)
1. **Collection mutation** - Fix Array/List/Dict persistence
2. **Type annotation scope** - Fix variable accessibility bug

### Short Term (Month)
1. ~~SDN implementation (#601-605)~~ ✅ Complete
2. Database layer basics (#700-706)

### Medium Term (Quarter)
1. SQP query DSL (#707-713)
2. ~~Web framework basics (#520-536)~~ ✅ Complete

---

## Status Legend

- ✅ **COMPLETE** - Fully implemented and tested
- 📋 **PLANNED** - Designed, not yet implemented

---

## Related Documentation

- [feature_done_1.md](feature_done_1.md) - Archive 1: Infrastructure, Core Language
- [feature_done_2.md](feature_done_2.md) - Archive 2: Codegen, Concurrency, Contracts
- [feature_done_3.md](feature_done_3.md) - Archive 3: UI, Union Types, GPU/SIMD
- [feature_done_4.md](feature_done_4.md) - Archive 4: DB/SQP design, consolidated
- [feature_done_7.md](feature_done_7.md) - Archive 7: Web, Build/Link, Infra, Module Privacy, FFI/ABI
- [db.md](db.md) - Database Abstraction Layer
- [sqp.md](sqp.md) - Simple Query and Persistence DSL
- [research/mold_linker_analysis.md](research/mold_linker_analysis.md) - Mold linker integration analysis
- [research/src_to_bin_optimization.md](research/src_to_bin_optimization.md) - Pipeline optimization guide
- [llm_friendly.md](llm_friendly.md) - LLM Quality Contract
- [plans/llm_friendly.md](plans/llm_friendly.md) - LLM-Friendly Implementation Plan
- [codegen_status.md](codegen_status.md) - MIR instruction coverage
- [architecture.md](architecture.md) - Design principles
- [research/aop.md](../research/aop.md) - AOP & Unified Predicates specification
- [research/sdn_self_hosting.md](../research/sdn_self_hosting.md) - SDN self-hosting and missing features
- [CLAUDE.md](../../CLAUDE.md) - Development guide
