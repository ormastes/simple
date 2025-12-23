# Simple Language Features

**Last Updated:** 2025-12-23

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
| #1000-#1050 | AOP & Unified Predicates | 🔄 In Progress (3/51) |
| #1051-#1060 | SDN Self-Hosting | 📋 Planned |
| #1061-#1103 | Missing Language Features | 🔄 In Progress (20/43) |
| #1104-#1115 | Concurrency Modes | ✅ Complete (14/12) |
| #1116-#1130 | FFI/ABI Interface | ✅ Complete |
| #1131-#1145 | Formatting & Lints | 🔄 In Progress (10/15) |
| #1146-#1155 | Trait Coherence | 🔄 In Progress (1/10) |
| #1156-#1179 | Tree-sitter Implementation | 📋 Planned |
| #1180-#1199 | Multi-Language Tooling | 📋 Planned |
| #1200-#1299 | Language Model Server & MCP | 📋 Planned |

---

## Summary Statistics

**Overall Progress:** 60% (354/588 features complete)

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
| **AOP & Unified Predicates** | 51 | 3 | 48 |
| **SDN Self-Hosting** | 10 | 0 | 10 |
| **Missing Language Features** | 43 | 20 | 23 |
| **Concurrency Modes** | 12 | 14 | -2 |
| **FFI/ABI Interface** | 15 | 15 | 0 |
| **Formatting & Lints** | 15 | 10 | 5 |
| **Trait Coherence** | 10 | 1 | 9 |
| **Tree-sitter Implementation** | 24 | 0 | 24 |
| **Multi-Language Tooling** | 20 | 0 | 20 |
| **Language Model Server & MCP** | 100 | 0 | 100 |
| **Macro Hygiene** | 1 | 1 | 0 |

**Test Status:** 1121+ tests passing (1089 + 32 capability + 7 memory model + 6 sync)

**Completed Features:** See [feature_done_1.md](feature_done_1.md), [feature_done_2.md](feature_done_2.md), [feature_done_3.md](feature_done_3.md), [feature_done_4.md](feature_done_4.md), [feature_done_5.md](feature_done_5.md), [feature_done_6.md](feature_done_6.md), [feature_done_7.md](feature_done_7.md), [feature_done_8.md](feature_done_8.md)

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

### SDN Self-Hosting (#1051-1060) 📋

Replace `simple.toml` with `simple.sdn` - use Simple's native data format for its own configuration.

**Documentation:**
- [research/sdn_self_hosting.md](../research/sdn_self_hosting.md) - Full specification

**Current:** `simple.toml` (TOML format)
**Proposed:** `simple.sdn` (SDN format)

#### Phase 1: Dual Support (#1051-1053)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1051 | `simple.sdn` manifest parsing | 3 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |
| #1052 | Manifest format auto-detection | 2 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |
| #1053 | `simple pkg migrate` command | 2 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |

#### Phase 2: SDN Default (#1054-1056)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1054 | `simple init` generates `.sdn` | 2 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |
| #1055 | TOML deprecation warning | 1 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |
| #1056 | Lock file as SDN (`simple-lock.sdn`) | 2 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |

#### Phase 3: Full SDN (#1057-1060)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1057 | Remove TOML dependency | 2 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | - |
| #1058 | SDN for all config files | 3 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/driver/tests/` |
| #1059 | SDN for AOP/DI config | 3 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/compiler/tests/` |
| #1060 | SDN CLI improvements | 2 | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/sdn/tests/` |

**SDN Manifest Example:**
```sdn
package:
    name: myproject
    version: 0.1.0
    main: src/main.spl

dependencies:
    http: 1.0
    json:
        version: 2.0
        features = [serde]

features |name, deps|
    full, [http, json, logging]
    minimal, [http]
```

---

### Missing Language Features (#1061-1103) 🔄

Features documented in `doc/spec/` but not yet tracked.

**Documentation:**
- [research/sdn_self_hosting.md](../research/sdn_self_hosting.md) - Full feature list
- [spec/macro.md](../spec/macro.md) - Contract-first macro spec
- [spec/metaprogramming.md](../spec/metaprogramming.md) - DSL/decorators/attributes
- [spec/language_enhancement.md](../spec/language_enhancement.md) - Memory model

#### Macros (#1061-1065)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1065b | Macro intros must not shadow existing symbols | 3 | ✅ | R | [macro.md](../spec/macro.md) | - | - |

Notes: type checker enforces macro definition order and const-evaluates `intro` for/if blocks.

#### DSL Features (#1066-1068)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1068 | Fluent interface support | 2 | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |

#### Built-in Decorators (#1069-1072)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1069 | `@cached` decorator | 3 | 📋 | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |
| #1070 | `@logged` decorator | 2 | 📋 | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |
| #1071 | `@deprecated(message)` | 2 | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/compiler/tests/` |
| #1072 | `@timeout(seconds)` | 3 | 📋 | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |

#### Attributes (#1073-1077)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1073 | `#[inline]` hint | 2 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1074 | `#[derive(...)]` auto-impl | 4 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1075 | `#[cfg(...)]` conditional | 3 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1076 | `#[allow(...)]`/`#[deny(...)]` | 2 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1077 | `#[test]` marker | 2 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |

#### Comprehensions (#1078-1082)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1078 | List comprehension | 3 | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/parser/tests/` |
| #1079 | Dict comprehension | 3 | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/parser/tests/` |
| #1080 | Negative indexing `arr[-1]` | 2 | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/runtime/tests/` |
| #1081 | Slicing `arr[2:5]`, `arr[::2]` | 3 | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/runtime/tests/` |
| #1082 | Spread `[*a, *b]`, `{**d1, **d2}` | 3 | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/parser/tests/` |

#### Pattern Matching Enhancements (#1083-1090)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1085 | Range patterns `case 1..10:` | 2 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1086 | `if let Some(x) = ...` | 3 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1087 | `while let Some(x) = ...` | 3 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1088 | Chained comparisons `0 < x < 10` | 2 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1089 | Exhaustiveness checking | 4 | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1090 | Unreachable arm detection | 3 | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |

#### Context & Error Handling (#1091-1095)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1091 | `with open(...) as f:` | 3 | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/parser/tests/` |
| #1092 | `ContextManager` trait | 2 | 📋 | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |
| #1093 | `move \:` closures | 3 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1094 | `?` operator for Result | 2 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1095 | `?` operator for Option | 2 | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |

#### Memory Model (#1096-1103)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|

#### Formal Verification (#1104-1106)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|

**Status:** All memory model features complete (#1096-1106)! Complete formal verification in Lean 4.

**Implementation:**
- **Reference capabilities** (#1096-1098): Zero-cost abstraction, 32 tests passing
  - `mut T`, `iso T`, `T` with compile-time aliasing prevention
  - Capability conversion rules (iso→mut→shared)
- **Happens-before model** (#1099): Graph-based tracking with 7 tests passing
  - Program order, synchronization order, transitivity
  - Runtime race detection API (`is_race_free()`, `detect_data_races()`)
- **SC-DRF guarantee** (#1100): Formal proof in Lean 4
  - Sequential consistency for data-race-free programs
  - Synchronization axioms (locks, atomics, threads, channels)
- **Sync primitives** (#1101-1103): Runtime FFI with 6 tests passing
  - `Atomic[T]`: Lock-free with Acquire/Release/SeqCst ordering
  - `Mutex[T]`, `RwLock[T]`: RAII guards, happens-before on lock/unlock
  - Semaphore, Barrier, Channel synchronization
- **Formal verification** (#1104-1106): Complete Lean 4 proofs
  - **MemoryCapabilities.lean** (350+ lines): Aliasing prevention, conversion safety
  - **MemoryModelDRF.lean** (510+ lines): SC-DRF theorem, race detection correctness
  - **Integration proof**: Capabilities + SC-DRF = complete memory safety

See [MEMORY_MODEL_IMPLEMENTATION_SUMMARY.md](../report/MEMORY_MODEL_IMPLEMENTATION_SUMMARY.md) and [SC_DRF_VERIFICATION_COMPLETE.md](../report/SC_DRF_VERIFICATION_COMPLETE.md).

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

### Formatting and Lints (#1131-1145) 🔄

Deterministic formatting and semantic lint set for code quality.

**Status:** Phase 1 Complete (pattern-based tools in Simple) - Phase 2 Planned (AST-based)

**Documentation:**
- [spec/formatting_lints.md](../spec/formatting_lints.md) - Formatting and Lints Specification
- `simple/app/README.md` - Formatter & Linter implementation details

**Implementation:**
- ✅ Source: `simple/app/formatter/main.spl` (166 lines), `simple/app/lint/main.spl` (262 lines)
- ⏳ Build: Run `./simple/build_tools.sh` to compile binaries
- ⏳ Phase 2: AST-based analysis, control flow analysis
- ⏳ Phase 3: IDE integration, auto-fix

#### Canonical Formatter (#1131-1133)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1133 | Format-on-save IDE integration | 2 | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | - |

**Features (#1131-1132):**
- ✅ 4-space indentation, idempotent formatting
- ✅ `--check` (CI), `--write` (in-place), stdout output
- ✅ Handles `:`, `{}`, `[]`, `else`, `elif` indentation
- ⏳ TODO: AST-based, comment preservation, max line length

#### Semantic Lints (#1134-1138)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|

**Lints Implemented (14 total):**
- Safety (S001-S003): Unused Result, null deref, unsafe without comment
- Correctness (C001-C003): Unreachable code, non-exhaustive match, type mismatch
- Warning (W001-W003): Unused variable/import, dead code
- Style (ST001-ST003): Naming conventions (Allow by default)
- Concurrency (CC001-CC002): Shared mutable state, thread safety

#### Lint Control (#1139-1145)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1139 | `#[allow]`/`#[deny]`/`#[warn]` attributes | 2 | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/parser/tests/` |
| #1142 | Auto-fix CLI (`simple fix`) | 4 | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1144 | Lint configuration in simple.sdn | 2 | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1145 | `--explain` for error codes | 2 | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |

**Features (#1140-1141, #1143):**
- ✅ `--deny-all`, `--warn-all` for lint level control
- ✅ Fix-it hints with formatted output (file:line:col)
- ✅ Stable error codes (S001-S003, C001-C003, W001-W003, ST001-ST003, CC001-CC002)

---

### Trait Coherence (#1146-1155) 📋

Trait implementation rules for unambiguous dispatch and type safety.

**Documentation:**
- [spec/traits.md](../spec/traits.md) - Trait Coherence Rules section

#### Core Coherence (#1146-1149)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1146 | Orphan rule enforcement | 3 | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1147 | Overlap detection | 4 | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1148 | Associated type coherence | 4 | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1149 | Blanket impl conflict detection | 4 | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |

#### Advanced Coherence (#1150-1153)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1151 | Negative trait bounds (`!Trait`) | 4 | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1152 | Coherence error messages | 3 | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1153 | Newtype pattern support | 2 | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |

#### Extension Methods (#1154-1155)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #1154 | Extension traits | 3 | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1155 | Delegation pattern | 3 | 📋 | S | [traits.md](../spec/traits.md) | `std_lib/test/` | - |

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

### Language Model Server & MCP (#1200-1299) 📋

Server infrastructure and Minimal Code Preview protocol for LLM-optimized code understanding.

**🎯 SELF-HOSTED: MCP and Language Server implemented in Simple language**

**Documentation:**
- [spec/basic_mcp.md](../spec/basic_mcp.md) - MCP Specification v1.0
- [plans/llm_friendly.md](../plans/llm_friendly.md) - Implementation Plan
- [guides/llm_friendly.md](../guides/llm_friendly.md) - LLM Quality Contract

**Key Benefits:**
- 90%+ token reduction via collapsed outline format
- Multi-language support (Simple, Rust, Python, Ruby, Erlang, etc.)
- Progressive disclosure (expand on demand)
- Virtual information (auto traits, AOP, coverage)
- Single JSON field format for minimal overhead
- Integrated compile/test/deploy tooling

**Prerequisites:**
- Tree-sitter implementation (#1156-1179) - Required for multi-language parsing
- Multi-language tooling (#1180-1199) - Required for compile/test/deploy

**Implementation:**
- Language: **Simple** (self-hosted)
- Location: `simple/std_lib/src/lms/` and `simple/std_lib/src/mcp/`

#### Language Model Server - Basic (#1200-1209)

Server infrastructure for handling MCP protocol requests. **Implemented in Simple language.**

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

#### MCP Core Features - Simple Language (#1210-1229)

Core MCP protocol implementation for Simple/Basic language folding. **Implemented in Simple language.**

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

MCP support for multiple programming languages using Tree-sitter. **Implemented in Simple language.**

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

**Implementation Notes:**
- **Self-hosted:** MCP and Language Server implemented in Simple language
- **Prerequisite:** Tree-sitter (#1156-1179) for multi-language parsing
- MCP reduces token usage by 90%+ via collapsed outline format
- Uses block marks (`C>`, `F>`, `T>`, `P>`, `V•`) for structure
- Single JSON `text` field for LLM efficiency
- Progressive disclosure via tool calls (not inline hints)
- Exposes virtual information (auto traits, AOP, coverage)
- Multi-language support: Simple, Rust, Python, Ruby, Erlang, Go, C/C++, JS/TS
- Integrated tooling: compile, test, deploy via MCP protocol

**Implementation Locations:**
- Language Server: `simple/std_lib/src/lms/` (written in Simple)
- MCP Core: `simple/std_lib/src/mcp/` (written in Simple)
- Tree-sitter: `simple/std_lib/src/treesitter/` (written in Simple)
- Multi-lang Tooling: `simple/std_lib/src/tooling/` (written in Simple)

**Related Features:**
- #1156-1179: Tree-sitter Implementation (prerequisite)
- #1180-1199: Multi-Language Tooling (prerequisite)
- #890-893: Context Pack Generator (LLM-Friendly)
- #885-889: AST/IR Export (LLM-Friendly)
- #1300-1304: Contract-first macro system (parser + hygiene)

### Contract-First Macros (#1300-1304) 🔄

Contract-first macros declare `intro`/`inject`/`returns` headers that enumerate the symbols they introduce before expanding the body. Expansion now runs at the AST level with hygiene so that macro-generated bindings never shadow the caller.

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|

**Notes:**
- #1300/1301 delivered the new `macro` header syntax plus `const_eval`/`emit` execution before AST-level hygiene existed.
- #1303 (`intro`/`inject`/`returns` symbol table integration) and #1304 (one-pass LL(1) macro compilation) remain planned but are now unblocked by hygienic expansion.
- Hygiene lives in `src/compiler/src/interpreter_macro.rs` via `MacroHygieneContext` plus the `apply_macro_hygiene_*` helpers that rewrite emitted blocks, statements, expressions, and patterns before calls to `exec_block`.

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
