# Simple Language Features

**Last Updated:** 2025-12-20

## Feature Table Format

All feature tables use this standardized 7-column format:

```markdown
| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #NNN | Name | ✅/📋 | R/S/S+R | [doc](path) | `path/` | `path/` |
```

**Column Reference:**

| Column | Description | Example Values |
|--------|-------------|----------------|
| **Feature ID** | Unique identifier (`#NNN`) | `#100`, `#700` |
| **Feature** | Short feature name | `TCP sockets`, `PostgreSQL driver` |
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
| #1000-#1050 | AOP & Unified Predicates | 📋 Planned |
| #1051-#1060 | SDN Self-Hosting | 📋 Planned |
| #1061-#1103 | Missing Language Features | 🔄 In Progress (5/43) |
| #1104-#1115 | Concurrency Modes | 📋 Planned |
| #1116-#1130 | FFI/ABI Interface | ✅ Complete |
| #1131-#1145 | Formatting & Lints | 📋 Planned |
| #1146-#1155 | Trait Coherence | 📋 Planned |

---

## Summary Statistics

**Overall Progress:** 67% (290/434 features complete)

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
| **AOP & Unified Predicates** | 51 | 0 | 51 |
| **SDN Self-Hosting** | 10 | 0 | 10 |
| **Missing Language Features** | 43 | 5 | 38 |
| **Concurrency Modes** | 12 | 0 | 12 |
| **FFI/ABI Interface** | 15 | 15 | 0 |
| **Formatting & Lints** | 15 | 0 | 15 |
| **Trait Coherence** | 10 | 0 | 10 |

**Test Status:** 1089+ tests passing

**Completed Features:** See [feature_done_1.md](feature_done_1.md), [feature_done_2.md](feature_done_2.md), [feature_done_3.md](feature_done_3.md), [feature_done_4.md](feature_done_4.md), [feature_done_5.md](feature_done_5.md), [feature_done_6.md](feature_done_6.md), [feature_done_7.md](feature_done_7.md)

---

## Planned Features

### LLM-Friendly Features (#880-919) 📋

Features to make Simple optimized for LLM-assisted development, verification, and collaboration.

**Documentation:**
- [llm_friendly.md](./llm_friendly.md) - LLM Quality Contract
- [plans/llm_friendly.md](./plans/llm_friendly.md) - Implementation Plan

#### Capability-Based Effects (#880-884)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #880 | `module requires[cap]` | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #881 | `@pure` / `@io` / `@net` | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #882 | Capability propagation | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #883 | Forbidden effect errors | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #884 | Stdlib effect annotations | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/effects/` | - |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #885 | `--emit-ast` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #886 | `--emit-hir` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #887 | `--emit-mir` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #888 | `--error-format=json` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #889 | Semantic diff tool | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Example:**
```bash
simple compile app.spl --emit-ast > ast.json
simple compile app.spl --error-format=json 2> errors.json
simple diff --semantic old.spl new.spl
```

#### Context Pack Generator (#890-893)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #890 | `simple context` command | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #891 | Dependency symbol extraction | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #892 | Markdown context format | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #893 | JSON context format | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

**Example:**
```bash
# Extract minimal context (only symbols used by app.service)
simple context app.service --format=markdown > context.md
simple context app.service --format=json > context.json
```

**Impact:** 90% reduction in LLM context tokens

#### Property-Based Testing (#894-898)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #894 | `@property_test` decorator | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | `src/compiler/tests/` |
| #895 | Input generators | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |
| #896 | Shrinking on failure | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | `src/runtime/tests/` |
| #897 | Configurable iterations | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |
| #898 | Generator combinators | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/property/` | - |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #899 | `@snapshot_test` decorator | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/snapshot/` | `src/compiler/tests/` |
| #900 | Snapshot storage | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #901 | `--snapshot-update` flag | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #902 | Multi-format snapshots | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/snapshot/` | `src/driver/tests/` |

**Example:**
```simple
@snapshot_test
fn test_render_user_json():
    let user = User(id: 42, name: "Alice")
    let json = render_json(user)
    expect_snapshot(json, format: "json")
```

#### Lint Framework (#903-907)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #903 | Lint rule trait | 📋 | S | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/lint/` | - |
| #904 | Built-in rules | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #905 | Configurable severity | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #906 | `simple lint` command | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #907 | Auto-fix suggestions | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #908 | `simple fmt` command | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |
| #909 | Single correct style | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/parser/tests/` |
| #910 | Format-on-save integration | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |

**Impact:** Eliminates stylistic variance; LLM output is predictable

#### Build & Audit Infrastructure (#911-915)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #911 | Deterministic build mode | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #912 | Replay logs | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #913 | `@generated_by` provenance | 📋 | S+R | [llm_friendly.md](llm_friendly.md) | `std_lib/test/system/audit/` | `src/compiler/tests/` |
| #914 | API surface lock file | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |
| #915 | Spec coverage metric | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/driver/tests/` |

**Example:**
```simple
# Auto-generated provenance annotation
@generated_by(tool: "claude", prompt_hash: "abc123", version: "3.5")
fn calculate_tax(amount: i64) -> i64:
    ...
```

#### Sandboxed Execution (#916-919)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #916 | Resource limits | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #917 | Network isolation | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #918 | Filesystem isolation | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/runtime/tests/` |
| #919 | `simple run --sandbox` | 📋 | R | [llm_friendly.md](llm_friendly.md) | `system/cli/` | `src/driver/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1000 | `pc{...}` syntactic island (lexer mode) | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1001 | Predicate operators (!, &, \|, grouping) | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1002 | Pattern wildcards (*, **, prefix*, *suffix) | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1003 | Signature pattern `ret_pat qname_pat(arg_pats)` | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1004 | `..` argument wildcard | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1005 | Allowed introducer validation (`on`, `bind on`, `forbid`, `allow`) | 📋 | R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1006 | Weaving selector set (execution/within/attr/effect/test/decision/condition) | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1007 | DI/Mock selector set (type/within/attr only) | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1008 | Illegal selector in context diagnostic | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1009 | Typed dependency graph (compiler-built) | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1010 | SDN `di:` section with profiles | 📋 | R | [aop.md](../research/aop.md) | - | `src/sdn/tests/` |
| #1011 | `bind on pc{...} -> Impl scope priority` syntax | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1012 | `@sys.inject` constructor injection | 📋 | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/di/` | `src/compiler/tests/` |
| #1013 | Per-parameter `@sys.inject` | 📋 | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/di/` | `src/compiler/tests/` |
| #1014 | Priority/specificity/stable-order resolution | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1015 | Ambiguous binding diagnostic | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1016 | Release profile freeze (direct wiring) | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1017 | All-params-injectable rule for constructor `@sys.inject` | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1018 | Parameter-level diagnostic for unresolvable deps | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1019 | No mixing constructor vs per-param injection | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1020 | `mock Name implements Trait:` syntax | 📋 | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/mock/` | `src/parser/tests/` |
| #1021 | `expect method() -> Type:` syntax | 📋 | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/mock/` | `src/parser/tests/` |
| #1022 | `@sys.test_only` decorator enforcement | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1023 | Mock binding via DI predicates (test profile) | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1024 | Illegal mock in non-test diagnostic | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1025 | Illegal Mock* binding outside test profile | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1026 | `arch_rules:` block syntax | 📋 | S+R | [aop.md](../research/aop.md) | - | `src/parser/tests/` |
| #1027 | `forbid pc{...}` rule | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1028 | `allow pc{...}` rule | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1029 | `import(from_pattern, to_pattern)` selector | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1030 | `depend(from_pattern, to_pattern)` selector | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1031 | `use(pattern)` selector | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1032 | `export(pattern)` selector | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1033 | `config(STRING)` selector | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**SDN Validation Hooks:**
| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1034 | Release build MUST NOT select test profile | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1035 | Release MUST NOT enable runtime interceptors | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Example:**
```simple
arch_rules:
    forbid pc{ import(within(domain.**), within(infrastructure.**)) }
    forbid pc{ depend(within(domain.**), within(infrastructure.**)) }
    forbid pc{ use(Container) & within(domain.**) }
    forbid pc{ config("profiles.test") & attr(release) }
```

#### Phase 7: Compile-Time Weaving (#1036-1042)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1036 | `execution(signature)` join point | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1037 | `within(pattern)` join point | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1038 | `attr(IDENT)` join point | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1039 | `effect(effect_set)` join point | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1040 | `test(IDENT)` join point | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1041 | `decision()`/`condition()` join points (coverage) | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1042 | Zero-overhead when aspects.enabled = [] | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Advice Forms:**
| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1043 | `before` advice | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1044 | `after_success` advice | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1045 | `after_error` advice | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1046 | Advice priority ordering | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |

**Ordering:** Higher priority → earlier for `before`, later for `after_*`, outermost for `around`.

#### Phase 8: Link-Time & Runtime Backends (Optional) (#1047-1050)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1047 | `call(signature)` link-time selector | 📋 | R | [aop.md](../research/aop.md) | - | `src/compiler/tests/` |
| #1048 | `init(pattern)` runtime selector (DI-controlled) | 📋 | R | [aop.md](../research/aop.md) | - | `src/runtime/tests/` |
| #1049 | `around` advice with `proceed()` (runtime only) | 📋 | R | [aop.md](../research/aop.md) | - | `src/runtime/tests/` |
| #1050 | Proceed exactly-once enforcement | 📋 | R | [aop.md](../research/aop.md) | - | `src/runtime/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1051 | `simple.sdn` manifest parsing | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |
| #1052 | Manifest format auto-detection | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |
| #1053 | `simple pkg migrate` command | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |

#### Phase 2: SDN Default (#1054-1056)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1054 | `simple init` generates `.sdn` | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |
| #1055 | TOML deprecation warning | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |
| #1056 | Lock file as SDN (`simple-lock.sdn`) | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/pkg/tests/` |

#### Phase 3: Full SDN (#1057-1060)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1057 | Remove TOML dependency | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | - |
| #1058 | SDN for all config files | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/driver/tests/` |
| #1059 | SDN for AOP/DI config | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/compiler/tests/` |
| #1060 | SDN CLI improvements | 📋 | R | [sdn_self_hosting.md](../research/sdn_self_hosting.md) | - | `src/sdn/tests/` |

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
- [spec/metaprogramming.md](../spec/metaprogramming.md) - Macro/DSL spec
- [spec/language_enhancement.md](../spec/language_enhancement.md) - Memory model

#### Macros (#1061-1065)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1061 | `macro` keyword | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1062 | `gen_code` block | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1063 | Hygienic macro expansion | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1064 | AST manipulation in macros | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1065 | Macro-as-decorator | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |

#### DSL Features (#1066-1068)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1066 | `context obj:` block | ✅ | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/compiler/tests/` |
| #1067 | `method_missing` handler | ✅ | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/compiler/tests/` |
| #1068 | Fluent interface support | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |

#### Built-in Decorators (#1069-1072)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1069 | `@cached` decorator | 📋 | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |
| #1070 | `@logged` decorator | 📋 | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |
| #1071 | `@deprecated(message)` | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/compiler/tests/` |
| #1072 | `@timeout(seconds)` | 📋 | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |

#### Attributes (#1073-1077)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1073 | `#[inline]` hint | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1074 | `#[derive(...)]` auto-impl | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1075 | `#[cfg(...)]` conditional | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1076 | `#[allow(...)]`/`#[deny(...)]` | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1077 | `#[test]` marker | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |

#### Comprehensions (#1078-1082)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1078 | List comprehension | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/parser/tests/` |
| #1079 | Dict comprehension | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/parser/tests/` |
| #1080 | Negative indexing `arr[-1]` | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/runtime/tests/` |
| #1081 | Slicing `arr[2:5]`, `arr[::2]` | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/runtime/tests/` |
| #1082 | Spread `[*a, *b]`, `{**d1, **d2}` | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/parser/tests/` |

#### Pattern Matching Enhancements (#1083-1090)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1083 | Match guards `case x if x > 0:` | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1084 | Or patterns `case "a" \| "b":` | ✅ | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1085 | Range patterns `case 1..10:` | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1086 | `if let Some(x) = ...` | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1087 | `while let Some(x) = ...` | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1088 | Chained comparisons `0 < x < 10` | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1089 | Exhaustiveness checking | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1090 | Unreachable arm detection | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |

#### Context & Error Handling (#1091-1095)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1091 | `with open(...) as f:` | 📋 | S+R | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | `src/parser/tests/` |
| #1092 | `ContextManager` trait | 📋 | S | [metaprogramming.md](../spec/metaprogramming.md) | `std_lib/test/` | - |
| #1093 | `move \:` closures | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/compiler/tests/` |
| #1094 | `?` operator for Result | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |
| #1095 | `?` operator for Option | 📋 | R | [metaprogramming.md](../spec/metaprogramming.md) | - | `src/parser/tests/` |

#### Memory Model (#1096-1103)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1096 | `mut T` exclusive writer capability | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1097 | `iso T` isolated capability | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1098 | Capability conversions | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1099 | Happens-before memory model | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/runtime/tests/` |
| #1100 | Data-race-free guarantee | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/runtime/tests/` |
| #1101 | `Atomic[T]` wrapper | 📋 | S+R | [language_enhancement.md](../spec/language_enhancement.md) | `std_lib/src/infra/` | `src/runtime/tests/` |
| #1102 | `Mutex[T]` wrapper | 📋 | S+R | [language_enhancement.md](../spec/language_enhancement.md) | `std_lib/src/infra/` | `src/runtime/tests/` |
| #1103 | `RwLock[T]` wrapper | 📋 | S+R | [language_enhancement.md](../spec/language_enhancement.md) | `std_lib/src/infra/` | `src/runtime/tests/` |

**Note:** Memory Model features (#1096-1103) require `#[concurrency_mode(lock_base)]` or `#[unsafe]`.

---

### Concurrency Modes (#1104-1115) 📋

Safety modes for concurrency: actor (Erlang-style), lock_base (Rust-style), unsafe.

**Documentation:**
- [spec/language_enhancement.md](../spec/language_enhancement.md) - Section 4: Concurrency Modes

#### Mode System (#1104-1107)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1104 | `#[concurrency_mode(actor)]` (default) | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1105 | `#[concurrency_mode(lock_base)]` | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1106 | `#[concurrency_mode(unsafe)]` | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1107 | `unsafe:` block syntax | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/parser/tests/` |

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

Native concurrent libraries (TBB, crossbeam) with GC-managed objects.

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1108 | GC write barriers in concurrent collections | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/runtime/tests/` |
| #1109 | `ConcurrentMap[K, V]` with GC objects | 📋 | S+R | [language_enhancement.md](../spec/language_enhancement.md) | `std_lib/src/infra/` | `src/runtime/tests/` |
| #1110 | `ConcurrentQueue[T]` with GC objects | 📋 | S+R | [language_enhancement.md](../spec/language_enhancement.md) | `std_lib/src/infra/` | `src/runtime/tests/` |
| #1111 | `ConcurrentStack[T]` with GC objects | 📋 | S+R | [language_enhancement.md](../spec/language_enhancement.md) | `std_lib/src/infra/` | `src/runtime/tests/` |
| #1112 | Object tracing through collection handles | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/runtime/tests/` |

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

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1113 | Compile error for `mut T` in actor mode | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1114 | Compile error for `Mutex` in actor mode | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |
| #1115 | Warning for unsafe in release build | 📋 | R | [language_enhancement.md](../spec/language_enhancement.md) | - | `src/compiler/tests/` |

---

### Formatting and Lints (#1131-1145) 📋

Deterministic formatting and semantic lint set for code quality.

**Documentation:**
- [spec/formatting_lints.md](../spec/formatting_lints.md) - Formatting and Lints Specification

#### Canonical Formatter (#1131-1133)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1131 | Canonical formatter (no config) | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1132 | Formatter CLI (`simple fmt`) | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1133 | Format-on-save IDE integration | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | - |

#### Semantic Lints (#1134-1138)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1134 | Safety lint set | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1135 | Correctness lint set | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1136 | Warning lint set | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1137 | Style lint set | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1138 | Concurrency lint set | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |

#### Lint Control (#1139-1145)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1139 | `#[allow]`/`#[deny]`/`#[warn]` attributes | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/parser/tests/` |
| #1140 | Lint groups | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1141 | Fix-it hints in diagnostics | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1142 | Auto-fix CLI (`simple fix`) | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1143 | Error code stability | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1144 | Lint configuration in simple.sdn | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1145 | `--explain` for error codes | 📋 | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |

---

### Trait Coherence (#1146-1155) 📋

Trait implementation rules for unambiguous dispatch and type safety.

**Documentation:**
- [spec/traits.md](../spec/traits.md) - Trait Coherence Rules section

#### Core Coherence (#1146-1149)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1146 | Orphan rule enforcement | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1147 | Overlap detection | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1148 | Associated type coherence | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1149 | Blanket impl conflict detection | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |

#### Advanced Coherence (#1150-1153)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1150 | Specialization (`#[default]` impl) | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1151 | Negative trait bounds (`!Trait`) | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1152 | Coherence error messages | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1153 | Newtype pattern support | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |

#### Extension Methods (#1154-1155)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1154 | Extension traits | 📋 | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1155 | Delegation pattern | 📋 | S | [traits.md](../spec/traits.md) | `std_lib/test/` | - |

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
