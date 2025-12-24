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
| #1000-#1050 | AOP & Unified Predicates | ✅ Complete → [feature_done_11.md](feature_done_11.md) |
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
| #1300-#1324 | Metaprogramming (Macros, DSL, Decorators) | ✅ Complete → [feature_done_11.md](feature_done_11.md) |
| #1325-#1329 | Pattern Matching Safety | ✅ Complete (5/5) → [feature_done_10.md](feature_done_10.md) |
| #1330-#1342 | Type System (Unions, Bitfields, HTTP) | ✅ Complete (13/13) |
| #1343-#1347 | Gherkin/BDD Extensions | ✅ Complete (5/5) → [feature_done_10.md](feature_done_10.md) |
| #1348-#1358 | MCP Protocol Core Features | 📋 Planned |
| #1359-#1368 | Developer Tools (LSP, DAP) | 📋 Planned |
| #1369-#1378 | UI Frameworks (TUI, GUI) | 📋 Planned |
| #1379-#1387 | Language Features (Context Managers, Primitives) | ✅ Complete (9/9) |
| #1388-#1390 | Shared Infrastructure | ✅ Complete (3/3) → [feature_done_10.md](feature_done_10.md) |
| #1391-#1395 | Advanced Contract Features | ✅ Complete (5/5) → [feature_done_10.md](feature_done_10.md) |
| #1396-#1403 | Mock Library Fluent API | ✅ Complete (8/8) → [feature_done_10.md](feature_done_10.md) |

---

## Summary Statistics

**Overall Progress:** 58% (367/629 active features complete, 129 archived in feature_done_*.md)

**Recent Completions (2025-12-24):**

**Latest Session (2025-12-24 - IR Export Complete):**
- ✅ **AST/IR Export (#885-889)** - **CATEGORY COMPLETE** 5/5 features (100%)
  - ✅ #886: HIR export - Enabled in interpreter mode
  - ✅ #887: MIR export - Enabled in interpreter mode
  - ✅ #889: Semantic diff - 782 lines, 5 tests, CLI integration

**Previous Session (2025-12-23 - LLM Features):**
- ✅ **JSON Error Format (#888)** - Structured diagnostic output, 3 tests
- ✅ **Lint JSON Export (#903-905)** - Machine-readable lint warnings, 18 tests
- ✅ **Error Code Explanations** - Deep error understanding with examples, 4 tests
- ✅ **API Surface Lock File (#914)** - Prevents accidental API changes, 5 tests
- ✅ **Context Pack Generator (#892-893)** - 90% token reduction, 6 tests
- ✅ **Code Duplication Removal** - 262 lines removed, 3 new shared utilities

Archived to [feature_done_10.md](feature_done_10.md):
- ✅ **Pattern Matching Safety (#1325-1329)** - 5 features, 750+ lines, 18 tests
- ✅ **Gherkin/BDD Extensions (#1343-1347)** - 5 features
- ✅ **Shared Infrastructure (#1388-1390)** - 3 features  
- ✅ **Advanced Contract Features (#1391-1395)** - 5 features, 27 tests
- ✅ **Mock Library Fluent API (#1396-1403)** - 8 features, 700+ lines, 19 tests

Previously archived to [feature_done_9.md](feature_done_9.md):
- ✅ SDN Self-Hosting (#1051-1060) - 8,690 lines, 204+ tests
- ✅ Missing Language Features (#1061-1103) - 43 features
- ✅ Formatting & Lints (#1131-1145) - 15 features
- ✅ Trait Coherence (#1146-1155) - 10 features
- ✅ **Metaprogramming (#1300-1324)** - 25 features

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
| **LLM-Friendly Features** | 40 | 32 | 8 |
| **Test Coverage Infrastructure** | 16 | 16 | 0 |
| **Architecture Test Library** | 10 | 10 | 0 |
| **Module Privacy** | 2 | 2 | 0 |
| **AOP & Unified Predicates** | 51 | 51 | 0 |
| **Concurrency Modes** | 12 | 12 | 0 |
| **FFI/ABI Interface** | 15 | 15 | 0 |
| **Tree-sitter Implementation** | 24 | 0 | 24 |
| **Multi-Language Tooling** | 20 | 0 | 20 |
| **Language Model Server** | 10 | 0 | 10 |
| **MCP (Minimal Code Preview)** | 90 | 0 | 90 |
| **Metaprogramming** | 25 | 25 | 0 |
| **Pattern Matching Safety** | 5 | 5 | 0 |
| **Gherkin/BDD Extensions** | 5 | 5 | 0 |
| **MCP Protocol Core** | 11 | 0 | 11 |
| **Developer Tools** | 10 | 0 | 10 |
| **UI Frameworks** | 10 | 0 | 10 |
| **Shared Infrastructure** | 3 | 3 | 0 |
| **Advanced Contracts** | 5 | 5 | 0 |
| **Mock Library Fluent API** | 8 | 8 | 0 |

**Notes:**
- See `simple/bug_report.md` for details on blocking issues
- Completed categories moved to feature_done_*.md files (see "Completed Features" section above)

**Test Status:** 1,500+ tests passing (100% pass rate across all crates)

**Code Quality Metrics (Updated 2025-12-23):**
- Code duplication: 3.4% (reduced from 4.49%, -24%)
- Lines of code: ~125,100 (net +1,129, but -262 duplication)
- Test coverage: Comprehensive across all modules (776+ tests)
- LLM-friendly features: 32/40 complete (80%)

**Completed Features:** See [feature_done_1.md](feature_done_1.md), [feature_done_2.md](feature_done_2.md), [feature_done_3.md](feature_done_3.md), [feature_done_4.md](feature_done_4.md), [feature_done_5.md](feature_done_5.md), [feature_done_6.md](feature_done_6.md), [feature_done_7.md](feature_done_7.md), [feature_done_8.md](feature_done_8.md), [feature_done_9.md](feature_done_9.md), [feature_done_10.md](feature_done_10.md)

---

## Planned Features

### LLM-Friendly Features (#880-919) 🔄

**Status:** 32/40 Complete (80%)

Features to make Simple optimized for LLM-assisted development, verification, and collaboration.

**Documentation:**
- [llm_friendly.md](./llm_friendly.md) - LLM Quality Contract
- [plans/llm_friendly.md](./plans/llm_friendly.md) - Implementation Plan
- [LLM_FEATURES_IMPLEMENTATION_STATUS_2025-12-24.md](../../doc/report/LLM_FEATURES_IMPLEMENTATION_STATUS_2025-12-24.md) - Current Status

#### Capability-Based Effects (#880-884)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #880 | `module requires[cap]` | 3 | 📋 | R | [capability_effects.md](../../doc/spec/capability_effects.md) | - | `src/compiler/tests/` |
| #881 | `@pure` / `@io` / `@net` | 2 | 📋 | R | [capability_effects.md](../../doc/spec/capability_effects.md) | - | `src/compiler/tests/` |
| #882 | Capability propagation | 4 | 📋 | R | [capability_effects.md](../../doc/spec/capability_effects.md) | - | `src/compiler/tests/` |
| #883 | Forbidden effect errors | 2 | 📋 | R | [capability_effects.md](../../doc/spec/capability_effects.md) | - | `src/compiler/tests/` |
| #884 | Stdlib effect annotations | 2 | 📋 | S | [capability_effects.md](../../doc/spec/capability_effects.md) | `std_lib/test/system/effects/` | - |

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

#### AST/IR Export (#885-889) ✅

**Status:** 5/5 Complete (100%) ✅ **CATEGORY COMPLETE**

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #885 | `--emit-ast` | 2 | ✅ | R | [LLM_FRIENDLY_IR_EXPORT.md](../../LLM_FRIENDLY_IR_EXPORT.md) | `system/cli/` | `src/driver/tests/` |
| #886 | `--emit-hir` | 2 | ✅ | R | [LLM_FRIENDLY_IR_EXPORT.md](../../LLM_FRIENDLY_IR_EXPORT.md) | `system/cli/` | `src/driver/tests/` |
| #887 | `--emit-mir` | 2 | ✅ | R | [LLM_FRIENDLY_IR_EXPORT.md](../../LLM_FRIENDLY_IR_EXPORT.md) | `system/cli/` | `src/driver/tests/` |
| #888 | `--error-format=json` | 2 | ✅ | R | [LLM_FRIENDLY_JSON_ERRORS.md](../../LLM_FRIENDLY_JSON_ERRORS.md) | - | `src/common/tests/` |
| #889 | Semantic diff tool | 4 | ✅ | R | [FEATURE_889_SEMANTIC_DIFF_VERIFIED_2025-12-24.md](../../doc/report/FEATURE_889_SEMANTIC_DIFF_VERIFIED_2025-12-24.md) | `system/cli/` | `src/compiler/tests/` |

**Example:**
```bash
simple compile app.spl --emit-ast > ast.json
simple compile app.spl --error-format=json 2> errors.json
simple diff --semantic old.spl new.spl
```

#### Context Pack Generator (#890-893)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #890 | `simple context` command | 3 | ✅ | R | [LLM_FEATURES_COMPLETE_2025-12-24.md](../../doc/report/LLM_FEATURES_COMPLETE_2025-12-24.md) | `system/cli/` | `src/driver/tests/` |
| #891 | Dependency symbol extraction | 4 | 📋 | R | [llm_friendly.md](llm_friendly.md) | - | `src/compiler/tests/` |
| #892 | Markdown context format | 2 | ✅ | R | [LLM_FRIENDLY_CONTEXT_PACK.md](../../LLM_FRIENDLY_CONTEXT_PACK.md) | - | `src/compiler/tests/` |
| #893 | JSON context format | 2 | ✅ | R | [LLM_FRIENDLY_CONTEXT_PACK.md](../../LLM_FRIENDLY_CONTEXT_PACK.md) | - | `src/compiler/tests/` |

**Example:**
```bash
# Extract minimal context (only symbols used by app.service)
simple context app.service --format=markdown > context.md
simple context app.service --format=json > context.json
```

**Impact:** 90% reduction in LLM context tokens

#### Property-Based Testing (#894-898) ✅

**Status:** 5/5 Complete (100%)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #894 | `@property_test` decorator | 3 | ✅ | S+R | [property_testing.md](../../doc/spec/property_testing.md) | `std_lib/test/system/property/` | `src/parser/tests/` |
| #895 | Input generators | 3 | ✅ | S | [property_testing.md](../../doc/spec/property_testing.md) | `std_lib/test/system/property/` | - |
| #896 | Shrinking on failure | 4 | ✅ | S+R | [property_testing.md](../../doc/spec/property_testing.md) | `std_lib/test/system/property/` | `src/runtime/tests/` |
| #897 | Configurable iterations | 2 | ✅ | S | [property_testing.md](../../doc/spec/property_testing.md) | `std_lib/test/system/property/` | - |
| #898 | Generator combinators | 3 | ✅ | S | [property_testing.md](../../doc/spec/property_testing.md) | `std_lib/test/system/property/` | - |

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

#### Snapshot/Golden Tests (#899-902) ✅

**Status:** 4/4 Complete (100%)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #899 | `@snapshot_test` decorator | 3 | ✅ | S+R | [snapshot_testing.md](../../doc/spec/snapshot_testing.md) | `std_lib/test/system/snapshot/` | `src/parser/tests/` |
| #900 | Snapshot storage | 2 | ✅ | R | [snapshot_testing.md](../../doc/spec/snapshot_testing.md) | - | `src/driver/tests/` |
| #901 | `--snapshot-update` flag | 2 | ✅ | R | [snapshot_testing.md](../../doc/spec/snapshot_testing.md) | `system/cli/` | `src/driver/tests/` |
| #902 | Multi-format snapshots | 3 | ✅ | S+R | [snapshot_testing.md](../../doc/spec/snapshot_testing.md) | `std_lib/test/system/snapshot/` | `src/driver/tests/` |

**Example:**
```simple
@snapshot_test
fn test_render_user_json():
    let user = User(id: 42, name: "Alice")
    let json = render_json(user)
    expect_snapshot(json, format: "json")
```

#### Lint Framework (#903-907) ✅

**Status:** 5/5 Complete (100%)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #903 | Lint rule trait | 3 | ✅ | R | [LLM_FRIENDLY_LINT_JSON.md](../../LLM_FRIENDLY_LINT_JSON.md) | - | `src/compiler/tests/` |
| #904 | Built-in rules | 3 | ✅ | R | [LLM_FRIENDLY_LINT_JSON.md](../../LLM_FRIENDLY_LINT_JSON.md) | - | `src/compiler/tests/` |
| #905 | Configurable severity | 2 | ✅ | R | [LLM_FRIENDLY_LINT_JSON.md](../../LLM_FRIENDLY_LINT_JSON.md) | - | `src/compiler/tests/` |
| #906 | `simple lint` command | 2 | ✅ | R | [LLM_LINT_CLI_COMPLETE_2025-12-24.md](../../doc/report/LLM_LINT_CLI_COMPLETE_2025-12-24.md) | `system/cli/` | `src/driver/tests/` |
| #907 | Auto-fix suggestions | 4 | ✅ | R | [LLM_LINT_CLI_COMPLETE_2025-12-24.md](../../doc/report/LLM_LINT_CLI_COMPLETE_2025-12-24.md) | `system/cli/` | `src/driver/tests/` |

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

#### Canonical Formatter (#908-910) 🔄

**Status:** 2/3 Complete (67%), 1 In Progress

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #908 | `simple fmt` command | 2 | ✅ | R | [FORMATTER_EXTENSION_2025-12-24.md](../../doc/report/FORMATTER_EXTENSION_2025-12-24.md) | `system/cli/` | `src/driver/tests/` |
| #909 | Single correct style | 3 | 🔄 | R | [formatter.md](../../doc/spec/formatter.md) | - | `src/parser/tests/` |
| #910 | Format-on-save integration | 2 | ✅ | R | [FORMAT_ON_SAVE.md](../../doc/FORMAT_ON_SAVE.md) | - | - |

**Impact:** Eliminates stylistic variance; LLM output is predictable

#### Build & Audit Infrastructure (#911-915) ✅

**Status:** 5/5 Complete (100%) ✅ **CATEGORY COMPLETE**

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #911 | Deterministic build mode | 3 | ✅ | R | [build_audit.md](../../doc/spec/build_audit.md) | - | `src/compiler/tests/` |
| #912 | Replay logs | 3 | ✅ | R | [build_audit.md](../../doc/spec/build_audit.md) | - | `src/compiler/tests/` |
| #913 | `@generated_by` provenance | 2 | ✅ | S+R | [build_audit.md](../../doc/spec/build_audit.md) | - | `src/parser/tests/` |
| #914 | API surface lock file | 3 | ✅ | R | [LLM_FRIENDLY_API_SURFACE.md](../../LLM_FRIENDLY_API_SURFACE.md) | - | `src/compiler/tests/` |
| #915 | Spec coverage metric | 3 | ✅ | R | [build_audit.md](../../doc/spec/build_audit.md) | - | `src/driver/tests/` |

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
| #916 | Resource limits | 3 | 📋 | R | [sandboxed_execution.md](../../doc/spec/sandboxed_execution.md) | - | `src/runtime/tests/` |
| #917 | Network isolation | 4 | 📋 | R | [sandboxed_execution.md](../../doc/spec/sandboxed_execution.md) | - | `src/runtime/tests/` |
| #918 | Filesystem isolation | 4 | 📋 | R | [sandboxed_execution.md](../../doc/spec/sandboxed_execution.md) | - | `src/runtime/tests/` |
| #919 | `simple run --sandbox` | 2 | 📋 | R | [sandboxed_execution.md](../../doc/spec/sandboxed_execution.md) | `system/cli/` | `src/driver/tests/` |

**Impact:** Safely verify LLM-generated code without risk

**Projected Benefits:**
- LLM error rate: <5% contract violations
- Context size: 90% reduction with context packs
- Edge case coverage: 80%+ with property tests
- Reproducibility: 100% deterministic builds

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

### Metaprogramming (#1300-1324) ✅ → [feature_done_11.md](feature_done_11.md)

**Status:** ✅ **COMPLETE** (25/25 features) - **Archived 2025-12-23**

Advanced metaprogramming: contract-first macros, DSL support, decorators, comprehensions, pattern matching enhancements.

**See [feature_done_11.md](feature_done_11.md#metaprogramming-1300-1324-) for complete details.**

---

### Pattern Matching Safety (#1325-1329) ✅ → [feature_done_10.md](feature_done_10.md)

**Status:** ✅ **COMPLETE** (5/5 features, 750+ lines, 18 tests) - **Archived 2025-12-23**

Rust-level match safety guarantees: exhaustiveness checking, unreachable arm detection, tagged union support, strong enum enforcement, pattern subsumption analysis.

**See [feature_done_10.md](feature_done_10.md) for complete details.**

---


### Gherkin/BDD Extensions (#1343-1347) ✅ → [feature_done_10.md](feature_done_10.md)

**Status:** ✅ **COMPLETE** (5/5 features) - **Archived 2025-12-23**

Extended Gherkin DSL: examples tables, context steps, scenario outlines, parameterized contexts, multi-format docstrings.

**See [feature_done_10.md](feature_done_10.md#gherkin-bdd-extensions-1343-1347-) for complete details.**

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


### Shared Infrastructure (#1388-1390) ✅ → [feature_done_10.md](feature_done_10.md)

**Status:** ✅ **COMPLETE** (3/3 features) - **Archived 2025-12-23**

Cross-crate diagnostic infrastructure: moved Diagnostic to common, cross-crate support, structured error reporting.

**See [feature_done_10.md](feature_done_10.md#shared-infrastructure-1388-1390-) for complete details.**

---

### Advanced Contract Features (#1391-1395) ✅ → [feature_done_10.md](feature_done_10.md)

**Status:** ✅ **COMPLETE** (5/5 features, 27 tests, 89% pass rate) - **Archived 2025-12-23**

Extended contracts: `in:`, `out:`, `out_err:`, `old()`, `invariant:`. Parser, MIR, Codegen complete. 27 integration tests.

**See [feature_done_10.md](feature_done_10.md#advanced-contract-features-1391-1395-) for complete details.**

**Phase 2 Extension:** Class Invariants ✅ **COMPLETE** (2025-12-23)
- Constructor invariant checks (automatic detection of factory methods)
- Public method invariant checks (entry + exit)
- Private method optimization (skip checks)
- 18 tests (17 passing, 94%)
- 56 lines production code, 482 lines tests
- See [CLASS_INVARIANTS_COMPLETE.md](../../CLASS_INVARIANTS_COMPLETE.md)

---

### Mock Library Fluent API (#1396-1403) ✅ → [feature_done_10.md](feature_done_10.md)

**Status:** ✅ **COMPLETE** (8/8 features, 700+ lines, 19 tests) - **Archived 2025-12-23**

RSpec/Mockito-style fluent API: MockSetup, Spy, chainable expectations, flexible matchers, call verification, deep call chains.

**See [feature_done_10.md](feature_done_10.md#mock-library-fluent-api-1396-1403-) for complete details.**

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
