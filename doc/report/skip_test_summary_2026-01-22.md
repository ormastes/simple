# Skip Test Summary - Quick Reference

**Total: 772 skipped tests**

## Skip Test Tree

```
772 Total Skips
├── 425 Unit Tests (55%)
│   ├── 151 Parser/Tree-sitter
│   │   ├── 80 Grammar compilation (grammar_simple_spec.spl)
│   │   ├── 23 Grammar testing framework
│   │   ├── 20 Python grammar support
│   │   ├── 15 Rust grammar support
│   │   └── 13 Other (lexer, query, language detection)
│   │
│   ├── 42 ML/Torch
│   │   ├── 36 Tensor operations
│   │   └── 6 Neural networks
│   │
│   ├── 37 Debug Adapter Protocol (DAP)
│   │   ├── 15 Server implementation
│   │   ├── 13 Protocol messages
│   │   └── 9 Type definitions
│   │
│   ├── 30 Concurrency (ALL blocked on async runtime)
│   │   ├── 10 Promise creation
│   │   ├── 8 Promise operations
│   │   ├── 7 Promise combinators
│   │   └── 5 Type safety
│   │
│   ├── 28 Tooling
│   │   ├── 10 Build system
│   │   ├── 8 Package management
│   │   ├── 6 Code generation
│   │   └── 4 Project management
│   │
│   ├── 28 SDN Format
│   │   ├── 15 Parser
│   │   ├── 9 Compatibility with Rust
│   │   └── 4 Roundtrip tests
│   │
│   ├── 26 Verification (Lean 4 proofs)
│   │   ├── 10 Memory safety
│   │   ├── 8 Type system
│   │   └── 8 Runtime properties
│   │
│   ├── 25 Language Server Protocol (LSP)
│   │   ├── 8 Completions
│   │   ├── 7 Diagnostics
│   │   ├── 6 Navigation
│   │   └── 4 Code actions
│   │
│   ├── 22 Testing - Contract Testing
│   │   ├── 8 Pre/post conditions
│   │   ├── 6 Invariants
│   │   ├── 5 Contract inheritance
│   │   └── 3 Runtime checking
│   │
│   ├── 20 Game Engine
│   │   ├── 8 Physics/collision
│   │   ├── 7 Rendering
│   │   └── 5 Entity-component system
│   │
│   └── 16 Other
│       ├── 7 Constraints
│       ├── 5 Host platform
│       └── 4 Misc
│
├── 293 System/Feature Tests (38%)
│   ├── 79 Testing Framework
│   │   ├── 53 Property-based testing
│   │   ├── 22 Contract testing
│   │   └── 4 Other
│   │
│   ├── 52 Snapshot Testing
│   │   ├── 22 Formats
│   │   ├── 16 Comparison
│   │   └── 14 Runner/basic
│   │
│   ├── 30 SDN System Tests
│   │   ├── 17 CLI tools
│   │   └── 13 File I/O
│   │
│   ├── 27 Architecture Tests
│   │   └── Module boundaries, dependencies
│   │
│   ├── 25 Stdlib Improvements
│   │   └── API enhancements, optimizations
│   │
│   └── 80 Other System Tests
│
└── 54 Integration Tests (7%)
    ├── 24 UI/TUI (ratatui backend)
    ├── 16 ML Integration
    └── 14 Spec Framework

```

## Quick Navigation

### By Priority (Unlock Impact)

1. **Tree-sitter Grammar** - 151 skips → LSP, syntax highlighting
2. **Testing Infrastructure** - 131 skips → Property/snapshot/contract testing
3. **Async Runtime** - 30 skips → Promise API, concurrency
4. **DAP** - 37 skips → Debugger support
5. **SDN Parser** - 28 skips → Data format compatibility

### By Status/Blocker

#### Blocked on Missing Feature
- **Async Runtime** → 30 concurrency tests
- **Tree-sitter Integration** → 151 parser tests
- **Testing Infrastructure** → 79+ testing framework tests

#### Work in Progress
- **Tree-sitter files** → Recently migrated to [] syntax (2026-01-22)
- **SDN parser** → Basic implementation exists, needs completion

#### Deferred/Low Priority
- **Verification** (26) → Lean 4 integration planned but not started
- **Game Engine** (20) → Optional feature
- **UI/TUI** (24) → Terminal UI framework

#### Future Enhancements
- **Stdlib Improvements** (25) → API enhancements
- **Architecture Tests** (27) → Enforcement tools

## Files with Most Skips (Top 10)

| # | File | Skips | Blocker |
|---|------|-------|---------|
| 1 | `parser/treesitter/grammar_simple_spec.spl` | 80 | Grammar not complete |
| 2 | `concurrency/promise_spec.spl` | 30 | No async runtime |
| 3 | `tooling/tooling_spec.spl` | 28 | Build system pending |
| 4 | `spec/arch_spec.spl` | 27 | Architecture tests deferred |
| 5 | `verification/memory_capabilities_spec.spl` | 26 | Lean 4 integration |
| 6 | `improvements/stdlib_improvements_spec.spl` | 25 | Future enhancements |
| 7 | `ui/tui/ratatui_backend_spec.spl` | 24 | TUI not started |
| 8 | `property/generators_spec.spl` | 23 | Property testing infra |
| 9 | `snapshot/formats_spec.spl` | 22 | Snapshot testing infra |
| 10 | `testing/contract_spec.spl` | 22 | Contract testing infra |

## Recent Changes

**2026-01-22:**
- Fixed tree-sitter syntax migration (angle → square brackets)
- Current skip count: **772**
- Previous documented count (2026-01-16): 1,241
- **Reduction: 469 skips (37.8%)**

## Next Steps

1. **Immediate** (this sprint)
   - Complete async runtime basics → unblock 30 tests
   - Implement core tree-sitter grammar → unblock 80+ tests
   
2. **Short term** (next 2-3 sprints)
   - Complete SDN parser → unblock 28 tests
   - Basic DAP implementation → unblock 37 tests
   
3. **Medium term** (this quarter)
   - Testing infrastructure (property, snapshot, contract) → unblock 131 tests
   - LSP core features → unblock 25 tests

---

**See also:**
- `doc/report/skip_test_analysis_2026-01-22.md` - Full analysis with trends
- `doc/report/skip_test_by_category_2026-01-22.md` - Detailed breakdown by feature
- `doc/test/test_result.md` - Latest test run results
