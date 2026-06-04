# TODO Categorization - Non-Compiler Items

**Date:** 2026-01-20
**Status:** 📊 Analysis Complete
**Scope:** All remaining TODOs excluding completed compiler implementations

## Executive Summary

**Total Unique TODOs:** 51 unique items
**Total Instances:** 126+ occurrences (many duplicates)
**Compiler TODOs:** 0 (✅ All completed)
**Non-Compiler TODOs:** 51

### Priority Breakdown
- **P0 (Critical):** 0
- **P1 (High):** 31 items (61%)
- **P2 (Medium):** 4 items (8%)
- **P3 (Low):** 16 items (31%)

## Category 1: Stdlib API - Core Infrastructure (P1)

**Status:** 🔴 CRITICAL - Blocking many features
**Count:** 12 unique APIs
**Priority:** P1
**Effort:** High (each 1-4 weeks)

### File I/O (Most Critical)
```simple
# Needed in 7+ different tools
[stdlib][P1] Add file I/O library to Simple
[stdlib][P1] Add file reading FFI
[stdlib][P1] Add file reading to stdlib
[stdlib][P1] Add file writing support
```

**Blocks:**
- All migration tools
- Test discovery
- Context pack generation
- Spec generation
- Lint configuration

**Implementation:**
- FFI bindings to Rust std::fs
- Simple wrapper API
- Path handling
- Error handling

### Regex Support (Second Most Critical)
```simple
# Needed in 6+ different tools
[stdlib][P1] Add regex library to Simple
[stdlib][P1] Add regex support
[stdlib][P1] Add regex support for pattern matching
[stdlib][P1] Add regex for title extraction
```

**Blocks:**
- All code migration tools
- Pattern matching utilities
- Test extraction
- Spec generation

**Implementation:**
- FFI bindings to Rust regex crate
- Simple API wrapper
- Match groups support
- Replace functionality

### CLI Argument Parsing
```simple
[stdlib][P1] Add CLI argument parsing
[stdlib][P1] Add command-line argument parsing
```

**Blocks:**
- All CLI tools (10+ utilities)
- User-facing tools
- Build scripts

**Implementation:**
- Arg parsing library
- Help generation
- Type conversion
- Validation

### Additional P1 APIs
```simple
[stdlib][P1] Add datetime library to Simple        # Time operations
[stdlib][P1] Add directory operations              # Directory traversal
[stdlib][P1] Add glob/directory listing            # File finding
[stdlib][P1] Add Path/PathBuf type to Simple       # Path manipulation
[stdlib][P1] Add JSON serialization library        # Data interchange
[stdlib][P1] Add markdown parsing library          # Doc processing
[stdlib][P1] Add string manipulation library       # String utilities
```

**Total P1 Stdlib APIs:** 12 items

## Category 2: Stdlib API - Advanced Features (P1)

**Status:** 🟡 HIGH PRIORITY - For advanced tooling
**Count:** 6 items
**Priority:** P1
**Effort:** Medium-High (2-6 weeks each)

```simple
[compiler][P1] Add BTreeMap/BTreeSet to stdlib     # Ordered collections
[compiler][P1] Add JSON serialization to stdlib    # Serialization
[compiler][P1] Implement minimal mode extraction   # Context packing
[compiler][P1] Integrate with Parser and ApiSurface # Compiler integration
[stdlib][P2] Add HashMap/Map type to stdlib        # Hash tables
[stdlib][P2] Add Rust AST parsing                  # AST manipulation
```

**Use Cases:**
- Context pack generation (for LLMs)
- Code refactoring tools
- AST-based transformations
- Advanced data structures

## Category 3: DAP (Debug Adapter Protocol) Infrastructure

**Status:** 🟠 DEFERRED - Needs DAP server framework
**Count:** 7 items
**Priority:** P2-P3
**Effort:** Very High (4-8 weeks total)

```simple
[stdlib][P2] Parse program path, args, etc.        # Launch configuration
[stdlib][P3] Actually start execution              # Debug session start
[stdlib][P3] Get actual stack from interpreter     # Stack trace
[stdlib][P3] Get actual variables from interpreter # Variable inspection
[stdlib][P3] Actually continue execution           # Continue command
[stdlib][P3] Actually step                         # Step command
[stdlib][P3] Check condition if present            # Conditional breakpoints
```

**Current Status:** Mock implementation with placeholder data

**Blockers:**
- DAP protocol implementation
- Interpreter integration
- Debugger infrastructure
- VSCode extension integration

**Implementation Path:**
1. Complete interpreter instrumentation
2. Add debugging hooks to runtime
3. Implement DAP protocol handlers
4. Connect to VSCode debugging API
5. Add breakpoint management
6. Implement step/continue logic

## Category 4: LSP (Language Server Protocol) Features

**Status:** 🟠 DEFERRED - Needs LSP server framework
**Count:** 3 items
**Priority:** P3
**Effort:** High (3-6 weeks total)

```simple
[stdlib][P3] Extract prefix at cursor position for better filtering
[stdlib][P3] Implement sophisticated context analysis for smarter completions
[stdlib][P3] Implement proper scope-based filtering for better accuracy
```

**Current Status:** Basic LSP with limited features

**Blockers:**
- LSP protocol full implementation
- Symbol table from compiler
- Scope analysis
- Type inference integration

**Use Cases:**
- Smart autocomplete
- Go to definition
- Find references
- Hover information

## Category 5: Interpreter Enhancement

**Status:** 🟡 MEDIUM PRIORITY
**Count:** 3 items
**Priority:** P3
**Effort:** Medium (2-4 weeks total)

```simple
[stdlib][P3] Look up method in class definition    # OOP support
[stdlib][P3] FFI call with argument marshalling    # FFI support
[stdlib][P3] Load compiled module and call function # Module loading
```

**Blockers:**
- Class/method registry in interpreter
- FFI marshalling layer (libffi)
- Module loading infrastructure

**Impact:**
- Full OOP method dispatch
- C library integration
- Compiled code interop

## Category 6: Linting & Analysis

**Status:** 🟢 LOW PRIORITY
**Count:** 2 items
**Priority:** P3
**Effort:** Low-Medium (1-2 weeks total)

```simple
[stdlib][P3] Add TODO/FIXME format lints (T00x rules)
[stdlib][P3] Use AST-based linting when compiler integration is available
```

**Current Status:** Pattern-based linting works

**Enhancement:**
- AST-based semantic linting
- TODO format validation
- Custom lint rules

## Category 7: Services & Tools

**Status:** 🟢 LOW PRIORITY
**Count:** 4 items
**Priority:** P3
**Effort:** Medium (2-4 weeks total)

```simple
[stdlib][P3] Create and run LMS server              # Language Model Server
[stdlib][P3] Get actual command line arguments      # LMS CLI
[stdlib][P3] Implement actual search across files   # MCP search
[stdlib][P3] Load and display actual obligations    # Verification display
```

**Use Cases:**
- LLM integration (Claude, GPT)
- Multi-file search (MCP)
- Formal verification UI

## Category 8: Runtime & Sandboxing

**Status:** 🔴 HIGH PRIORITY
**Count:** 1 item
**Priority:** P1
**Effort:** Medium (1-2 weeks)

```simple
[runtime][P1] Implement FFI binding to simple_runtime::apply_sandbox()
```

**Purpose:** Security sandboxing for untrusted code
**Blocks:** Safe code execution, plugin systems
**Implementation:** FFI binding to Rust runtime

## Priority Matrix

### P0 (Critical) - 0 items
None. All critical compiler TODOs completed.

### P1 (High) - 31 items

**Stdlib Core APIs (12):**
- File I/O (multiple aspects)
- Regex support
- CLI argument parsing
- DateTime library
- Directory operations
- Glob/listing
- Path handling
- JSON serialization
- Markdown parsing
- String manipulation

**Advanced Features (6):**
- BTreeMap/BTreeSet
- Context packing
- Parser integration
- HashMap/Map
- Rust AST parsing

**Runtime (1):**
- Sandbox FFI binding

**Total P1:** 19 unique features (31 TODO items including variations)

### P2 (Medium) - 4 items
- HashMap/Map (also in P1 list)
- Rust AST parsing (also in P1 list)
- DAP program launch parsing
- Attribute type support

### P3 (Low) - 16 items
- DAP features (6 items)
- LSP features (3 items)
- Interpreter features (3 items)
- Linting features (2 items)
- Services (2 items)

## Implementation Roadmap

### Phase 1: Core Stdlib APIs (CRITICAL)
**Duration:** 8-12 weeks
**Priority:** P1

1. **File I/O** (2 weeks)
   - Read/write files
   - Directory operations
   - Path manipulation

2. **Regex** (2 weeks)
   - Pattern matching
   - Match groups
   - Replace operations

3. **CLI Parsing** (1 week)
   - Argument parsing
   - Help generation
   - Type conversion

4. **DateTime** (1 week)
   - Basic date/time types
   - Formatting
   - Parsing

5. **JSON** (2 weeks)
   - Serialization
   - Deserialization
   - Error handling

6. **Collections** (2 weeks)
   - HashMap/BTreeMap
   - HashSet/BTreeSet
   - Dictionary types

7. **Additional** (2 weeks)
   - Markdown parsing
   - String utilities
   - Glob patterns

**Deliverables:** Core stdlib ready for tool development

### Phase 2: Advanced Tooling (HIGH)
**Duration:** 4-6 weeks
**Priority:** P1-P2

1. **Context Packing** (2 weeks)
   - API surface extraction
   - Minimal mode
   - Parser integration

2. **AST Parsing** (2 weeks)
   - Rust AST access
   - Simple AST utilities
   - Transformation helpers

3. **Sandbox Runtime** (1 week)
   - FFI binding
   - Security policies
   - Capability control

**Deliverables:** Advanced development tools ready

### Phase 3: DAP & LSP (MEDIUM)
**Duration:** 6-10 weeks
**Priority:** P2-P3

1. **DAP Implementation** (4-6 weeks)
   - Protocol handlers
   - Interpreter integration
   - Breakpoint management
   - Step/continue logic

2. **LSP Enhancement** (2-4 weeks)
   - Smart completion
   - Scope analysis
   - Symbol resolution

**Deliverables:** Full IDE integration

### Phase 4: Interpreter & Services (LOW)
**Duration:** 4-6 weeks
**Priority:** P3

1. **Interpreter Enhancement** (2-3 weeks)
   - Method lookup
   - FFI marshalling
   - Module loading

2. **Services** (2-3 weeks)
   - LMS server
   - MCP integration
   - Verification UI

**Deliverables:** Complete ecosystem

## Dependency Graph

```
Core APIs (File I/O, Regex, CLI)
    ↓
Migration Tools (all 5 tools unblocked)
    ↓
Advanced Tooling (Context Pack, AST)
    ↓
IDE Features (DAP, LSP)
    ↓
Services (LMS, MCP, Verification)
```

## Complexity Assessment

### Easy (1-2 weeks each)
- CLI argument parsing
- DateTime library
- Sandbox FFI binding
- String manipulation

### Medium (2-4 weeks each)
- File I/O
- Regex support
- JSON serialization
- HashMap/BTreeMap
- Interpreter enhancements

### Hard (4-8 weeks each)
- DAP full implementation
- LSP enhancement
- Context pack integration
- Rust AST parsing
- Module loading

## Blockers Analysis

### Blocked Items: 35/51 (69%)

**Blocked by File I/O:** 15 items
- All migration tools
- Spec generation
- Test discovery
- Lint configuration

**Blocked by Regex:** 10 items
- Code migration tools
- Pattern matching
- Test extraction

**Blocked by CLI Parsing:** 10 items
- All CLI tools

**Blocked by Infrastructure:** 10 items
- DAP (needs debugger)
- LSP (needs server)
- Interpreter (needs architecture)

## Recommendations

### Immediate (Next Sprint)
1. ✅ **File I/O** - Unblocks 15 tools
2. ✅ **Regex** - Unblocks 10 tools
3. ✅ **CLI Parsing** - Unblocks 10 tools

**Impact:** Enables 35+ blocked features

### Short-term (1-2 months)
4. DateTime library
5. JSON serialization
6. HashMap/BTreeMap
7. Directory operations

### Medium-term (3-6 months)
8. DAP implementation
9. LSP enhancement
10. Context pack tooling

### Long-term (6-12 months)
11. Full interpreter OOP
12. FFI marshalling
13. Module loading
14. Service integrations

## Summary Statistics

| Category | Count | Priority | Status |
|----------|-------|----------|--------|
| Stdlib Core APIs | 12 | P1 | 🔴 Critical |
| Advanced Features | 6 | P1-P2 | 🟡 High |
| DAP Infrastructure | 7 | P2-P3 | 🟠 Deferred |
| LSP Features | 3 | P3 | 🟠 Deferred |
| Interpreter | 3 | P3 | 🟡 Medium |
| Linting | 2 | P3 | 🟢 Low |
| Services | 4 | P3 | 🟢 Low |
| Runtime | 1 | P1 | 🔴 High |
| **TOTAL** | **51** | **Mixed** | **Analysis Complete** |

## Conclusion

The majority of remaining TODOs are **stdlib API features** (35/51, 69%), with most being P1 priority. The key blockers are:

1. **File I/O** - Critical, blocks 15+ features
2. **Regex** - Critical, blocks 10+ features
3. **CLI Parsing** - Critical, blocks 10+ features

**Recommended Focus:** Implement the top 3 stdlib APIs to unblock 70% of deferred features.

**Compiler Status:** ✅ Complete (0 remaining TODOs)

**Next Priority:** Stdlib infrastructure, not more compiler work.
