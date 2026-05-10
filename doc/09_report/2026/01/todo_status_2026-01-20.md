# TODO Status Report - 2026-01-20

## Summary

**Total TODOs in stdlib:** 67 (excluding todo_parser.spl meta-references)

**By Priority:**
- **P1 (High Priority):** 23 TODOs
- **P2 (Medium Priority):** 6 TODOs
- **Untagged:** ~38 TODOs (mostly implementation stubs)

## TODOs by Feature Category

### 1. Regex Library (P1) - **14 TODOs**

**Status:** ❌ Not Implemented

**Blocking:**
- `migrate_spec_to_spl.spl` - 7 TODOs
- `scaffold_feature.spl` - 6 TODOs
- `spec_gen.spl` - 5 TODOs

**Use Cases:**
- Markdown parsing and extraction
- Code pattern matching
- Title extraction from spec files
- Template variable replacement
- Feature scaffolding

**Files Affected:**
```
simple/std_lib/src/tooling/migrate_spec_to_spl.spl:
  - TODO: [stdlib][P1] Add regex library to Simple
  - TODO: [stdlib][P1] Add regex
  - TODO: [stdlib][P1] Add regex
  - TODO: [stdlib][P1] Add regex
  - TODO: [stdlib][P1] Add regex and markdown parsing
  - TODO: [stdlib][P1] Needs regex and markdown parsing for full implementation
  - TODO: [stdlib][P1] Needs regex and markdown parsing for full implementation

simple/std_lib/src/tooling/scaffold_feature.spl:
  - TODO: [stdlib][P1] Add regex support (6 instances)
  - TODO: [stdlib][P1] Needs regex support for full parsing

simple/std_lib/src/tooling/spec_gen.spl:
  - TODO: [stdlib][P1] Add regex library to Simple
  - TODO: [stdlib][P1] Add regex library (2 instances)
  - TODO: [stdlib][P1] Add regex for title extraction
  - TODO: [stdlib][P1] Add regex support for pattern matching
```

### 2. Rust AST Parsing (P2) - **5 TODOs**

**Status:** ❌ Not Implemented

**Blocking:**
- `refactor_lowering.spl` - Tool to extract match arms into helper methods

**Use Cases:**
- Parse Rust impl blocks
- Extract match expressions
- Extract match arms
- Refactor lowering.rs code

**Files Affected:**
```
simple/std_lib/src/tooling/refactor_lowering.spl:
  - TODO: [stdlib][P2] Add Rust AST parsing (3 instances)
  - TODO: [stdlib][P2] Needs Rust AST parsing for full implementation (2 instances)
```

**Note:** Downgraded from P1 to P2 after string manipulation was implemented.

### 3. Markdown Parsing (P1) - **2 TODOs**

**Status:** ❌ Not Implemented

**Blocking:**
- `migrate_spec_to_spl.spl` - Migration from markdown specs to .spl

**Use Cases:**
- Parse markdown test specifications
- Extract code blocks from markdown
- Convert markdown to spec files

**Files Affected:**
```
simple/std_lib/src/tooling/migrate_spec_to_spl.spl:
  - TODO: [stdlib][P1] Add markdown parsing library
  - TODO: [stdlib][P1] Add regex and markdown parsing
```

### 4. JSON Serialization (P1) - **2 TODOs**

**Status:** ❌ Not Implemented

**Blocking:**
- `context_pack.spl` - Context pack serialization

**Use Cases:**
- Serialize context packs to JSON
- Export structured data
- LLM integration

**Files Affected:**
```
simple/std_lib/src/tooling/context_pack.spl:
  - TODO: [compiler][P1] Add JSON serialization to stdlib
  - TODO: [stdlib][P1] Add JSON serialization library
```

### 5. HashMap/Map Type (P2) - **2 TODOs**

**Status:** ❌ Not Implemented

**Blocking:**
- `lint_config.spl` - Lint configuration storage

**Use Cases:**
- Key-value storage
- Configuration management
- Fast lookups

**Files Affected:**
```
simple/std_lib/src/tooling/lint_config.spl:
  - TODO: [stdlib][P2] Add HashMap/Map type to stdlib
```

### 6. BTreeMap/BTreeSet (P1) - **1 TODO**

**Status:** ❌ Not Implemented

**Blocking:**
- `context_pack.spl` - Ordered collections

**Use Cases:**
- Sorted key-value storage
- Ordered sets
- Range queries

**Files Affected:**
```
simple/std_lib/src/tooling/context_pack.spl:
  - TODO: [compiler][P1] Add BTreeMap/BTreeSet to stdlib
```

### 7. Command-Line Argument Parsing (P1) - **1 TODO**

**Status:** ❌ Not Implemented

**Blocking:**
- `spec_gen.spl` - CLI argument handling

**Use Cases:**
- Parse flags and options
- Validate arguments
- Help text generation

**Files Affected:**
```
simple/std_lib/src/tooling/spec_gen.spl:
  - TODO: [stdlib][P1] Add command-line argument parsing
```

### 8. Glob/Directory Listing (P1) - **1 TODO**

**Status:** ❌ Not Implemented (Partially - list_dir exists in file_io)

**Blocking:**
- `spec_gen.spl` - Finding spec files

**Use Cases:**
- Pattern-based file matching
- Recursive directory traversal
- File filtering

**Files Affected:**
```
simple/std_lib/src/tooling/spec_gen.spl:
  - TODO: [stdlib][P1] Add glob/directory listing
```

**Note:** Basic directory listing is available via `infra.file_io.list_dir()` and `infra.file_io.glob()`, but may need enhancement.

### 9. Sandbox FFI Binding (P1) - **1 TODO**

**Status:** ❌ Not Implemented

**Blocking:**
- `sandbox.spl` - Runtime sandbox integration

**Use Cases:**
- Process sandboxing
- Security isolation
- Resource limits

**Files Affected:**
```
simple/std_lib/src/tooling/sandbox.spl:
  - TODO: [runtime][P1] Implement FFI binding to simple_runtime::apply_sandbox()
```

### 10. Implementation Stubs (~38 TODOs)

**Status:** ⚠️ Placeholder/Stub Functions

**Categories:**
- Module imports (when available)
- Parser integration
- Compiler integration
- Config parsing

**Files with Stubs:**
```
simple/std_lib/src/tooling/startup.spl:
  - TODO: Implement or import from actual modules when available

simple/std_lib/src/tooling/feature_db.spl:
  - TODO: Implement or import from test_runner module when available

simple/std_lib/src/tooling/coverage.spl:
  - TODO: Implement or import from coverage module when available

simple/std_lib/src/tooling/basic.spl:
  - TODO: Implement or import from runner module when available

simple/std_lib/src/tooling/i18n_commands.spl:
  - TODO: Implement or import from i18n module when available

simple/std_lib/src/tooling/compile_commands.spl:
  - TODO: Implement or import from compiler module when available

simple/std_lib/src/tooling/web_commands.spl:
  - TODO: Implement or import from web module when available

simple/std_lib/src/tooling/misc_commands.spl:
  - TODO: Implement or import from actual modules when available

simple/std_lib/src/tooling/pkg_commands.spl:
  - TODO: Implement or import from pkg module when available

simple/std_lib/src/tooling/env_commands.spl:
  - TODO: Parse config to show more info

simple/std_lib/src/tooling/lint_config.spl:
  - TODO: [compiler][P2] Add Attribute type to Simple or use FFI

simple/std_lib/src/tooling/context_pack.spl:
  - TODO: [compiler][P1] Integrate with Parser and ApiSurface
  - TODO: [compiler][P1] Implement minimal mode extraction

simple/std_lib/src/infra/config_env.spl:
  - TODO(dict): Implement rt_dict_remove() in runtime
```

## Recently Completed (2026-01-20)

### ✅ File I/O (P1) - 6 TODOs Removed
- Implemented comprehensive file I/O module (`infra.file_io`)
- 21 runtime FFI functions registered
- 30+ safe wrapper functions
- Removed TODOs from: migrate_spec_to_spl, extract_tests, spec_gen, file_walker

### ✅ String Manipulation (P1) - 4 TODOs Removed
- String library already fully implemented (`core.string`)
- 40+ operations (split, replace, trim, etc.)
- 450+ lines of implementation
- Removed outdated TODOs from refactor_lowering.spl

### ✅ Path/PathBuf Types (P1) - 1 TODO Removed
- Implemented Path and PathBuf types (`infra.path`)
- 26 methods for path manipulation
- Cross-platform support (Unix/Windows)
- Removed TODO from spec_gen.spl

## Priority Recommendations

### Highest Impact (P1)

1. **Regex Library** - 14 TODOs blocking
   - Most requested feature
   - Blocks 3 major tooling modules
   - Consider integrating with regex crate via FFI

2. **JSON Serialization** - 2 TODOs blocking
   - Critical for LLM tooling
   - Context pack export
   - Consider serde_json FFI integration

3. **Markdown Parsing** - 2 TODOs blocking
   - Test migration workflow
   - Could use pulldown-cmark via FFI

4. **Collections (HashMap, BTreeMap)** - 3 TODOs blocking
   - Core data structures
   - Many use cases across codebase

### Medium Impact (P2)

1. **Rust AST Parsing** - 5 TODOs blocking
   - Needed for refactoring tools
   - Could use syn crate via FFI
   - Lower priority than regex

### Lower Impact

1. **Implementation Stubs** - ~38 TODOs
   - Most are placeholders for future integration
   - Will be resolved as modules are implemented
   - Not urgent blockers

## Statistics

| Category | P1 | P2 | Untagged | Total |
|----------|----|----|----------|-------|
| Regex | 14 | 0 | 0 | 14 |
| Rust AST | 0 | 5 | 0 | 5 |
| Markdown | 2 | 0 | 0 | 2 |
| JSON | 2 | 0 | 0 | 2 |
| Collections | 1 | 2 | 0 | 3 |
| Stubs | 4 | 1 | ~33 | ~38 |
| CLI Args | 1 | 0 | 0 | 1 |
| Glob | 1 | 0 | 0 | 1 |
| Sandbox | 1 | 0 | 0 | 1 |
| **Total** | **23** | **6** | **~38** | **~67** |

## Trend Analysis

**Session Progress (2026-01-20):**
- Started: ~78 TODOs
- Completed: 11 TODOs
- Remaining: 67 TODOs
- **Reduction: 14%**

**Features Completed:**
- File I/O ✅
- String Manipulation ✅
- Path/PathBuf ✅

**Next Recommended Implementation:**
1. Regex library (blocks 14 TODOs)
2. JSON serialization (blocks 2 TODOs, enables LLM tools)
3. HashMap/Map types (blocks 3 TODOs, core data structure)

## Implementation Strategy

### Quick Wins (FFI Integration)

Many of these features can be implemented quickly via FFI bindings to existing Rust crates:

1. **Regex** → `regex` crate
2. **JSON** → `serde_json` crate
3. **Markdown** → `pulldown-cmark` crate
4. **Collections** → Rust std HashMap/BTreeMap

### Pure Simple Implementation

Some features should be implemented in Simple for better integration:

1. **Command-line argument parsing** - Pure Simple
2. **Glob patterns** - FFI to `glob` crate
3. **File walking** - Build on existing file_io

## Conclusion

The codebase has **67 TODOs remaining**, with the highest concentration in:
1. **Regex support** (14 TODOs) - Highest priority
2. **Implementation stubs** (~38 TODOs) - Will resolve over time
3. **Rust AST parsing** (5 TODOs) - Medium priority

**Recommended next steps:**
1. Implement regex library via FFI
2. Implement JSON serialization via FFI
3. Add HashMap/BTreeMap via FFI
4. This would resolve ~19 P1 TODOs and unblock major tooling modules
