# Parser/Lexer/TreeSitter File Locations - Reference Guide

**Date:** 2026-02-04
**Status:** Post-Duplication Analysis
**Related:**
- `doc/research/parser_duplication_analysis_2026-02-04.md` - Duplication analysis
- `doc/design/parser_architecture_unified_2026-02-04.md` - Architecture design
- `doc/plan/parser_merge_plan_2026-02-04.md` - Merge implementation plan

---

## Quick Reference

### What to Use When

| Task | Use This File | Size | Notes |
|------|--------------|------|-------|
| **Tokenize Simple code** | `compiler/lexer.spl` | 1,268 L | ✅ CANONICAL |
| **Parse Simple code** | `compiler/parser.spl` | 1,813 L | ✅ CANONICAL |
| **Get outline (compiler)** | `compiler/treesitter.spl` | 1,444 L | ✅ CANONICAL |
| **Get outline (LSP/IDE)** | `compiler/parser/treesitter.spl` | 509 L | ✅ Fast mode |
| **Parse SDN format** | `std/sdn/parser.spl` | 683 L | SDN only |
| **Tokenize SDN format** | `std/sdn/lexer.spl` | 411 L | SDN only |
| **Parse IR DSL** | `compiler/irdsl/parser.spl` | 147 L | IR DSL only |
| **Parse predicates** | `compiler/predicate_parser.spl` | 251 L | Type predicates |
| **Scan imports** | `app/depgraph/parser.spl` | 271 L | Dependency tool |
| **Scan annotations** | `app/ffi_gen/parser.spl` | 310 L | FFI generator |
| **Parse test DB** | `app/test_runner_new/test_db_parser.spl` | 267 L | Test runner |
| **Wrap for interpreter** | `app/interpreter/parser.spl` | 65 L | Convenience |

---

## File Tree (Current State)

```
src/
├── compiler/                          ← Core Simple Language Parsing
│   ├── lexer.spl                     (1,268 L) ✅ CANONICAL Simple lexer
│   ├── lexer_types.spl               Token type definitions
│   ├── parser.spl                    (1,813 L) ✅ CANONICAL Simple parser
│   ├── parser_types.spl              AST type definitions
│   ├── treesitter.spl                (1,444 L) ✅ CANONICAL outline parser
│   ├── treesitter_types.spl          Outline type definitions
│   ├── parser/
│   │   └── treesitter.spl            (509 L)   ✅ Lightweight outline (LSP/IDE)
│   ├── predicate_parser.spl          (251 L)   ✅ Predicate sublanguage
│   └── irdsl/
│       └── parser.spl                (147 L)   ✅ IR DSL parser
│
├── std/
│   └── sdn/                           ← SDN Format Parsing
│       ├── lexer.spl                 (411 L)   ✅ SDN format lexer
│       └── parser.spl                (683 L)   ✅ SDN format parser
│
└── app/
    ├── interpreter/
    │   └── parser.spl                (65 L)    ✅ TreeSitter wrapper (convenience)
    ├── depgraph/
    │   └── parser.spl                (271 L)   ✅ Import scanner (tool)
    ├── ffi_gen/
    │   └── parser.spl                (310 L)   ✅ Annotation scanner (tool)
    ├── test_runner_new/
    │   └── test_db_parser.spl        (267 L)   ✅ Test DB parser (tool)
    └── parser/
        └── lexer.spl                 (1,654 L) ⚠️ DUPLICATE (to be merged)
```

**Total:** 7,847 lines across 13 files

---

## File Categorization

### Category A: Core Language (Simple Syntax)

These parse Simple language source code. Only ONE of each should exist.

| File | Lines | Purpose | Status |
|------|-------|---------|--------|
| `compiler/lexer.spl` | 1,268 | Simple tokenization | ✅ CANONICAL |
| `compiler/parser.spl` | 1,813 | Simple AST parsing | ✅ CANONICAL |
| `compiler/treesitter.spl` | 1,444 | Simple outline (compiler) | ✅ CANONICAL |
| `compiler/parser/treesitter.spl` | 509 | Simple outline (LSP/IDE) | ✅ KEEP (different use case) |
| `app/parser/lexer.spl` | 1,654 | Simple tokenization | ⚠️ DUPLICATE → MERGE |

**Action:** Merge `app/parser/lexer.spl` into `compiler/lexer.spl`

---

### Category B: Other Languages (Not Simple)

These parse other languages/formats. Each is unique, NOT a duplicate.

| File | Lines | Language | Purpose |
|------|-------|----------|---------|
| `std/sdn/parser.spl` | 683 | SDN | Config/data format |
| `std/sdn/lexer.spl` | 411 | SDN | Config/data tokenization |
| `compiler/irdsl/parser.spl` | 147 | IR DSL | MIR instruction definitions |
| `compiler/predicate_parser.spl` | 251 | Predicate | Type-level predicates |

**Action:** Keep all (different languages)

---

### Category C: Specialized Tools (Simple Language, But Limited)

These parse Simple source but only extract specific information, not full AST.

| File | Lines | What It Extracts | Why Separate |
|------|-------|-----------------|--------------|
| `app/depgraph/parser.spl` | 271 | Import declarations | Lightweight scanner, no full parse |
| `app/ffi_gen/parser.spl` | 310 | @Lib annotations | Line-based scanning, no AST |
| `app/test_runner_new/test_db_parser.spl` | 267 | Test database format | Different format (test DB) |

**Action:** Keep all (specialized extraction, not full parsing)

---

### Category D: Convenience Wrappers (Thin Layer)

These wrap existing parsers with simpler APIs, no duplication of logic.

| File | Lines | Wraps | Why It Exists |
|------|-------|-------|---------------|
| `app/interpreter/parser.spl` | 65 | `parser.treesitter.parser.TreeSitterParser` | Result-based API for interpreter |

**Action:** Keep (thin wrapper, not duplicate)

---

## Import Patterns

### Current (Before Merge)

```simple
# Compiler uses compiler lexer (correct)
use compiler.lexer.{Lexer}

# Some files use app lexer (incorrect - duplicate)
use app.parser.lexer.{Lexer}

# Both exist, causing confusion!
```

### After Merge (Target State)

```simple
# All files use compiler lexer
use compiler.lexer.{Lexer}

# app.parser.lexer no longer exists
```

---

## Detailed File Descriptions

### 1. `src/compiler/lexer.spl` (1,268 lines)

**Purpose:** Tokenize Simple source code into token stream

**Features:**
- Full Unicode support
- String interpolation (f-strings)
- Indentation tracking (INDENT/DEDENT)
- Math block mode (enables `^` operator)
- Block system integration
- Generic depth tracking (for `>>` disambiguation)
- Implicit multiplication detection
- Error recovery

**Used By:**
- `compiler/parser.spl` - Full AST parsing
- `compiler/treesitter.spl` - Outline parsing
- Any tool needing tokenization

**API:**
```simple
impl Lexer:
    static fn new(source: text) -> Lexer
    static fn with_registry(source, registry) -> Lexer
    me next_token() -> Token
```

---

### 2. `src/app/parser/lexer.spl` (1,654 lines) ⚠️ DUPLICATE

**Purpose:** Tokenize Simple source code (DUPLICATE of compiler/lexer.spl)

**Differences:**
- Uses `class` instead of `struct`
- Has `pending_tokens` buffer
- Has `force_indentation_depth` feature
- No math block support
- No block registry integration
- Simpler (less features)

**Status:** ⚠️ **TO BE MERGED** into `compiler/lexer.spl`

**Migration Plan:**
1. Audit unique features (`pending_tokens`, `force_indentation_depth`)
2. Migrate to `compiler/lexer.spl` if needed
3. Update all imports: `app.parser.lexer` → `compiler.lexer`
4. Delete this file

---

### 3. `src/compiler/parser.spl` (1,813 lines)

**Purpose:** Parse Simple source into full AST

**Strategy:** Two-pass
1. Use TreeSitter for outline (fast)
2. Parse full bodies (detailed)

**Features:**
- Complete expression parsing
- Statement parsing
- Type expression parsing
- Pattern matching
- Block expressions

**Used By:**
- `compiler/driver.spl` - Main compilation
- Any tool needing full AST

**API:**
```simple
impl Parser:
    static fn new(source: text) -> Parser
    static fn with_resolved_blocks(source, resolved) -> Parser
    me parse() -> Module
```

---

### 4. `src/compiler/treesitter.spl` (1,444 lines)

**Purpose:** Fast outline parsing for compiler

**Features:**
- Extracts: imports, exports, functions, classes, structs, enums, traits, impls
- Doc comment accumulation
- Block outline extraction
- Fast mode (skip Skippable blocks)
- Error collection

**Used By:**
- `compiler/parser.spl` - Two-pass parsing
- `compiler/driver.spl` - Outline-only compilation

**API:**
```simple
impl TreeSitter:
    static fn new(source: text) -> TreeSitter
    static fn with_fast_mode(fast_mode: bool) -> TreeSitter
    me parse_outline() -> OutlineModule
```

---

### 5. `src/compiler/parser/treesitter.spl` (509 lines)

**Purpose:** Lightweight outline parsing for LSP/IDE

**Differences from main TreeSitter:**
- **Heuristic-based** (uses line scanning, not full lexer)
- More LSP/IDE focused (error regions, incremental updates)
- Simpler, faster (no full token stream)
- Tolerant of syntax errors

**Features:**
- Outline extraction (declarations without full bodies)
- Error region detection
- Incremental parsing support
- Indentation-based heuristics

**Used By:**
- LSP server (when implemented)
- IDE features (outline view, navigation)

**API:**
```simple
class OutlineParser:
    static fn from_source(source: text) -> OutlineParser
    me parse() -> [OutlineItem]
```

**Why Keep Separate:**
- Different algorithm (heuristic vs full tokenization)
- Different use case (IDE speed vs compiler accuracy)
- Both implementations are valid for their purposes

---

### 6. `src/lib/sdn/parser.spl` (683 lines)

**Purpose:** Parse SDN data format

**Language:** SDN (not Simple)

**Example:**
```sdn
package:
  name: myproject
  version: 1.0.0
```

**Used By:**
- Package manifest loading
- Config file parsing
- Data file parsing

**API:**
```simple
fn parse(source: text) -> Result<SdnValue, SdnError>
fn parse_file(path: text) -> Result<SdnValue, SdnError>
```

---

### 7. `src/lib/sdn/lexer.spl` (411 lines)

**Purpose:** Tokenize SDN format

**Language:** SDN (not Simple)

**Features:**
- INDENT/DEDENT tracking
- Table format support
- Key-value pairs

**Used By:**
- `std/sdn/parser.spl` - SDN parsing

**API:**
```simple
impl Lexer:
    static fn from_source(source: text) -> Lexer
    me tokenize() -> [Token]
```

---

### 8. `src/compiler/irdsl/parser.spl` (147 lines)

**Purpose:** Parse .irdsl files defining MIR instructions

**Language:** IR DSL (not Simple)

**Example:**
```irdsl
instruction Add:
  params: lhs: Value, rhs: Value
  backend: cranelift, interpreter
```

**Used By:**
- `compiler/mir_lowering.spl` - MIR instruction generation

---

### 9. `src/compiler/predicate_parser.spl` (251 lines)

**Purpose:** Parse predicate expressions in type constraints

**Language:** Predicate logic (Simple sublanguage)

**Example:**
```simple
fn sort<T where T: Ord>(items: [T]) -> [T]
#           ^^^^^^^^^^^^^ predicate
```

**Used By:**
- `compiler/type_checker.spl` - Type constraint checking

---

### 10. `src/app/depgraph/parser.spl` (271 lines)

**Purpose:** Extract import declarations for dependency analysis

**Strategy:** Lightweight scanning (no full parse)

**What It Extracts:**
```simple
use std.io.file
import parser.treesitter.{Tree}
common use std.collections.*
```

**Used By:**
- `app/depgraph/` - Dependency graph generation

---

### 11. `src/app/ffi_gen/parser.spl` (310 lines)

**Purpose:** Extract @Lib annotations and extern declarations

**Strategy:** Line-based scanning (no AST)

**What It Extracts:**
```simple
@Lib(rust: "reqwest", version: "0.11")
extern class HttpClient:
    static fn new() -> HttpClient
```

**Used By:**
- `app/ffi_gen/` - FFI wrapper generation

---

### 12. `src/app/test_runner_new/test_db_parser.spl` (267 lines)

**Purpose:** Parse test database format

**Format:** Custom test DB format (not Simple, not SDN)

**Used By:**
- `app/test_runner_new/` - Test result tracking

---

### 13. `src/app/interpreter/parser.spl` (65 lines)

**Purpose:** Thin wrapper for interpreter to use TreeSitter

**What It Wraps:**
```simple
import parser.treesitter.parser.{TreeSitterParser}
```

**API:**
```simple
impl SimpleParser:
    static fn new() -> SimpleParser
    fn parse(source: String) -> Result<Tree, ParseError>
    fn parse_expression(source) -> Result<Tree, ParseError>
    fn parse_statement(source) -> Result<Tree, ParseError>
```

**Why Keep:**
- Thin wrapper (does NOT duplicate parsing logic)
- Provides Result-based API
- No algorithmic duplication

---

## Statistics

### By Category

| Category | Files | Lines | Status |
|----------|-------|-------|--------|
| Core Language (Simple) | 5 | 6,688 | 1 duplicate to merge |
| Other Languages | 4 | 1,492 | Keep all |
| Specialized Tools | 3 | 848 | Keep all |
| Convenience Wrappers | 1 | 65 | Keep |
| **TOTAL** | **13** | **7,847** | |

### Duplications

| Component | Primary | Duplicate | Overlap | Action |
|-----------|---------|-----------|---------|--------|
| **Lexer** | `compiler/lexer.spl` (1,268 L) | `app/parser/lexer.spl` (1,654 L) | ~70% | Merge |
| **TreeSitter** | `compiler/treesitter.spl` (1,444 L) | `compiler/parser/treesitter.spl` (509 L) | ~40% | Keep both (different use cases) |

**Total duplicated code:** ~1,200-1,500 lines (from lexer only)

---

## Migration Checklist

### Files to Keep (Post-Merge)

- [x] `compiler/lexer.spl` - ✅ CANONICAL Simple lexer
- [x] `compiler/parser.spl` - ✅ CANONICAL Simple parser
- [x] `compiler/treesitter.spl` - ✅ CANONICAL outline parser (compiler)
- [x] `compiler/parser/treesitter.spl` - ✅ Lightweight outline parser (LSP)
- [x] `std/sdn/parser.spl` - ✅ SDN parser
- [x] `std/sdn/lexer.spl` - ✅ SDN lexer
- [x] `compiler/irdsl/parser.spl` - ✅ IR DSL parser
- [x] `compiler/predicate_parser.spl` - ✅ Predicate parser
- [x] `app/depgraph/parser.spl` - ✅ Import scanner
- [x] `app/ffi_gen/parser.spl` - ✅ Annotation scanner
- [x] `app/test_runner_new/test_db_parser.spl` - ✅ Test DB parser
- [x] `app/interpreter/parser.spl` - ✅ TreeSitter wrapper

### Files to Remove (Post-Merge)

- [ ] `app/parser/lexer.spl` - ❌ DELETE (merge into compiler/lexer.spl)

### Imports to Update

```bash
# Find all imports of old lexer
grep -r "app\.parser\.lexer" src/ test/

# Update to new import
# OLD: use app.parser.lexer.{Lexer}
# NEW: use compiler.lexer.{Lexer}
```

---

## Quick Start (For New Contributors)

### "I want to tokenize Simple code"

```simple
use compiler.lexer.{Lexer}

val lexer = Lexer.new("fn main(): print 'Hello'")
val tokens = lexer.tokenize()
```

### "I want to parse Simple code (full AST)"

```simple
use compiler.parser.{Parser}

val parser = Parser.new(source)
val module = parser.parse()
```

### "I want to get outline only (fast)"

```simple
use compiler.treesitter.{TreeSitter}

val ts = TreeSitter.new(source)
val outline = ts.parse_outline()
# outline has: imports, exports, functions, classes, ...
```

### "I want to parse SDN config file"

```simple
use std.sdn.parser.{parse_file}

match parse_file("config.sdn"):
    case Ok(value): process(value)
    case Err(e): print "Error: {e}"
```

### "I want to extract imports from .spl file"

```simple
use app.depgraph.parser.{extract_imports}

val imports = extract_imports(source)
```

---

## Related Documentation

- **Duplication Analysis:** `doc/research/parser_duplication_analysis_2026-02-04.md`
- **Architecture Design:** `doc/design/parser_architecture_unified_2026-02-04.md`
- **Merge Plan:** `doc/plan/parser_merge_plan_2026-02-04.md`
- **File Tree:** `doc/architecture/file_tree.md` (if exists)
- **Compiler Architecture:** `doc/guide/compiler_architecture.md` (if exists)

---

**Last Updated:** 2026-02-04
**Status:** ✅ Complete - Ready for merge implementation
