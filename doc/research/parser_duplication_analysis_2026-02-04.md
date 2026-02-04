# Parser/Lexer/TreeSitter Duplication Analysis

**Date:** 2026-02-04
**Status:** Research Complete - Merge Plan Ready

## Executive Summary

Found **8 parser implementations**, **4 lexer implementations**, and **2 treesitter implementations** across the codebase, totaling **7,847 lines** of potentially duplicated code.

**Key Findings:**
- **2 full compiler parsers** (compiler + app/interpreter) - **1,878 lines**
- **2 full lexers** (compiler + app/parser) - **2,922 lines**
- **2 treesitter implementations** (compiler + compiler/parser) - **1,953 lines**
- **6 specialized parsers** for specific formats - **1,246 lines**

**Recommendation:** Merge duplicated compiler components, keep specialized parsers separate.

---

## Detailed Analysis

### Category A: Full Language Parsers (Merge Candidates)

#### 1. Main Compiler Parser

**Location:** `src/compiler/parser.spl`
**Size:** 1,813 lines
**Purpose:** Primary compiler parser
**Features:**
- Full Simple language parsing
- Uses TreeSitter for outline, then detailed token parse
- Two-pass: outline → full bodies
- AST type definitions in `parser_types.spl`
- Imports: `lexer.*`, `treesitter.*`, `blocks.*`, `parser_types.*`

**Key Methods:**
```simple
impl Parser:
    static fn new(source: text) -> Parser
    static fn with_resolved_blocks(source, resolved) -> Parser
    me parse() -> Module
    me parse_full() -> Module
    me parse_function_body(outline) -> Function
    me parse_class_body(outline) -> Class
```

**Status:** ✅ Primary - Keep as canonical

---

#### 2. Interpreter Parser Wrapper

**Location:** `src/app/interpreter/parser.spl`
**Size:** 65 lines
**Purpose:** Wrapper for interpreter to use TreeSitter
**Features:**
- Thin wrapper around `parser.treesitter.parser.TreeSitterParser`
- Simple API: `parse()`, `parse_expression()`, `parse_statement()`
- Error handling with `ParseError` enum
- Does NOT duplicate parser logic, just wraps existing TreeSitter

**Key Methods:**
```simple
impl SimpleParser:
    static fn new() -> SimpleParser
    fn parse(source: String) -> Result<Tree, ParseError>
    fn parse_expression(source) -> Result<Tree, ParseError>
    fn parse_statement(source) -> Result<Tree, ParseError>
```

**Duplication:** ❌ **NOT duplicated** - this is a wrapper, not a duplicate implementation

**Action:** ✅ Keep as-is (lightweight wrapper for interpreter convenience)

---

### Category B: Full Language Lexers (Merge Candidates)

#### 1. Main Compiler Lexer

**Location:** `src/compiler/lexer.spl`
**Size:** 1,268 lines
**Purpose:** Primary compiler lexer
**Features:**
- Full Unicode support
- String interpolation
- Indentation tracking (INDENT/DEDENT tokens)
- Math block support (enables `^` operator)
- Block system integration (lazy-loaded registry)
- Generic depth tracking for `>>` disambiguation
- Implicit multiplication detection

**Key State:**
```simple
struct Lexer:
    source, pos, line, col
    indent_stack: [i64]
    paren_depth, in_math_block, math_brace_depth
    generic_depth
    block_registry, current_block_kind, current_lexer_mode
```

**Status:** ✅ Primary - Keep as canonical

---

#### 2. App Parser Lexer

**Location:** `src/app/parser/lexer.spl`
**Size:** 1,654 lines
**Purpose:** Parser for app/tool use (potentially older implementation)
**Features:**
- Full tokenization
- Indentation tracking
- String interpolation (`FStringToken`)
- Force indentation mode
- Bracket depth tracking

**Key State:**
```simple
class Lexer:
    source, pos, line, column
    indent_stack: [i64]
    pending_tokens: [Token]
    at_line_start, bracket_depth
    force_indentation_depth
```

**Differences from compiler lexer:**
- Uses `class` instead of `struct`
- Has `pending_tokens` buffer
- Has `force_indentation_depth` (compiler uses `block_brace_depth`)
- No math block support
- No block registry integration
- Simpler overall (no generics tracking, no block modes)

**Duplication:** ⚠️ **~70% duplicated** - Core tokenization logic is similar

**Action:** 🔄 **MERGE** - Migrate unique features to compiler lexer, remove this file

---

### Category C: TreeSitter Implementations (Merge Candidates)

#### 1. Main Compiler TreeSitter

**Location:** `src/compiler/treesitter.spl`
**Size:** 1,444 lines
**Purpose:** Outline parser for compiler
**Features:**
- Fast outline parsing (structure without full parse)
- Extracts: imports, exports, functions, classes, structs, enums, traits, impls
- Doc comment accumulation
- Block outline extraction
- Fast mode (skip Skippable blocks)
- Block registry integration

**Key Methods:**
```simple
impl TreeSitter:
    static fn new(source) -> TreeSitter
    static fn with_fast_mode(fast_mode) -> TreeSitter
    me parse_outline() -> OutlineModule
```

**Status:** ✅ Primary - Keep as canonical

---

#### 2. Compiler Parser TreeSitter Module

**Location:** `src/compiler/parser/treesitter.spl`
**Size:** 509 lines
**Purpose:** Shared outline parsing for compiler/interpreter/LSP
**Features:**
- Outline parsing (extract declarations without full AST)
- Error region detection
- Incremental parsing support
- Indentation-based heuristics
- **More lightweight** than main treesitter

**Key Types:**
```simple
enum OutlineKind: Function, Method, Class, Struct, Enum, ...
struct OutlineItem: kind, name, line, column, visibility, ...
class OutlineParser: Fast outline extraction
```

**Differences:**
- **Heuristic-based** (uses line scanning, not full lexer)
- More LSP/IDE focused (error regions, incremental updates)
- Simpler, faster (no full token stream)
- Tolerant of syntax errors

**Duplication:** ⚠️ **~40% overlapping functionality**

**Action:** 🔄 **DECIDE** - Either:
1. Keep both (different use cases: compiler vs IDE)
2. Merge into unified implementation with modes
3. Use lightweight version for IDE, full version for compiler

---

### Category D: Specialized Parsers (Keep Separate)

These parsers handle specific formats/languages, NOT Simple language. They are domain-specific and should remain separate.

#### 1. SDN Parser

**Location:** `src/std/sdn/parser.spl`
**Size:** 683 lines
**Purpose:** Parse SDN data format (Simple's config/data format)
**Language:** SDN (not Simple)
**Action:** ✅ Keep separate (different language)

---

#### 2. SDN Lexer

**Location:** `src/std/sdn/lexer.spl`
**Size:** 411 lines
**Purpose:** Tokenize SDN format
**Language:** SDN (not Simple)
**Action:** ✅ Keep separate (different language)

---

#### 3. Dependency Graph Parser

**Location:** `src/app/depgraph/parser.spl`
**Size:** 271 lines
**Purpose:** Extract imports from .spl files for dependency analysis
**Features:** Lightweight import extraction (no full parsing)
**Action:** ✅ Keep separate (specialized tool)

---

#### 4. FFI Gen Parser

**Location:** `src/app/ffi_gen/parser.spl`
**Size:** 310 lines
**Purpose:** Parse @Lib annotations and extern class declarations
**Features:** Line-based scanning (no AST dependency)
**Action:** ✅ Keep separate (specialized tool, simple line scanner)

---

#### 5. Test DB Parser

**Location:** `src/app/test_runner_new/test_db_parser.spl`
**Size:** 267 lines
**Purpose:** Parse test database format
**Action:** ✅ Keep separate (specialized format)

---

#### 6. IR DSL Parser

**Location:** `src/compiler/irdsl/parser.spl`
**Size:** 147 lines
**Purpose:** Parse .irdsl files defining MIR instructions
**Language:** IR DSL (not Simple)
**Action:** ✅ Keep separate (different language)

---

#### 7. Predicate Parser

**Location:** `src/compiler/predicate_parser.spl`
**Size:** 251 lines
**Purpose:** Parse predicate expressions for type system
**Action:** ✅ Keep separate (specialized sublanguage)

---

## Summary Table

| File | Lines | Category | Status | Action |
|------|-------|----------|--------|--------|
| `src/compiler/parser.spl` | 1,813 | Full Parser | ✅ Canonical | Keep |
| `src/app/interpreter/parser.spl` | 65 | Wrapper | ✅ Not Duplicate | Keep |
| `src/compiler/lexer.spl` | 1,268 | Full Lexer | ✅ Canonical | Keep |
| `src/app/parser/lexer.spl` | 1,654 | Full Lexer | ⚠️ 70% Duplicate | **MERGE → compiler** |
| `src/compiler/treesitter.spl` | 1,444 | Outline Parser | ✅ Canonical | Keep |
| `src/compiler/parser/treesitter.spl` | 509 | Outline Parser | ⚠️ 40% Overlap | **DECIDE** |
| `src/std/sdn/parser.spl` | 683 | SDN Format | ✅ Separate Language | Keep |
| `src/std/sdn/lexer.spl` | 411 | SDN Format | ✅ Separate Language | Keep |
| `src/app/depgraph/parser.spl` | 271 | Import Scanner | ✅ Specialized | Keep |
| `src/app/ffi_gen/parser.spl` | 310 | Annotation Scanner | ✅ Specialized | Keep |
| `src/app/test_runner_new/test_db_parser.spl` | 267 | Test DB | ✅ Specialized | Keep |
| `src/compiler/irdsl/parser.spl` | 147 | IR DSL | ✅ Separate Language | Keep |
| `src/compiler/predicate_parser.spl` | 251 | Predicate Lang | ✅ Specialized | Keep |
| **TOTAL** | **7,847** | | | |

---

## Duplication Statistics

### True Duplications (Need Action)

| Component | Primary | Duplicate | Overlap | Action |
|-----------|---------|-----------|---------|--------|
| **Lexer** | `compiler/lexer.spl` (1,268 L) | `app/parser/lexer.spl` (1,654 L) | ~70% | Merge → compiler |
| **TreeSitter** | `compiler/treesitter.spl` (1,444 L) | `compiler/parser/treesitter.spl` (509 L) | ~40% | Decide (see below) |

**Total duplicated code:** ~2,000-2,500 lines

### Non-Duplications (Keep Separate)

- **Interpreter wrapper** (65 lines) - Thin wrapper, not a duplicate
- **Specialized parsers** (1,246 lines) - Different languages/formats
- **SDN parsers** (1,094 lines) - Completely separate language

---

## Merge Plan

### Phase 1: Lexer Consolidation (High Priority)

**Goal:** Single canonical lexer in `src/compiler/lexer.spl`

**Steps:**

1. **Audit unique features in `app/parser/lexer.spl`:**
   - `pending_tokens` buffer mechanism
   - `force_indentation_depth` feature
   - Any unique token kinds or error messages

2. **Migrate useful features to `compiler/lexer.spl`:**
   - If `pending_tokens` is useful, add to compiler lexer
   - If `force_indentation_depth` is needed, integrate

3. **Update all references:**
   ```bash
   # Find all imports of app/parser/lexer
   grep -r "from.*app\.parser\.lexer" src/
   grep -r "use.*app\.parser\.lexer" src/
   ```

4. **Replace with compiler lexer:**
   ```simple
   # OLD:
   from app.parser.lexer import Lexer

   # NEW:
   from compiler.lexer import Lexer
   ```

5. **Delete `src/app/parser/lexer.spl`**

6. **Verify tests pass:**
   ```bash
   simple test --tag=lexer
   simple test --tag=parser
   ```

**Estimated effort:** 2-3 hours
**Risk:** Low (lexer is well-tested)

---

### Phase 2: TreeSitter Consolidation (Medium Priority)

**Goal:** Decide whether to merge or keep separate

**Option A: Keep Both (Recommended)**

**Rationale:**
- `compiler/treesitter.spl` - Full outline parser for compiler (uses lexer, comprehensive)
- `compiler/parser/treesitter.spl` - Lightweight heuristic parser for LSP/IDE (tolerant, fast)
- Different use cases justify separate implementations

**Action:**
1. Rename for clarity:
   - `compiler/treesitter.spl` → `compiler/outline_parser.spl`
   - `compiler/parser/treesitter.spl` → `compiler/ide/outline_heuristic.spl`
2. Document distinction in comments
3. Keep both

**Estimated effort:** 1 hour (renaming + docs)

**Option B: Merge with Modes**

**Rationale:**
- Combine into single implementation with `fast_mode` flag
- `fast_mode=true` → Heuristic parsing (IDE)
- `fast_mode=false` → Full parsing (compiler)

**Action:**
1. Merge implementations into `compiler/outline_parser.spl`
2. Add mode selection logic
3. Update all references
4. Delete duplicate file

**Estimated effort:** 4-6 hours
**Risk:** Medium (need to ensure both modes work correctly)

**Recommendation:** **Choose Option A** (keep both) - Different use cases justify separate implementations.

---

### Phase 3: Update Documentation (High Priority)

**Goal:** Document final structure in file location docs

**Files to Update:**

1. **`doc/architecture/file_tree.md`** (if exists)
   - Document canonical parser/lexer locations
   - List specialized parsers with their purposes

2. **`doc/guide/compiler_architecture.md`** (if exists)
   - Update parser/lexer architecture diagrams
   - Document single lexer, single parser

3. **Create new documentation:**
   - `doc/architecture/parser_lexer_structure.md` - Comprehensive guide

**Estimated effort:** 2 hours

---

## File Location Reference (Post-Merge)

### Compiler Core (Simple Language Parsing)

```
src/compiler/
├── lexer.spl                    (1,268 lines) - ✅ CANONICAL Simple lexer
├── lexer_types.spl              - Token types for lexer
├── parser.spl                   (1,813 lines) - ✅ CANONICAL Simple parser
├── parser_types.spl             - AST types for parser
├── treesitter.spl               (1,444 lines) - ✅ CANONICAL outline parser (compiler)
├── treesitter_types.spl         - Outline types
└── parser/
    └── treesitter.spl           (509 lines)   - ✅ KEEP Lightweight outline (IDE/LSP)
```

### Specialized Parsers (Domain-Specific)

```
src/std/sdn/
├── parser.spl                   (683 lines)   - ✅ SDN format parser
└── lexer.spl                    (411 lines)   - ✅ SDN format lexer

src/compiler/
├── irdsl/parser.spl             (147 lines)   - ✅ IR DSL parser
└── predicate_parser.spl         (251 lines)   - ✅ Predicate language parser

src/app/
├── depgraph/parser.spl          (271 lines)   - ✅ Import scanner (tool)
├── ffi_gen/parser.spl           (310 lines)   - ✅ Annotation scanner (tool)
├── test_runner_new/test_db_parser.spl  (267 lines) - ✅ Test DB parser (tool)
└── interpreter/parser.spl       (65 lines)    - ✅ TreeSitter wrapper (convenience)
```

### Removed (After Merge)

```
src/app/parser/
└── lexer.spl                    (1,654 lines) - ❌ DELETE after merge
```

---

## Migration Checklist

### Pre-Merge Audit

- [x] Identify all lexer implementations
- [x] Identify all parser implementations
- [x] Identify all treesitter implementations
- [x] Count line duplications
- [x] Categorize by purpose (compiler vs specialized)
- [ ] Audit unique features in `app/parser/lexer.spl`
- [ ] List all imports of `app/parser/lexer`
- [ ] Check for test dependencies on duplicate lexer

### Lexer Merge

- [ ] Copy unique features from `app/parser/lexer.spl` to `compiler/lexer.spl`
- [ ] Update all imports: `app.parser.lexer` → `compiler.lexer`
- [ ] Run tests: `simple test --tag=lexer`
- [ ] Delete `src/app/parser/lexer.spl`
- [ ] Commit: "refactor: Merge duplicate lexer into compiler/lexer.spl"

### TreeSitter Decision

- [ ] Decide: Option A (keep both) or Option B (merge with modes)
- [ ] If Option A: Rename files for clarity, update docs
- [ ] If Option B: Merge implementations, add mode flag
- [ ] Run tests: `simple test --tag=treesitter`
- [ ] Commit: "refactor: Consolidate treesitter implementations"

### Documentation

- [ ] Create `doc/architecture/parser_lexer_structure.md`
- [ ] Update `doc/architecture/file_tree.md` (if exists)
- [ ] Update `doc/guide/compiler_architecture.md` (if exists)
- [ ] Add comments in canonical files explaining they are the single source
- [ ] Commit: "docs: Document parser/lexer/treesitter architecture"

### Verification

- [ ] Run full test suite: `simple test`
- [ ] Run Rust tests: `simple build rust test`
- [ ] Check no broken imports: `simple build --release`
- [ ] Verify LSP still works (if applicable)
- [ ] Run linter: `simple lint src/compiler/`

---

## TODOs for Difficult Merges

### TODO: Lexer Force Indentation

**Location:** `src/app/parser/lexer.spl:40-45`

```simple
me enable_forced_indentation():
    self.force_indentation_depth = self.force_indentation_depth + 1

me disable_forced_indentation():
    if self.force_indentation_depth > 0:
        self.force_indentation_depth = self.force_indentation_depth - 1
```

**Question:** Is this feature used anywhere? If so, migrate to compiler lexer.

**Action:** Search for usage:
```bash
grep -r "enable_forced_indentation\|disable_forced_indentation" src/
```

---

### TODO: Lexer Pending Tokens

**Location:** `src/app/parser/lexer.spl:23,47-55`

```simple
pending_tokens: [Token]

fn tokenize() -> [Token]:
    var tokens_: [Token] = []
    loop:
        val tok = self.next_token()
        val is_eof = tok.kind is TokenKind.Eof
        tokens_.push(tok)
        if is_eof:
            break
    tokens_
```

**Question:** Does compiler lexer need a `tokenize()` convenience method?

**Action:** Check if `compiler/lexer.spl` has equivalent functionality. If not, add.

---

### TODO: TreeSitter Error Recovery

**Location:** `src/compiler/parser/treesitter.spl:96-140`

The lightweight treesitter has error region detection:

```simple
enum ErrorSeverity: Error, Warning, Info
struct ErrorRegion: line, column, end_line, message, severity
```

**Question:** Should compiler treesitter also report error regions?

**Action:** Consider adding error region reporting to `compiler/treesitter.spl` for better IDE integration.

---

### TODO: TreeSitter Incremental Parsing

**Location:** `src/compiler/parser/treesitter.spl:142-200`

The lightweight treesitter has incremental update support:

```simple
class IncrementalParser:
    fn apply_edit(range: EditRange) -> ParseResult
```

**Question:** Should compiler treesitter support incremental updates?

**Action:** If LSP/IDE features are added to compiler, migrate incremental parsing logic.

---

## Risks and Mitigation

### Risk 1: Breaking Existing Code

**Impact:** High - Lexer is used throughout codebase
**Probability:** Medium - Many imports to update

**Mitigation:**
1. Use grep to find all imports before changing
2. Update all imports in single commit
3. Run full test suite before committing
4. Have rollback plan (git revert)

---

### Risk 2: Missing Unique Features

**Impact:** High - Lose functionality
**Probability:** Low - Careful audit will catch

**Mitigation:**
1. Line-by-line comparison of `app/parser/lexer.spl` vs `compiler/lexer.spl`
2. Check for methods/fields in duplicate not in canonical
3. Migrate or document reason for omission

---

### Risk 3: Test Failures

**Impact:** Medium - Tests may depend on duplicate lexer behavior
**Probability:** Medium - Some tests may use app/parser/lexer directly

**Mitigation:**
1. Run tests before and after merge
2. Fix any failures by updating test imports
3. Ensure behavior is identical (or intentionally different)

---

## Success Criteria

- [ ] Only one Simple language lexer: `compiler/lexer.spl`
- [ ] Only one Simple language parser: `compiler/parser.spl`
- [ ] TreeSitter architecture documented (either merged or kept separate with clear rationale)
- [ ] All tests pass: `simple test` and `simple build rust test`
- [ ] No duplicate implementations of core language parsing
- [ ] Specialized parsers clearly documented as separate (SDN, IR DSL, etc.)
- [ ] File location documentation updated

---

## Timeline

| Phase | Duration | Effort |
|-------|----------|--------|
| Phase 1: Lexer Merge | 2-3 hours | Medium |
| Phase 2: TreeSitter Decision | 1-6 hours | Low-Medium (depends on option) |
| Phase 3: Documentation | 2 hours | Low |
| **Total** | **5-11 hours** | **Medium** |

**Recommended schedule:**
- Day 1: Lexer merge (Phase 1)
- Day 2: TreeSitter decision + documentation (Phase 2-3)

---

## References

**Related Documents:**
- `doc/report/compiler_components_found_2026-02-04.md` - Compiler component inventory
- `doc/report/runtime_minimal_2026-02-04.md` - Runtime architecture analysis
- `doc/report/rust_removed_2026-02-04.md` - Rust folder removal summary

**Source Files:**
- `src/compiler/lexer.spl` - Canonical lexer
- `src/compiler/parser.spl` - Canonical parser
- `src/compiler/treesitter.spl` - Canonical outline parser
- `src/app/parser/lexer.spl` - Duplicate lexer (to be removed)
- `src/compiler/parser/treesitter.spl` - Lightweight outline parser (keep or merge)

---

**Status:** ✅ Research Complete - Ready for implementation

**Next Action:** Begin Phase 1 (Lexer Merge) after user approval
