# TreeSitter Heuristic Mode Merge Plan

**Date:** 2026-02-04
**Goal:** Add error-tolerant line-based parsing to heavyweight TreeSitter
**Effort:** 4-6 hours
**Risk:** Medium

---

## Overview

Merge the lightweight line-based algorithm into `compiler/treesitter.spl` to enable error-tolerant parsing for LSP/IDE use cases.

**Key Benefit:** Tolerant of syntax errors - always produces results even with broken code.

---

## Current State

### Heavyweight TreeSitter (compiler/treesitter.spl)
- Token-based parsing with full Lexer
- Strict error handling
- Rich `OutlineModule` output
- Has `fast_mode` (skips blocks, still uses Lexer)
- **Used by:** compiler/driver.spl, compiler/driver_types.spl

### Lightweight OutlineParser (compiler/parser/treesitter.spl)
- Line-based heuristic scanning
- **Error-tolerant** - always produces results
- Simple `[OutlineItem]` output
- **Used by:** Nobody (dead code)

---

## Target Architecture

```simple
struct TreeSitter:
    # ... existing fields
    fast_mode: bool          # Skip Skippable blocks (existing)
    heuristic_mode: bool     # Use line-based algorithm (NEW)

impl TreeSitter:
    static fn with_heuristic_mode(enabled: bool) -> TreeSitter

    me parse_outline() -> OutlineModule:
        if self.heuristic_mode:
            self.parse_outline_heuristic()  # Line-based, error-tolerant
        else:
            self.parse_outline_token_based()  # Token-based, strict

    # Port from OutlineParser
    me parse_outline_heuristic() -> OutlineModule:
        val lines = self.lexer.source.split("\n")
        var items = []
        # ... line-based parsing logic
        self.convert_items_to_module(items)

    me convert_items_to_module(items: [OutlineItem]) -> OutlineModule:
        # Convert lightweight OutlineItem to rich OutlineModule
```

---

## Implementation Steps

### Phase 1: Add Field and API (30 min)

**Step 1.1: Add `heuristic_mode` field**

Location: `src/compiler/treesitter.spl:20-30`

```simple
struct TreeSitter:
    # ... existing fields
    fast_mode: bool         # If true, skip Skippable blocks
    heuristic_mode: bool    # If true, use line-based error-tolerant parsing (NEW)
    registry: BlockRegistry?
```

**Step 1.2: Update constructors**

Add to `TreeSitter.new()`:
```simple
heuristic_mode: false,  # Default to token-based
```

Add new constructor:
```simple
static fn with_heuristic_mode(enabled: bool) -> TreeSitter:
    """Create TreeSitter with heuristic mode for error-tolerant parsing.

    Heuristic mode uses line-based scanning instead of full lexer tokenization.
    Always produces results, even with syntax errors.
    Ideal for LSP/IDE use where speed and tolerance matter more than accuracy.
    """
    var ts = TreeSitter.new("")
    ts.heuristic_mode = enabled
    ts
```

---

### Phase 2: Port Helper Types (30 min)

**Step 2.1: Copy OutlineItem type**

From `compiler/parser/treesitter.spl:18-69` copy to top of `compiler/treesitter.spl`:

```simple
# ============================================================================
# Heuristic Mode Types (for line-based parsing)
# ============================================================================

struct OutlineItem:
    """Lightweight outline item for heuristic parsing."""
    kind: OutlineKind
    name: text
    line: i64
    column: i64
    end_line: i64
    visibility: text
    parent: text?
    signature: text?
    children: [OutlineItem]

enum OutlineKind:
    Function | Method | StaticMethod | MutableMethod
    Class | Struct | Enum | EnumVariant
    Trait | Impl | Module
    Import | Export
    Val | Var | Const | TypeAlias
```

**Note:** Check if `OutlineKind` conflicts with existing types in `treesitter_types.spl`.

---

### Phase 3: Port Line-Based Algorithm (2-3 hours)

**Step 3.1: Add branch in `parse_outline()`**

Location: `src/compiler/treesitter.spl:85`

```simple
me parse_outline() -> OutlineModule:
    """Parse source into an outline module."""

    # NEW: Branch based on mode
    if self.heuristic_mode:
        return self.parse_outline_heuristic()

    # Existing token-based parsing
    var module = OutlineModule(
        name: "",
        imports: [],
        # ... existing code
    )
```

**Step 3.2: Port heuristic parsing method**

Copy from `compiler/parser/treesitter.spl:87-109` and adapt:

```simple
me parse_outline_heuristic() -> OutlineModule:
    """Parse outline using line-based heuristics (error-tolerant).

    Uses simple line scanning and pattern matching instead of full tokenization.
    Always produces results, even with syntax errors.
    """
    val lines = self.lexer.source.split("\n")
    var items: [OutlineItem] = []
    var current_impl_target: text? = nil
    var line_num = 0

    while line_num < lines.len():
        val line = lines[line_num]
        val trimmed = line.trim()
        val indent = self.indent_level(line)

        # Skip empty lines and comments
        if trimmed.len() == 0 or trimmed[0] == '#':
            line_num = line_num + 1
            continue

        # Top-level declarations (indent 0)
        if indent == 0:
            current_impl_target = nil
            self.parse_declaration_heuristic(trimmed, line_num + 1, indent, &items, &current_impl_target)

        # Nested members (indent 4 inside impl)
        elif indent == 4 and current_impl_target.?:
            self.parse_member_heuristic(trimmed, line_num + 1, &items)

        line_num = line_num + 1

    # Convert lightweight items to rich OutlineModule
    self.convert_items_to_module(items)
```

**Step 3.3: Port helper methods**

Copy and adapt from `compiler/parser/treesitter.spl:111-end`:

```simple
fn indent_level(line: text) -> i64:
    """Count leading spaces (each 4 spaces = 1 indent level)."""
    var count = 0
    for ch in line:
        if ch == ' ':
            count = count + 1
        else:
            break
    count / 4

me parse_declaration_heuristic(trimmed: text, line: i64, indent: i64,
                                items: &[OutlineItem], impl_target: &text?):
    """Parse a top-level declaration line (heuristic)."""
    # ... port from OutlineParser.parse_declaration

me parse_member_heuristic(trimmed: text, line: i64, items: &[OutlineItem]):
    """Parse a member declaration inside impl/class (heuristic)."""
    # ... port from OutlineParser.parse_member
```

---

### Phase 4: Data Conversion (1-2 hours)

**Step 4.1: Implement converter**

```simple
me convert_items_to_module(items: [OutlineItem]) -> OutlineModule:
    """Convert lightweight OutlineItem list to rich OutlineModule.

    Maps heuristic parsing results to compiler-compatible format.
    Some fields will be empty/placeholder since heuristic parsing is limited.
    """
    var functions: [FunctionOutline] = []
    var classes: [ClassOutline] = []
    var structs: [StructOutline] = []
    var enums: [EnumOutline] = []
    var traits: [TraitOutline] = []
    var impls: [ImplOutline] = []
    var imports: [ImportOutline] = []
    var exports: [ExportOutline] = []
    var type_aliases: [TypeAliasOutline] = []
    var constants: [ConstantOutline] = []

    for item in items:
        match item.kind:
            case OutlineKind.Function | OutlineKind.Method | OutlineKind.StaticMethod:
                functions.push(self.item_to_function(item))
            case OutlineKind.Class:
                classes.push(self.item_to_class(item))
            case OutlineKind.Struct:
                structs.push(self.item_to_struct(item))
            case OutlineKind.Enum:
                enums.push(self.item_to_enum(item))
            case OutlineKind.Trait:
                traits.push(self.item_to_trait(item))
            case OutlineKind.Impl:
                impls.push(self.item_to_impl(item))
            case OutlineKind.Import:
                imports.push(self.item_to_import(item))
            case OutlineKind.Export:
                exports.push(self.item_to_export(item))
            # ... handle other kinds

    OutlineModule(
        name: "",
        imports: imports,
        exports: exports,
        functions: functions,
        classes: classes,
        structs: structs,
        enums: enums,
        traits: traits,
        impls: impls,
        type_aliases: type_aliases,
        constants: constants,
        inline_blocks: [],  # Heuristic mode doesn't track blocks
        errors: []  # Heuristic mode is error-tolerant
    )

# Conversion helpers
me item_to_function(item: OutlineItem) -> FunctionOutline:
    FunctionOutline(
        name: item.name,
        visibility: self.parse_visibility(item.visibility),
        params: [],  # Heuristic mode doesn't parse params
        return_type: nil,
        type_params: [],
        span: Span(line: item.line, col: item.column,
                   end_line: item.end_line, end_col: 0),
        doc: nil
    )

me item_to_class(item: OutlineItem) -> ClassOutline:
    # ... similar conversion

# ... other converters
```

---

### Phase 5: Testing (1 hour)

**Step 5.1: Create test file**

Create `test/lib/std/unit/compiler/treesitter_heuristic_spec.spl`:

```simple
import testing.{describe, it, expect}
use compiler.treesitter.{TreeSitter}

describe "TreeSitter heuristic mode":
    it "parses valid code":
        val source = "fn hello(): print 'hi'"
        val ts = TreeSitter.with_heuristic_mode(true).with_source(source)
        val outline = ts.parse_outline()
        expect(outline.functions.len()).to_equal(1)
        expect(outline.functions[0].name).to_equal("hello")

    it "tolerates syntax errors":
        val source = "fn broken(: # Missing closing paren\nfn works(): 42"
        val ts = TreeSitter.with_heuristic_mode(true).with_source(source)
        val outline = ts.parse_outline()
        # Should still extract 'works' function
        expect(outline.functions.len()).to_be_at_least(1)

    it "handles incomplete code":
        val source = "class MyClass:\n    fn method"
        val ts = TreeSitter.with_heuristic_mode(true).with_source(source)
        val outline = ts.parse_outline()
        expect(outline.classes.len()).to_equal(1)
        expect(outline.errors.len()).to_equal(0)  # Error-tolerant
```

**Step 5.2: Run tests**

```bash
# Test heuristic mode
simple test test/lib/std/unit/compiler/treesitter_heuristic_spec.spl

# Verify existing tests still pass
simple test --tag=treesitter

# Full test suite
simple test
```

---

### Phase 6: Cleanup (15 min)

**Step 6.1: Delete old file**

```bash
rm src/compiler/parser/treesitter.spl
```

**Step 6.2: Remove directory if empty**

```bash
ls src/compiler/parser/
# If empty:
rmdir src/compiler/parser/
```

---

### Phase 7: Documentation (30 min)

**Step 7.1: Update TreeSitter docstring**

```simple
struct TreeSitter:
    """Outline parser for Simple source code.

    Supports two parsing modes:

    1. Token-based (default): Full lexer tokenization, strict parsing
       - High accuracy
       - Proper error reporting
       - Use for: Compilation

    2. Heuristic (optional): Line-based pattern matching, error-tolerant
       - Fast scanning
       - Always produces results (even with errors)
       - Use for: LSP/IDE, incomplete code

    Examples:
        # Strict parsing (compilation)
        val ts = TreeSitter.new(source)
        val outline = ts.parse_outline()

        # Error-tolerant parsing (IDE)
        val ts = TreeSitter.with_heuristic_mode(true).with_source(source)
        val outline = ts.parse_outline()  # Works even with syntax errors
    """
```

**Step 7.2: Update architecture doc**

Update `doc/design/parser_architecture_unified_2026-02-04.md`:

```markdown
### TreeSitter: Two Modes (Not Two Implementations)

#### Mode 1: Token-Based (Default)
- Full lexer tokenization
- Strict error handling
- Use: Compilation

#### Mode 2: Heuristic (Optional)
- Line-based scanning
- Error-tolerant
- Use: LSP/IDE

Both modes in single file: `src/compiler/treesitter.spl`
```

---

## Verification Checklist

- [ ] `heuristic_mode` field added to TreeSitter struct
- [ ] `with_heuristic_mode()` constructor works
- [ ] Line-based parsing algorithm ported
- [ ] Converter from OutlineItem to OutlineModule works
- [ ] Tests pass with heuristic mode
- [ ] Existing token-based tests still pass
- [ ] Old file deleted (compiler/parser/treesitter.spl)
- [ ] Documentation updated
- [ ] Full build succeeds: `simple build --release`
- [ ] All tests pass: `simple test`

---

## Rollback Plan

If merge causes issues:

```bash
# Restore from backup
jj bookmark list
jj checkout backup-before-treesitter-merge

# Or revert specific changes
jj undo
```

---

## Success Criteria

✅ **Single TreeSitter with dual modes:**
- Token-based (strict, for compilation)
- Heuristic (tolerant, for IDE)

✅ **Error tolerance:**
- Heuristic mode always produces results
- Works with incomplete/broken code

✅ **No duplication:**
- Only one TreeSitter file
- Old lightweight file deleted

✅ **Tests pass:**
- New heuristic mode tests
- Existing token-based tests
- Full test suite

---

## Timeline

| Phase | Task | Duration |
|-------|------|----------|
| 1 | Add field and API | 30 min |
| 2 | Port helper types | 30 min |
| 3 | Port line-based algorithm | 2-3 hours |
| 4 | Data conversion | 1-2 hours |
| 5 | Testing | 1 hour |
| 6 | Cleanup | 15 min |
| 7 | Documentation | 30 min |
| **Total** | | **5-7 hours** |

---

**Status:** ✅ Plan Complete - Ready for implementation
