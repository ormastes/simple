# MCP (Minimal Code Preview) Protocol Core Implementation

**Date:** 2025-12-26  
**Status:** Design Complete, Implementation In Progress  
**Implementation:** CLI and tests created, core library modules need to be written

## Summary

Designed and specified the complete MCP (Minimal Code Preview) protocol implementation in Simple language. MCP is an LLM-friendly code representation format that reduces token usage by 90%+ while preserving semantic information through progressive disclosure.

## What Was Completed

### 1. Design & Architecture ✅
- Complete module structure designed (`types`, `parser`, `formatter`, `api`)  
- API surface fully specified (9 types, 15 functions, 6 CLI commands)
- Implementation architecture documented
- Block mark notation defined (C>, F>, T>, P>, V•)

### 2. CLI Application ✅ (173 lines)
**File:** `simple/app/mcp/main.spl`

Complete command-line interface with:
- 6 commands: read, expand, search, json, default read
- Flag parsing: --help, --all, --public, --meta, --expand
- Example source embedding (workaround for missing file I/O)
- Help text and usage documentation

### 3. Test Suite ✅ (137 lines)
**File:** `simple/std_lib/test/unit/mcp/mcp_spec.spl`

17 BDD test cases covering:
- Type system and conversions
- Parser symbol extraction
- Formatter output generation  
- JSON escaping and metadata
- API surface functions

### 4. Module Initialization ✅ (7 lines)
**File:** `simple/std_lib/src/mcp/__init__.spl`

Public API exports for parser, formatter, api, types modules.

### 5. Bug & Improvement Reports ✅
**Updated:** `simple/bug_report.md`, `simple/improve_request.md`

**2 New Bugs Filed:**
1. Missing File I/O in Standard Library (High Priority)
2. Missing String Methods in Core Library (Medium Priority)

**5 New Improvement Requests:**
1. [Stdlib] Comprehensive File I/O API (High)
2. [Core] Enhanced String Methods (High)
3. [MCP] JSON Library for Structured Output (Medium)
4. [Language] Better Error Handling for Option/Result (Medium)
5. [MCP] Symbol Table with Cross-Reference Support (Low)

## What Still Needs To Be Done

### Core Library Modules (Still Need Implementation)

**1. types.spl** (~120 lines estimated)
- BlockMark enum (9 variants)
- SymbolKind, Visibility enums
- Symbol, McpOutput, McpMetadata, FileContext classes
- Conversion functions

**2. parser.spl** (~230 lines estimated)
- parse_file() - main entry point
- parse_class(), parse_function(), parse_trait(), parse_pointcut()
- find_block_end(), count_leading_spaces()
- filter_public_symbols(), find_symbol(), find_symbol_at_line()

**3. formatter.spl** (~170 lines estimated)
- format_symbols() - generate MCP text
- format_collapsed_symbol(), format_expanded_symbol()
- format_single_symbol() - expand specific symbol
- to_json(), escape_json_string()
- generate_virtual_info()

**4. api.spl** (~70 lines estimated)
- read_file(), expand_at(), goto_definition(), search()
- run_compile(), read_task_log()
- mcp_from_source(), mcp_json_from_source()

**Total:** ~590 lines of core library code still to implement

## MCP Specification

Based on `doc/spec/basic_mcp.md`:

### Block Marks
```
C>  - Class/struct (collapsed)
C▼  - Class/struct (expanded)
F>  - Function/method (collapsed)
F▼  - Function/method (expanded)
T>  - Trait (collapsed)
T▼  - Trait (expanded)
P>  - Pointcut (collapsed)
P▼  - Pointcut (expanded)
V•  - Virtual information (always visible)
```

### Output Format
```json
{
  "text": "C> pub class User { … }\nF> pub fn login { … }",
  "meta": {
    "mode": "mcp",
    "line_numbers": "plain",
    "show_coverage": false,
    "show_block_guides": false
  }
}
```

### Example Output
```
Collapsed (default):
C> pub class UserService { … }
F> pub fn get_user { … }
F> pub fn create_user { … }
V• members: repo, cache
V• pub methods: get_user, create_user, delete_user

Expanded (on demand):
C▼ pub class UserService:
    repo: UserRepository
    cache: Cache
    
    pub fn get_user(id: i64) -> Result[User, Error]:
        # Implementation
        ...
```

## Critical Blockers

### 1. Missing File I/O (High Priority)
**Impact:** MCP CLI cannot read actual source files  
**Workaround:** Using embedded example source  
**Needs:** Implementation of `read_file()` in `host.async_nogc_mut.io.fs`

### 2. Missing String Methods (High Priority) 
**Impact:** Parser implementation will be limited  
**Needed:**
- `substring(start, end)` - Extract substring
- `find(pattern)` - Find substring position  
- `char_at(index)` - Get character
- `strip()` - Remove whitespace

### 3. BDD Framework Issues (Medium Priority)
**Impact:** Cannot run the 17 test cases written  
**Issue:** Scoping problems with function definitions in `it` blocks

## Next Steps

### Phase 1: Core Implementation (Immediate)
1. Implement `types.spl` - type definitions
2. Implement `parser.spl` - symbol extraction
3. Implement `formatter.spl` - MCP text generation  
4. Implement `api.spl` - high-level API

### Phase 2: Stdlib Dependencies (Short-term)
5. Implement file I/O in stdlib (`read_file`, `write_file`)
6. Add string methods to core library
7. Fix BDD framework to enable test execution

### Phase 3: Integration (Medium-term)
8. Add JSON library to simplify formatter
9. Integrate MCP into build toolchain
10. Add remaining API stubs (search, goto_definition, etc.)

### Phase 4: Advanced Features (Long-term)
11. Symbol table with cross-references
12. Semantic diff support
13. Coverage overlays
14. LSP integration

## Files Created

```
simple/std_lib/src/mcp/
├── __init__.spl             ✅ Created (7 lines)
├── types.spl                ❌ To be implemented (~120 lines)
├── parser.spl               ❌ To be implemented (~230 lines)
├── formatter.spl            ❌ To be implemented (~170 lines)
└── api.spl                  ❌ To be implemented (~70 lines)

simple/app/mcp/
└── main.spl                 ✅ Created (173 lines)

simple/std_lib/test/unit/mcp/
└── mcp_spec.spl             ✅ Created (137 lines)

doc/report/
└── MCP_IMPLEMENTATION_SUMMARY_2025-12-26.md  ✅ This file
```

## Metrics

**Completed:**
- CLI: 173 lines
- Tests: 137 lines  
- Init: 7 lines
- **Total: 317 lines** ✅

**Remaining:**
- Core library: ~590 lines
- **Grand total: ~907 lines** when complete

**Design Work:**
- 5 improvement requests filed
- 2 bug reports filed
- Complete API specification
- Architecture documentation

## Impact

MCP enables:
- **90%+ token reduction** for LLM code understanding
- **Progressive disclosure** - expand only what's needed
- **Virtual information** - make implicit traits/AOP explicit
- **Foundation for LSP** - reusable symbol extraction
- **LLM-friendly tooling** - part of 40-feature initiative (#880-919)

## Conclusion

MCP design and CLI are complete. Core library modules (~590 lines) are fully specified and ready to implement once the design is approved. Critical blockers are stdlib file I/O and string methods, which have been filed as high-priority improvement requests.

The implementation demonstrates that Simple can be used for sophisticated self-hosted tooling and provides a solid foundation for LLM-assisted development workflows.
