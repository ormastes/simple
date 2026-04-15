# Phase 3: Parser & Type System Enhancements

**Date:** 2026-02-09
**Status:** 🚀 In Progress
**Follows:** Phase 2 (5 TODOs completed)

## Overview

Phase 3 focuses on parser enhancements, type system improvements, SDN integration, and utility functions - all implementable in Pure Simple without FFI dependencies.

## Objectives

- **SDN Integration:** Replace placeholder SDN parsing with std.sdn
- **Type System:** Add pattern binding, type extraction, tracking
- **Parser Enhancements:** Interpolation parsing, attribute support
- **Utility Functions:** I/O helpers, neural network utilities

## Sub-Phases

### Phase 3.1: SDN Integration (5 TODOs)

**Files:** `src/lib/db_atomic.spl`, `src/lib/src/dl/config_loader.spl`, `src/lib/src/exp/artifact.spl`, `src/lib/src/exp/config.spl`
**Dependency:** `std.sdn` (already exists)

**Tasks:**
1. **TODO #201:** Use proper SDN parser in `db_atomic.spl` (line 351)
2. **TODO #202:** Parse SDN content and update table structure (line 406)
3. **TODO #213:** Use proper SDN parser in DL config loader (line 29)
4. **TODO #214:** Parse SDN artifacts file in experiment tracking (line 153)
5. **TODO #215:** Use `rt_sdn_parse` in experiment config (line 426)

**Approach:**
- Replace manual line-based parsing with `std.sdn.parse_sdn()`
- Extract fields from parsed SDN data structures
- Validate structure and provide helpful errors

### Phase 3.2: Type System Helpers (4 TODOs)

**Files:** `src/compiler/type_system/expr_infer.spl`, `src/compiler/type_system/stmt_check.spl`

**Tasks:**
1. **TODO #171:** Bind pattern variables in expression inference (line 234)
2. **TODO #178:** Extract element type from iterable (line 381)
3. **TODO #180:** Track last expression type in blocks (line 564)
4. **TODO #174:** Bind pattern variables in match arms (line 753)

**Approach:**
- Add helper functions for pattern decomposition
- Implement type extraction from container types
- Track types through statement sequences

### Phase 3.3: Parser Enhancements (2 TODOs)

**Files:** `src/compiler/parser.spl`, `src/compiler/parser_extensions.spl`

**Tasks:**
1. **TODO #152:** Parse string interpolations (line 1217)
2. **TODO #151:** Add attributes field to Function struct (line 272)

**Approach:**
- Parse `{expr}` patterns in string literals
- Add attribute tracking to AST nodes
- Support `#[attr]` syntax parsing

### Phase 3.4: Utility Functions (3 TODOs)

**Files:** `src/lib/hooks/stop.spl`, `src/lib/pure/nn.spl`

**Tasks:**
1. **TODO #186:** Print to stdout helper (line 154)
2. **TODO #187:** Read line from stdin helper (line 158)
3. **TODO #189:** Implement dropout mask for neural networks (line 182)

**Approach:**
- Use existing `rt_*` FFI functions for I/O
- Implement dropout with random masking
- Pure Simple implementations

## Implementation Strategy

1. **SDN First:** Highest impact, clear wins with existing stdlib
2. **Type System:** Foundation for better type checking
3. **Parser:** Enable new syntax features
4. **Utilities:** Small helpers, quick wins

## Success Criteria

- [ ] All 5 SDN placeholders replaced with std.sdn
- [ ] Pattern variable binding working in 2+ contexts
- [ ] Type extraction from iterables working
- [ ] String interpolation parsing complete
- [ ] Attribute support added to parser
- [ ] I/O helpers implemented
- [ ] Dropout mask working
- [ ] All files compile successfully
- [ ] Test suite remains 330/330 passing

## Estimated TODOs Resolved

**Total:** 14 TODOs
- SDN Integration: 5
- Type System: 4
- Parser: 2
- Utilities: 3

## Timeline

- **Day 1:** SDN Integration (Phase 3.1)
- **Day 2:** Type System Helpers (Phase 3.2)
- **Day 3:** Parser Enhancements (Phase 3.3)
- **Day 4:** Utility Functions + Testing (Phase 3.4)

## Next Phase

**Phase 4:** More parser/type system work, or move to testing/documentation
