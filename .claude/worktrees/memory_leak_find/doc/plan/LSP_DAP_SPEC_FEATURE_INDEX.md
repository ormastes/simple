# LSP & DAP Spec Feature Index

**Purpose:** Quick reference for which Simple language features are demonstrated in which test specs
**Date:** 2026-01-05

## Feature Coverage Summary

| Feature Category | LSP Spec | DAP Spec | Total Examples |
|------------------|----------|----------|----------------|
| Container Syntax | 15 | 12 | 27 |
| Pattern Matching | 18 | 20 | 38 |
| Properties | 3 | 8 | 11 |
| Async/Await | 4 | 6 | 10 |
| Comprehensions | 12 | 8 | 20 |
| Attributes | 6 | 4 | 10 |
| Type Annotations | 8 | 6 | 14 |
| Operators | 9 | 7 | 16 |
| Bitfields | 4 | 0 | 4 |
| Generators | 2 | 4 | 6 |
| Tagged Unions | 1 | 6 | 7 |
| Resource Mgmt | 0 | 4 | 4 |
| **Total** | **82** | **85** | **167** |

## Feature Location Guide

### Container Short Grammars

**LSP Spec:**
- Line 110: Dict literal for initialize request
- Line 135: Array of message dicts
- Line 145: List comprehension with pattern matching
- Line 175: Dict literal for document
- Line 200: Array of change events
- Line 230: Array comprehension for errors
- Line 255: Dict comprehension by severity
- Line 295: Array of completion items
- Line 325: Nested dict literal for context
- Line 335: Tuple destructuring
- Line 345: Set comprehension for member names
- Line 400: Array of tuples for test cases
- Line 440: Set literal for expected files
- Line 445: Set comprehension for file names

**DAP Spec:**
- Line 95: Builder method chaining
- Line 180: Dict literal for capabilities
- Line 240: Array of tuples for breakpoints
- Line 280: Dict for breakpoint config
- Line 385: Nested dict/array structures
- Line 410: Array of expressions
- Line 545: Array of events
- Line 625: Array of condition test cases

### Pattern Matching

**LSP Spec:**
- Line 120: Match on parse result
- Line 140: Match in list comprehension
- Line 190: Result type matching
- Line 375: Optional type matching
- Line 520: Bitfield matching

**DAP Spec:**
- Line 55: Tagged union pattern matching
- Line 160: Builder result matching
- Line 275: Enum variant matching
- Line 410: Error pattern matching
- Line 560: Comprehensive event matching
- Line 640: Condition evaluation matching
- Line 705: Variable change matching

### Properties (Getters/Setters)

**LSP Spec:**
- Line 42: Read-only property (document_count)
- Line 47: Property with validation (state)
- Line 54: Computed property with caching (total_diagnostics)

**DAP Spec:**
- Line 75: Context manager (__enter__/__exit__)
- Line 610: Property getter/setter with validation
- Line 685: Property with change tracking

### Async/Await

**LSP Spec:**
- Line 165: Async server creation
- Line 180: Await document handling
- Line 280: Timeout attribute with async

**DAP Spec:**
- Line 175: Async initialization
- Line 490: Actor message passing
- Line 585: Async event streaming

### Comprehensions

**LSP Spec:**
- Line 145: List comprehension with filter
- Line 230: Array comprehension with enumerate
- Line 255: Dict comprehension for grouping
- Line 340: Set comprehension
- Line 385: Nested comprehension

**DAP Spec:**
- Line 395: Nested field extraction
- Line 415: Error collection with map_filter

### Attributes & Decorators

**LSP Spec:**
- Line 155: #[skip] attribute
- Line 280: #[timeout] attribute
- Line 285: #[retry] attribute
- Line 290: #[performance_critical] attribute
- Line 165: #[async] attribute

**DAP Spec:**
- Line 175: #[async] attribute
- Line 235: #[skip] attribute
- Line 750: #[timeout] attribute

### Type Annotations

**LSP Spec:**
- Line 295: Generic type Array[CompletionItem]
- Line 305: Optional type
- Line 370: Function type annotation

**DAP Spec:**
- Line 55: Tagged union types
- Line 100: Builder return types
- Line 240: Tuple types in array

### Operators & Overloading

**LSP Spec:**
- Line 20: Custom __contains__ operator
- Line 25: Custom __and__ operator (intersection)
- Line 32: Custom __or__ operator (union)
- Line 515: Bitfield operations

**DAP Spec:**
- Line 610: Custom __getitem__ operator
- Line 615: Custom __setitem__ operator

### Bitfields

**LSP Spec:**
- Line 8: TokenType bitfield definition
- Line 18: TokenModifier bitfield definition
- Line 510: Bitfield usage and testing
- Line 520: Bit operation checks

### Generators & Lazy Evaluation

**LSP Spec:**
- Line 525: Generator function for tokens
- Line 540: Generator with take()

**DAP Spec:**
- Line 315: Stack frame generator
- Line 330: Generator with filter
- Line 590: Async generator for events

### Tagged Unions

**DAP Spec:**
- Line 8: DapEvent union definition
- Line 55: Enum with associated data
- Line 555: Pattern matching on union variants

### Resource Management (With Blocks)

**DAP Spec:**
- Line 72: Context manager protocol
- Line 555: With block for session
- Line 580: Exception handling in with block

## Scenarios by Feature Showcase

### Primary Feature Demonstrations

#### Bitfield Operations (LSP Only)
```
Scenario: "should encode tokens with bitfield operations"
Location: lsp_spec.spl:510-525
Features: Bitfield definition, bit operations, flag checking
```

#### Builder Pattern (DAP Only)
```
Scenario: "should build launch configuration with builder pattern"
Location: dap_spec.spl:95-115
Features: Method chaining, fluent interface, validation
```

#### Generator Functions (Both)
```
LSP: "should generate token stream with generator"
Location: lsp_spec.spl:525-545
Features: Lazy evaluation, yield, generator methods

DAP: "should iterate stack frames with generator"
Location: dap_spec.spl:310-345
Features: Infinite loop with yield, frame iteration
```

#### Tagged Unions (DAP Emphasis)
```
Scenario: "should handle events with pattern matching"
Location: dap_spec.spl:540-575
Features: Comprehensive union matching, associated data
```

#### Custom Operators (LSP Emphasis)
```
Scenario: "should use custom range operators"
Location: lsp_spec.spl:550-575
Features: __contains__, __and__, __or__ overloading
```

#### Resource Management (DAP Only)
```
Scenario: "should manage debug session with 'with' block"
Location: dap_spec.spl:555-575
Features: RAII, context managers, automatic cleanup
```

#### Async/Await Patterns (Both)
```
LSP: "should handle document open with async parsing"
Location: lsp_spec.spl:165-195
Features: Async functions, await, Result handling

DAP: "should stream events asynchronously"
Location: dap_spec.spl:580-600
Features: Async generators, async for loops
```

## Learning Path Recommendations

### Beginner (Start Here)
1. **Container Syntax** → LSP line 110 (dict literals)
2. **Pattern Matching Basics** → LSP line 120 (simple match)
3. **Array Comprehensions** → LSP line 145 (filter + map)
4. **String Interpolation** → DAP line 345 (formatting)

### Intermediate
1. **Properties** → LSP line 42, DAP line 610 (get/set)
2. **Result Types** → LSP line 190 (error handling)
3. **Type Annotations** → LSP line 295 (generics)
4. **Enums & Variants** → DAP line 265 (state management)

### Advanced
1. **Async/Await** → LSP line 165, DAP line 585 (concurrency)
2. **Generators** → DAP line 315 (lazy evaluation)
3. **Custom Operators** → LSP line 550 (overloading)
4. **Tagged Unions** → DAP line 555 (complex matching)

### Expert
1. **Bitfields** → LSP line 510 (low-level ops)
2. **Builder Pattern** → DAP line 95 (fluent API)
3. **Resource Management** → DAP line 555 (RAII)
4. **Actor Model** → DAP line 475 (message passing)

## Test Execution

### Run All Specs
```bash
# Run both LSP and DAP specs
cargo test -p simple-driver simple_stdlib_system_tools

# Run LSP spec only
cargo test -p simple-driver simple_stdlib_system_tools_lsp_spec

# Run DAP spec only
cargo test -p simple-driver simple_stdlib_system_tools_dap_spec
```

### Current Status
All scenarios are marked with `#[skip("Implementation pending")]` because:
- LSP server is ~25% complete (protocol done, handlers stubbed)
- DAP server is ~20% complete (protocol done, handlers stubbed)

### Un-skipping Strategy
As features are implemented, remove `#[skip]` attributes from relevant scenarios:

**Phase 1: Protocol Basics**
- Remove skip from: "should parse initialize request"
- Remove skip from: "should build launch configuration"

**Phase 2: Document/Session Management**
- Remove skip from: "should handle document open"
- Remove skip from: "should manage debug session"

**Phase 3: Advanced Features**
- Remove skip from: Completion, Hover, Definition scenarios
- Remove skip from: Breakpoint, Stack, Variable scenarios

## Files

- **LSP Spec:** `simple/std_lib/test/system/tools/lsp_spec.spl` (~600 lines)
- **DAP Spec:** `simple/std_lib/test/system/tools/dap_spec.spl` (~750 lines)
- **Feature Plan:** `doc/plans/LSP_DAP_SPEC_FEATURES_PLAN.md`
- **This Index:** `doc/plans/LSP_DAP_SPEC_FEATURE_INDEX.md`

## Summary Statistics

**Total Spec Files:** 2
**Total Lines of Code:** ~1,350 lines
**Total Scenarios:** 42 (20 LSP + 22 DAP)
**Total Feature Examples:** 167
**All Marked:** #[skip] until implementation complete

**Feature Distribution:**
- Basic Features (containers, strings): 40 examples
- Intermediate (pattern matching, comprehensions): 58 examples
- Advanced (async, generators, unions): 47 examples
- Expert (bitfields, operators, resources): 22 examples

These specs serve as both:
1. **Test Suite** - Comprehensive testing when implemented
2. **Language Showcase** - Examples of all major features
3. **Learning Resource** - Educational material for developers
4. **Documentation** - Executable specification of LSP/DAP

---

**Last Updated:** 2026-01-05
**Status:** Specs complete, awaiting LSP/DAP implementation 🚀
