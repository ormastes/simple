# Custom Blocks Easy API - Implementation Report

**Date:** 2026-02-05
**Status:** Research Complete, Ready for Implementation
**Author:** Claude (Research Agent)
**Epic:** Custom Blocks User Experience

---

## Executive Summary

This report presents a comprehensive research on making custom block creation in Simple Language easier and more user-friendly. The current `BlockDefinition` trait (20+ methods) is powerful but too complex for most use cases. We propose a three-tier API that provides progressive disclosure:

1. **Tier 1 (Minimal):** `block()` function - 80% of use cases, 3 lines of code
2. **Tier 2 (Builder):** `BlockBuilder` - 15% of use cases, fluent API
3. **Tier 3 (Full):** `BlockDefinition` trait - 5% of use cases, complete control

**Key Achievement:** Reduces block creation from 50+ lines to 3 lines for common cases while maintaining full power for advanced features.

---

## Research Deliverables

### 1. Comprehensive Documentation

**Location:** `doc/research/custom_blocks_user_friendly_api.md`
- 800+ lines of detailed API design
- Complete specification of all three tiers
- 20+ usage examples
- Error handling patterns
- Best practices and guidelines

### 2. SSpec Test Suite

**Location:** `test/compiler/custom_blocks_easy_api_spec.spl`
- 600+ lines of executable tests
- 60+ test cases covering all APIs
- Common recipes and patterns
- Edge cases and performance tests
- Documentation examples

### 3. Quick Reference Guide

**Location:** `doc/guide/custom_blocks_quick_reference.md`
- Concise cheat sheet (5-minute read)
- API signatures
- Common patterns
- Troubleshooting guide
- Decision tree for API selection

---

## Current State Analysis

### Existing Block Infrastructure (Already Implemented)

| Component | Status | Location |
|-----------|--------|----------|
| `BlockDefinition` trait | ✅ Complete | `src/compiler/blocks/definition.spl` |
| `BlockValue` enum | ✅ Complete | `src/compiler/blocks/value.spl` |
| `BlockRegistry` | ✅ Complete | `src/compiler/blocks/registry.spl` |
| `LexerMode` enum | ✅ Complete | `src/compiler/blocks/modes.spl` |
| `SyntaxFeatures` | ✅ Complete | `src/compiler/blocks/modes.spl` |
| `BlockContext` | ✅ Complete | `src/compiler/blocks/context.spl` |
| Built-in blocks | ✅ Complete | `src/compiler/blocks/builtin_blocks_defs.spl` |
| Lexer integration | ✅ Complete | `src/compiler/lexer.spl` |
| Parser integration | ✅ Complete | `src/compiler/parser.spl` |

**Status:** Foundation is 100% complete. All infrastructure is in place.

### What Needs to Be Built

**New modules to implement:**
1. `compiler.blocks.easy` - Minimal API wrapper
2. `compiler.blocks.builder` - Fluent builder implementation
3. `compiler.blocks.utils` - Pre-built parsers and utilities
4. `compiler.blocks.testing` - Test helpers

---

## Implementation Roadmap

### Phase 1: Core Easy API (Week 1-2)

**Goal:** Implement `compiler.blocks.easy` module

**Tasks:**
1. Implement `block()` function
   - Wraps `BlockDefinition` trait with defaults
   - Simple signature: `fn(kind, mode, parser) -> BlockDefinition`
   - Smart defaults for all optional methods

2. Implement `block_with_validation()`
   - Adds validation hook
   - Wraps simple validator `fn(BlockValue) -> [text]`

3. Implement `const_block()`
   - Adds compile-time evaluation
   - Wraps eval function `fn(BlockValue) -> ConstValue?`

**Files to create:**
- `src/compiler/blocks/easy.spl` (~200 lines)

**Tests:**
- `test/compiler/blocks/easy_api_spec.spl` (~150 lines)

**Success Criteria:**
- Users can create blocks in 3 lines
- All tests pass
- Example blocks work (heredoc, color, etc.)

---

### Phase 2: Builder API (Week 3-4)

**Goal:** Implement `compiler.blocks.builder` module

**Tasks:**
1. Implement `BlockBuilder` struct
   - Fluent API with method chaining
   - Builder state tracking
   - Validation at build time

2. Implement lexer mode shortcuts
   - `.raw_text()`, `.math_mode()`, `.normal_mode()`

3. Implement feature enablement
   - `.enable_feature(name)`, `.disable_feature(name)`
   - Presets: `.enable_all_math()`, `.enable_pipelines()`

4. Implement parser variants
   - `.simple_parser(fn(text) -> Result)` - Simple signature
   - `.parser(fn(text, ctx) -> Result)` - Full signature

5. Implement optional hooks
   - `.simple_validator()`, `.validator()`
   - `.const_eval()`
   - `.highlighter()`, `.completer()`, `.hover_provider()`

6. Implement `.build()` method
   - Construct `BlockDefinition` from builder state
   - Apply smart defaults
   - Validate configuration

**Files to create:**
- `src/compiler/blocks/builder.spl` (~400 lines)

**Tests:**
- `test/compiler/blocks/builder_api_spec.spl` (~300 lines)

**Success Criteria:**
- Fluent API works with method chaining
- All presets function correctly
- Builder validates at build time
- Generated blocks behave correctly

---

### Phase 3: Utility Library (Week 5)

**Goal:** Implement `compiler.blocks.utils` module

**Tasks:**
1. Pre-built parsers
   - `parse_json()`, `parse_yaml()`, `parse_toml()`, `parse_xml()`, `parse_csv()`
   - Use existing parsing libraries

2. Pre-built validators
   - `validate_json()`, `validate_regex()`, `validate_sql()`

3. Syntax highlighting helpers
   - `highlight_keywords()`, `highlight_strings()`, `highlight_comments()`, `highlight_numbers()`

4. Error message helpers
   - `error_at()`, `error_span()`, `errors_from_strings()`

5. Common utilities
   - `interpolate_variables()`, `strip_indent()`, `normalize_newlines()`

**Files to create:**
- `src/compiler/blocks/utils.spl` (~500 lines)

**Tests:**
- `test/compiler/blocks/utils_spec.spl` (~200 lines)

**Success Criteria:**
- All utility functions work
- Users can create JSON block in 5 lines using utilities
- Error helpers produce proper spans

---

### Phase 4: Testing Framework (Week 6)

**Goal:** Implement `compiler.blocks.testing` module

**Tasks:**
1. Test helper functions
   - `test_parse()` - Parse and assert
   - `test_parse_error()` - Assert parse error
   - `test_validate()` - Assert validation errors
   - `test_const_eval()` - Assert compile-time evaluation

2. Block mocking
   - `mock_block()` - Create test block
   - `with_block()` - Scoped registration (already in easy.spl)

3. Assertion helpers
   - Block-specific assertions
   - Payload comparison
   - Error message matching

**Files to create:**
- `src/compiler/blocks/testing.spl` (~200 lines)

**Tests:**
- `test/compiler/blocks/testing_spec.spl` (~100 lines)

**Success Criteria:**
- Test helpers simplify block testing
- Scoped registration works correctly
- All assertion helpers function properly

---

### Phase 5: Documentation & Examples (Week 7)

**Goal:** Complete user-facing documentation

**Tasks:**
1. Tutorial
   - Step-by-step guide for creating first block
   - Progressive complexity (simple → builder → full)
   - Common pitfalls and solutions

2. Cookbook
   - 20+ recipes for common block types
   - Copy-paste examples
   - Explanations of design choices

3. API Reference
   - Complete API documentation
   - All function signatures
   - Parameter descriptions
   - Return type documentation

4. Migration Guide
   - From full `BlockDefinition` to new APIs
   - Examples of before/after
   - Decision tree for API selection

5. Example Blocks
   - Implement 10+ example blocks using new API
   - Show progression from simple to complex

**Files to create:**
- `doc/guide/custom_blocks_tutorial.md` (~400 lines)
- `doc/guide/custom_blocks_cookbook.md` (~600 lines)
- `doc/guide/custom_blocks_api_reference.md` (~800 lines)
- `doc/guide/custom_blocks_migration.md` (~300 lines)
- `examples/blocks/` - Example block implementations

**Success Criteria:**
- New users can create first block in 10 minutes
- Documentation covers 95% of use cases
- Examples compile and run
- Migration path is clear

---

### Phase 6: Built-in Block Migration (Week 8)

**Goal:** Migrate existing built-in blocks to new API

**Tasks:**
1. Audit built-in blocks
   - `m{}`, `loss{}`, `nograd{}`, `sh{}`, `sql{}`, `re{}`, `json{}`, `md{}`
   - Identify which can use new API

2. Migrate eligible blocks
   - Rewrite using `BlockBuilder` where appropriate
   - Reduce code duplication
   - Keep advanced features where needed

3. Add documentation
   - Document each built-in block's implementation
   - Use as examples in tutorials

4. Verify behavior unchanged
   - Run full test suite
   - Ensure backward compatibility

**Files to update:**
- `src/compiler/blocks/builtin_blocks_defs.spl`
- Update all built-in block definitions

**Success Criteria:**
- Built-in blocks use new API where appropriate
- All tests pass (no behavior changes)
- Code is more readable and maintainable

---

## Technical Design Details

### Module Structure

```
src/compiler/blocks/
├── definition.spl         # Existing: BlockDefinition trait
├── value.spl             # Existing: BlockValue enum
├── registry.spl          # Existing: BlockRegistry
├── modes.spl             # Existing: LexerMode, SyntaxFeatures
├── context.spl           # Existing: BlockContext, BlockError
├── builtin_blocks_defs.spl # Existing: Built-in blocks
├── resolver.spl          # Existing: Block resolution
├── easy.spl              # NEW: Minimal API
├── builder.spl           # NEW: Builder API
├── utils.spl             # NEW: Utility functions
└── testing.spl           # NEW: Test helpers
```

### API Layering

```
┌─────────────────────────────────────────┐
│ Tier 1: block() / const_block()        │  Simple function calls
├─────────────────────────────────────────┤
│ Tier 2: BlockBuilder                   │  Fluent builder pattern
├─────────────────────────────────────────┤
│ Tier 3: BlockDefinition trait          │  Full trait implementation
├─────────────────────────────────────────┤
│ Foundation: Registry, Context, Value    │  Core infrastructure
└─────────────────────────────────────────┘
```

Each tier builds on the one below:
- Tier 1 wraps Tier 3 with smart defaults
- Tier 2 provides fluent API, builds Tier 3
- Tier 3 is always available for full control

### Smart Defaults Strategy

**Problem:** `BlockDefinition` has 20+ methods, most optional.

**Solution:** Provide sensible defaults for all optional methods:

| Method | Default Behavior |
|--------|------------------|
| `lexer_mode()` | `LexerMode.Raw` |
| `syntax_features()` | All features disabled |
| `validate()` | Return empty array (no errors) |
| `eval_const()` | Return `None` (no compile-time eval) |
| `lex()` | Not implemented (use standard lexer) |
| `treesitter_outline()` | Basic outline extraction |
| `parse_full()` | Delegates to `parse_payload()` |
| `highlight()` | Basic text highlighting |
| `completions()` | Return empty array |
| `hover()` | Return `None` |
| `signature_help()` | Return `None` |

**Implementation Pattern:**

```simple
# easy.spl - Wraps BlockDefinition
fn block(kind: text, mode: LexerMode, parser: fn(text) -> Result) -> BlockDefinition:
    struct SimpleBlockDef: BlockDefinition:
        _kind: text
        _mode: LexerMode
        _parser: fn(text) -> Result<BlockValue, text>

        fn kind() -> text: self._kind
        fn lexer_mode() -> LexerMode: self._mode

        fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
            match (self._parser)(payload):
                case Ok(value): Ok(value)
                case Err(msg): Err(BlockError(message: msg, span: ctx.span))

        # All other methods use defaults
        fn syntax_features() -> SyntaxFeatures: SyntaxFeatures.default()
        fn validate(value, ctx) -> [BlockError]: []
        fn eval_const(value) -> ConstValue?: None
        # ... etc

    SimpleBlockDef(_kind: kind, _mode: mode, _parser: parser)
```

### Builder State Management

**Challenge:** Builder must track mutable state across method calls.

**Solution:** Use `me` methods with field updates:

```simple
# builder.spl
struct BlockBuilder:
    kind: text
    mode: LexerMode
    features: SyntaxFeatures
    parser_fn: fn(text, BlockContext) -> Result<BlockValue, BlockError>?
    validator_fn: fn(BlockValue, BlockContext) -> [BlockError]?
    eval_fn: fn(BlockValue) -> ConstValue?
    # ... other fields

impl BlockBuilder:
    static fn new(kind: text) -> BlockBuilder:
        BlockBuilder(
            kind: kind,
            mode: LexerMode.Raw,
            features: SyntaxFeatures.default(),
            parser_fn: None,
            validator_fn: None,
            eval_fn: None
        )

    me raw_text() -> BlockBuilder:
        self.mode = LexerMode.Raw
        self

    me enable_feature(name: text) -> BlockBuilder:
        match name:
            case "power_caret": self.features.power_caret = true
            case "broadcast_ops": self.features.broadcast_ops = true
            # ... other features
        self

    fn build() -> BlockDefinition:
        # Validate builder state
        if not self.parser_fn.?:
            panic("Parser function is required")

        # Construct BlockDefinition with captured state
        # ... implementation
```

---

## Testing Strategy

### Unit Tests

Each module has dedicated spec file:
- `easy_api_spec.spl` - Tests `block()`, `const_block()`, etc.
- `builder_api_spec.spl` - Tests `BlockBuilder`
- `utils_spec.spl` - Tests utility functions
- `testing_spec.spl` - Tests test helpers

### Integration Tests

Test complete workflows:
- Create block → Register → Use → Unregister
- Build complex block with multiple features
- Use utility functions with builder API

### Example Tests

Use example blocks as test cases:
- Implement 10+ example blocks
- Each example is a test case
- Verify they work end-to-end

### Regression Tests

Ensure backward compatibility:
- All existing block tests still pass
- Built-in blocks work identically
- Performance is not degraded

---

## Performance Considerations

### Zero-Cost Abstractions

**Goal:** New APIs should have no runtime overhead.

**Strategy:**
1. **Compile-time construction:** Builders resolve at compile time
2. **Function inlining:** Wrapper functions are inlined
3. **Smart defaults:** Default implementations are empty (no-op)
4. **Lazy evaluation:** Only parse when block is used

### Benchmarks

Compare performance:
- Full trait implementation (baseline)
- `block()` wrapper (should be identical)
- `BlockBuilder` (should be identical after inlining)

**Acceptance Criteria:** <1% overhead vs. full trait

---

## Migration Path for Existing Code

### Phase 1: Additive (No Breaking Changes)

- New APIs added alongside existing trait
- All existing code continues to work
- Users can opt-in to new APIs

### Phase 2: Soft Deprecation (v0.6.0)

- Document new APIs as preferred
- Add deprecation notices to docs
- Show migration examples

### Phase 3: Hard Deprecation (v0.7.0)

- Emit compiler warnings for direct trait impl
- Suggest using new APIs
- Provide auto-migration tool

### Phase 4: Removal (v1.0.0)

- Remove trait-based API (if desired)
- Force migration to new APIs
- Or: Keep trait for advanced use cases

**Recommendation:** Keep full trait available indefinitely. Progressive disclosure means advanced users can still access full power.

---

## Success Metrics

### Quantitative

1. **Lines of Code Reduction:** 90% reduction for simple blocks (50 lines → 5 lines)
2. **Time to First Block:** <10 minutes for new users
3. **API Coverage:** 80% of use cases handled by Tier 1, 95% by Tier 2
4. **Performance:** <1% overhead vs. full trait
5. **Test Coverage:** >95% code coverage for new modules

### Qualitative

1. **User Feedback:** Survey users on ease of use
2. **Documentation Quality:** Can new users succeed without help?
3. **Example Quality:** Are examples clear and comprehensive?
4. **Error Messages:** Are build errors helpful?
5. **Discoverability:** Can users find the right API?

---

## Risks & Mitigations

### Risk 1: API Complexity Creep

**Risk:** Builder API becomes as complex as trait.

**Mitigation:**
- Enforce "progressive disclosure" principle
- Regular reviews of API surface
- User testing to validate simplicity

### Risk 2: Performance Overhead

**Risk:** Wrappers add runtime cost.

**Mitigation:**
- Benchmark all APIs vs. baseline
- Use inlining and compile-time resolution
- Profile and optimize hot paths

### Risk 3: Insufficient Power

**Risk:** New APIs can't handle advanced cases.

**Mitigation:**
- Keep full trait available (Tier 3)
- Ensure builder can configure all features
- Regular user feedback on limitations

### Risk 4: Backward Compatibility

**Risk:** Migration breaks existing code.

**Mitigation:**
- Additive-only changes in Phase 1
- Long deprecation period
- Auto-migration tool
- Keep trait available

### Risk 5: Documentation Debt

**Risk:** Docs become outdated as API evolves.

**Mitigation:**
- SSpec tests as executable docs
- Regular doc reviews
- User feedback on clarity
- Version docs with API changes

---

## Resource Requirements

### Development Time

| Phase | Duration | Complexity |
|-------|----------|------------|
| Phase 1: Easy API | 2 weeks | Low |
| Phase 2: Builder API | 2 weeks | Medium |
| Phase 3: Utils | 1 week | Low |
| Phase 4: Testing | 1 week | Low |
| Phase 5: Docs | 1 week | Medium |
| Phase 6: Migration | 1 week | Low |
| **Total** | **8 weeks** | - |

### Team Size

- **1 developer** - Full-time for 8 weeks
- **1 reviewer** - Part-time (10 hours/week)
- **1 tech writer** - Week 7 (docs)

### Dependencies

**Required before starting:**
- ✅ `BlockDefinition` trait (complete)
- ✅ `BlockRegistry` (complete)
- ✅ Lexer/Parser integration (complete)
- ✅ Built-in blocks (complete)

**No blockers - ready to start immediately.**

---

## Future Enhancements

### Package Manager Integration

```simple
# Install blocks from registry
simple install blocks/graphql
simple install blocks/protobuf

# Use in code
import blocks.graphql
val query = graphql{ ... }
```

### Block Composition

```simple
# Compose multiple blocks
val template = BlockBuilder("template")
    .compose_with(sql_block)
    .compose_with(markdown_block)
    .build()
```

### Macro Blocks

```simple
# Blocks that generate code
val component = macro_block("component", \payload:
    generate_component_code(payload)
)
```

### Live Preview (IDE)

```simple
# Real-time preview of block content
val diagram = BlockBuilder("diagram")
    .preview_renderer(\content: render_svg(content))
    .build()
```

---

## Conclusion

This research demonstrates that custom block creation in Simple can be dramatically simplified while maintaining full power for advanced use cases. The proposed three-tier API provides:

1. **Accessibility:** Beginners can create blocks in 3 lines
2. **Scalability:** Intermediate users have fluent builder API
3. **Power:** Advanced users have full trait control

**Implementation is straightforward:** All foundation infrastructure exists. We're adding a thin, ergonomic layer on top.

**Timeline is reasonable:** 8 weeks for complete implementation including docs and examples.

**Risk is low:** Additive changes only, no breaking changes required.

**Value is high:** Dramatically improved user experience for library authors.

**Recommendation: Proceed with implementation starting with Phase 1 (Easy API).**

---

## Appendix: File Deliverables Summary

### Research Documents (Completed)

1. `doc/research/custom_blocks_user_friendly_api.md` - Full API design (800 lines)
2. `doc/guide/custom_blocks_quick_reference.md` - Quick reference (300 lines)
3. `doc/report/custom_blocks_easy_api_implementation_2026-02-05.md` - This report (600 lines)

### Test Specifications (Completed)

4. `test/compiler/custom_blocks_easy_api_spec.spl` - SSpec tests (600 lines)

### Implementation Files (To Be Created)

5. `src/compiler/blocks/easy.spl` - Minimal API (~200 lines)
6. `src/compiler/blocks/builder.spl` - Builder API (~400 lines)
7. `src/compiler/blocks/utils.spl` - Utilities (~500 lines)
8. `src/compiler/blocks/testing.spl` - Test helpers (~200 lines)

### Documentation (To Be Created)

9. `doc/guide/custom_blocks_tutorial.md` - Tutorial (~400 lines)
10. `doc/guide/custom_blocks_cookbook.md` - Cookbook (~600 lines)
11. `doc/guide/custom_blocks_api_reference.md` - API reference (~800 lines)
12. `doc/guide/custom_blocks_migration.md` - Migration guide (~300 lines)

### Total Deliverables

- **Completed:** 4 documents (2,300 lines)
- **To Implement:** 8 files (3,700 lines)
- **Total:** 12 deliverables (6,000 lines)

---

**Next Action:** Begin Phase 1 implementation of `compiler.blocks.easy` module.
