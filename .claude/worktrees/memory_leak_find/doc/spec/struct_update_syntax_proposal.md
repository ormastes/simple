# Struct Update Syntax - Language Feature Proposal

**Priority:** P0 (CRITICAL - Blocks 15+ migrations)
**Status:** Proposal
**Date:** 2026-01-20
**Impact:** Would reduce builder pattern code by 50-70%

---

## Problem Statement

The sandbox.rs migration revealed a critical language limitation: **no struct update syntax** in Simple.

**Current situation:**
- Builder pattern migrations result in **+171% code expansion**
- Each builder method must **manually copy all fields**
- 15+ files blocked waiting for this feature
- Immutable builders completely impractical in Simple

**Example from sandbox.spl:**
```simple
fn with_memory(bytes: u64) -> SandboxConfig:
    SandboxConfig(
        time_limit_secs: time_limit_secs,      # Copy field 1
        memory_limit_bytes: Some(bytes),        # Updated field
        cpu_limit_percent: cpu_limit_percent,   # Copy field 2
        fd_limit: fd_limit,                     # Copy field 3
        thread_limit: thread_limit,             # Copy field 4
        stack_size_bytes: stack_size_bytes,     # Copy field 5
        heap_size_bytes: heap_size_bytes,       # Copy field 6
        allowed_syscalls: allowed_syscalls,     # Copy field 7
        network_enabled: network_enabled        # Copy field 8
    )
```

**Rust equivalent (1-2 lines):**
```rust
fn with_memory(self, bytes: u64) -> SandboxConfig {
    SandboxConfig { memory_limit_bytes: Some(bytes), ..self }
}
```

**Impact:** 9 fields × 18 lines per method × 9 methods = **162 lines of boilerplate**

---

## Proposed Solution

Add struct update syntax similar to Rust's `..` syntax.

### Option 1: Rust-Style (Recommended)

**Syntax:**
```simple
StructName(..base, field: new_value)
```

**Example:**
```simple
struct Point:
    x: i32
    y: i32
    z: i32

impl Point:
    fn with_x(new_x: i32) -> Point:
        Point(..self, x: new_x)  # Update x, copy rest

    fn with_y(new_y: i32) -> Point:
        Point(..self, y: new_y)  # Update y, copy rest

    fn translate(dx: i32, dy: i32, dz: i32) -> Point:
        Point(..self, x: x + dx, y: y + dy, z: z + dz)
```

**Benefits:**
- Familiar to Rust developers
- Clear "spread" semantics
- Works in any expression context

**Semantics:**
- `..base` must come before updated fields
- `base` is evaluated once
- Updated fields override base fields
- All fields must be covered (base + updates)

---

### Option 2: Inline Spread

**Syntax:**
```simple
StructName(field: new_value, ...self)
```

**Example:**
```simple
fn with_x(new_x: i32) -> Point:
    Point(x: new_x, ...self)
```

**Benefits:**
- Similar to JavaScript spread
- Allows updates before or after spread

**Drawbacks:**
- `...` vs `..` could be confusing
- Less clear which takes precedence

---

### Option 3: With Expression

**Syntax:**
```simple
base with field: new_value
```

**Example:**
```simple
fn with_x(new_x: i32) -> Point:
    self with x: new_x
```

**Benefits:**
- Very clear semantics
- Keyword-based (no operators)

**Drawbacks:**
- New keyword `with`
- Different from Rust
- Harder to chain: `(base with x: 1) with y: 2`

---

## Recommendation: Option 1 (Rust-Style)

Use `..base` syntax for the following reasons:

1. **Familiarity:** Rust developers already know this syntax
2. **Clarity:** `..` clearly indicates "spread remaining fields"
3. **Consistency:** Matches Rust semantics exactly
4. **Proven:** Rust has used this successfully for years
5. **Tooling:** LSP/IDE support easier (same as Rust)

---

## Detailed Specification

### Syntax Grammar

```
struct_construction:
    | TypeName '(' struct_update ')'

struct_update:
    | '..' expr ',' field_updates  # Update syntax
    | field_updates                # Normal syntax

field_updates:
    | field_update (',' field_update)* ','?

field_update:
    | identifier ':' expr
```

### Semantics

**Evaluation order:**
1. Evaluate base expression (`..base`)
2. Evaluate all field expressions (left to right)
3. Construct new struct:
   - Start with all fields from base
   - Override with explicitly provided fields
4. Return new struct

**Type checking:**
1. Base expression must have same type as constructed struct
2. Updated fields must match struct field types
3. All struct fields must be present (base + updates)

**Example:**
```simple
struct Config:
    host: text
    port: i32
    timeout: i32
    retries: i32

impl Config:
    static fn default() -> Config:
        Config(host: "localhost", port: 8080, timeout: 30, retries: 3)

    fn with_port(new_port: i32) -> Config:
        Config(..self, port: new_port)
        # Equivalent to:
        # Config(
        #     host: self.host,
        #     port: new_port,
        #     timeout: self.timeout,
        #     retries: self.retries
        # )

    fn with_timeout_and_retries(new_timeout: i32, new_retries: i32) -> Config:
        Config(..self, timeout: new_timeout, retries: new_retries)
```

---

## Error Handling

### Error: Missing base or fields

```simple
fn bad_update() -> Point:
    Point(..self, x: 10)  # Error if not all fields covered by base + updates
```

**Error message:**
```
error: struct update missing field(s): y, z
  --> example.spl:5:9
   |
 5 |     Point(..self, x: 10)
   |     ^^^^^^^^^^^^^^^^^^^^ missing fields: y, z
   |
help: provide the missing fields or ensure base has them
```

### Error: Duplicate field

```simple
fn bad_update() -> Point:
    Point(..self, x: 10, x: 20)  # Error: x specified twice
```

**Error message:**
```
error: field `x` specified more than once
  --> example.spl:5:26
   |
 5 |     Point(..self, x: 10, x: 20)
   |                          ^ duplicate field
```

### Error: Base type mismatch

```simple
fn bad_update(other: OtherStruct) -> Point:
    Point(..other, x: 10)  # Error: other is not a Point
```

**Error message:**
```
error: cannot use type `OtherStruct` as base for `Point`
  --> example.spl:5:15
   |
 5 |     Point(..other, x: 10)
   |               ^^^^^ expected `Point`, found `OtherStruct`
```

---

## Migration Impact Analysis

### Files Currently Blocked (15+)

All of these would benefit from struct update syntax:

1. **sandbox.rs** (94 lines → 255 lines, would become 94 → 120 lines with syntax)
   - 9 fields, 9 builder methods
   - Current: +171% expansion
   - With syntax: +27% expansion (acceptable)

2. **compile_commands.rs** (~200 lines, builder pattern)
3. **web_commands.rs** (~150 lines, config building)
4. **test_runner/config.rs** (~180 lines, builder pattern)
5. **pkg/manifest.rs** (~250 lines, nested builders)
6. **lint/rules.rs** (~140 lines, rule builders)
7. **codegen/options.rs** (~160 lines, codegen config)
8. **runtime/gc_config.rs** (~120 lines, GC tuning)
9. **interpreter/options.rs** (~130 lines, interpreter config)
10. **compiler/session.rs** (~300 lines, compiler session)
11. **driver/cli_options.rs** (~220 lines, CLI config)
12. **parser/parser_config.rs** (~110 lines, parser options)
13. **lexer/lexer_config.rs** (~90 lines, lexer options)
14. **mir/optimization_config.rs** (~140 lines, optimizer config)
15. **hir/lowering_options.rs** (~100 lines, lowering config)

**Total blocked:** ~2,400 lines of Rust code
**Estimated with current Simple:** ~6,500 lines (+171% avg)
**Estimated with update syntax:** ~2,900 lines (+20% avg)

**Savings:** ~3,600 lines of boilerplate eliminated

---

## Implementation Plan

### Phase 1: Parser (2-3 hours)

**Tasks:**
1. Add `..` token to lexer
2. Parse `..expr` in struct construction
3. Allow mixing `..base` with field updates
4. Ensure `..base` comes before field updates
5. Add syntax tests

**Files to modify:**
- `src/parser/src/lexer/mod.rs` - Add `..` token
- `src/parser/src/expressions/struct_construction.rs` - Parse struct update
- `src/parser/tests/struct_update_tests.rs` - Syntax tests

### Phase 2: Type Checking (3-4 hours)

**Tasks:**
1. Type check base expression
2. Verify base type matches struct type
3. Check all fields covered (base + updates)
4. Detect duplicate fields
5. Generate helpful error messages

**Files to modify:**
- `src/compiler/src/hir/type_checker.rs` - Type check struct update
- `src/compiler/src/hir/lower/expr_lowering.rs` - Lower to HIR
- `src/compiler/tests/type_checker/struct_update_tests.rs` - Type tests

### Phase 3: Code Generation (2-3 hours)

**Tasks:**
1. Evaluate base expression
2. Extract all base fields
3. Evaluate update expressions
4. Construct new struct with updated fields
5. Optimize (avoid copying if possible)

**Files to modify:**
- `src/compiler/src/mir/mir_gen.rs` - Generate MIR for struct update
- `src/compiler/src/codegen/struct_construction.rs` - Codegen
- `src/compiler/src/interpreter/struct_construction.rs` - Interpreter support

### Phase 4: Testing & Documentation (2 hours)

**Tasks:**
1. Write comprehensive tests
2. Test with sandbox.rs migration
3. Update language documentation
4. Add to cookbook

**Files to modify:**
- `simple/std_lib/test/features/struct_update_spec.spl` - Feature tests
- `doc/guide/struct_update.md` - User guide
- `doc/guide/migration_pattern_cookbook.md` - Add examples

**Total estimated time:** 9-12 hours

---

## Examples from Real Migrations

### Example 1: SandboxConfig (sandbox.rs)

**Before (255 lines):**
```simple
impl SandboxConfig:
    fn with_memory(bytes: u64) -> SandboxConfig:
        SandboxConfig(
            time_limit_secs: time_limit_secs,
            memory_limit_bytes: Some(bytes),
            cpu_limit_percent: cpu_limit_percent,
            fd_limit: fd_limit,
            thread_limit: thread_limit,
            stack_size_bytes: stack_size_bytes,
            heap_size_bytes: heap_size_bytes,
            allowed_syscalls: allowed_syscalls,
            network_enabled: network_enabled
        )
```

**After (120 lines):**
```simple
impl SandboxConfig:
    fn with_memory(bytes: u64) -> SandboxConfig:
        SandboxConfig(..self, memory_limit_bytes: Some(bytes))
```

**Savings:** 162 lines (9 methods × 18 lines → 9 methods × 1-2 lines)

### Example 2: Complex Update

**Updating multiple fields:**
```simple
fn configure_limits(mem: u64, cpu: i32, fds: i32) -> SandboxConfig:
    SandboxConfig(
        ..self,
        memory_limit_bytes: Some(mem),
        cpu_limit_percent: Some(cpu),
        fd_limit: Some(fds)
    )
```

### Example 3: Chaining

**Builder-style chaining:**
```simple
val config = SandboxConfig.default()
    .with_memory(1024 * 1024 * 1024)  # 1GB
    .with_cpu(50)                      # 50%
    .with_threads(4)                   # 4 threads
    .with_timeout(60)                  # 60 seconds
```

---

## Alternative Workarounds (Current)

While waiting for struct update syntax, these workarounds exist:

### Workaround 1: Use Mutable Struct (Recommended)

**Instead of builder pattern, use mutation:**
```simple
var config = SandboxConfig.default()
config.memory_limit_bytes = Some(1024 * 1024 * 1024)
config.cpu_limit_percent = Some(50)
config.fd_limit = Some(1024)
```

**Pros:**
- ✅ Same code size as Rust
- ✅ Familiar pattern (test_args.rs migration)

**Cons:**
- ❌ Not immutable
- ❌ Can't chain
- ❌ Not as fluent as builder

### Workaround 2: Accept Verbosity

**Just write out all the fields:**
```simple
fn with_memory(bytes: u64) -> SandboxConfig:
    SandboxConfig(
        time_limit_secs: time_limit_secs,
        memory_limit_bytes: Some(bytes),
        # ... all 9 fields ...
    )
```

**Pros:**
- ✅ Immutable
- ✅ Type safe

**Cons:**
- ❌ +171% code expansion
- ❌ Error-prone (easy to forget field)
- ❌ Hard to maintain (adding field requires updating all methods)

---

## Comparison with Other Languages

### Rust
```rust
Config { port: 8080, ..base }
```

### JavaScript
```javascript
{ ...base, port: 8080 }
```

### Python (dataclasses)
```python
replace(base, port=8080)
```

### Kotlin
```kotlin
base.copy(port = 8080)
```

### Swift
```swift
Config(base, port: 8080)  # Not directly supported, uses .copy()
```

**Observation:** Most modern languages support some form of struct/object update syntax.

---

## Testing Strategy

### Unit Tests

**Syntax tests:**
```simple
describe "struct update syntax":
    it "updates single field":
        val p1 = Point(x: 1, y: 2, z: 3)
        val p2 = Point(..p1, x: 10)
        expect p2.x == 10
        expect p2.y == 2
        expect p2.z == 3

    it "updates multiple fields":
        val p1 = Point(x: 1, y: 2, z: 3)
        val p2 = Point(..p1, x: 10, z: 30)
        expect p2.x == 10
        expect p2.y == 2
        expect p2.z == 30

    it "base can be expression":
        val p2 = Point(..Point(x: 1, y: 2, z: 3), x: 10)
        expect p2.x == 10
```

**Type error tests:**
```simple
describe "struct update type errors":
    it "rejects wrong base type":
        val other = OtherStruct()
        val p = Point(..other, x: 10)  # Error

    it "rejects duplicate field":
        val p1 = Point(x: 1, y: 2, z: 3)
        val p2 = Point(..p1, x: 10, x: 20)  # Error

    it "requires all fields":
        val p2 = Point(..incomplete_base)  # Error if missing fields
```

### Integration Tests

**Real-world usage:**
- Migrate sandbox.rs with new syntax
- Verify 50-70% code reduction
- Ensure all tests pass
- Benchmark performance (should be same as manual)

---

## Performance Considerations

**Expected performance:**
- Same as manual field copy
- Compiler can optimize if `base` not used after
- May enable move semantics in future

**Optimization opportunities:**
1. If `base` is last use, move fields instead of copy
2. If only one field updated, can reuse base allocation
3. If struct is `Copy`, no allocation needed

---

## Documentation Needs

### User Guide
- Syntax introduction
- Examples with various patterns
- When to use vs mutable pattern
- Common pitfalls

### API Documentation
- Add to struct construction docs
- Show in builder pattern examples
- Migrate existing examples to use syntax

### Migration Guide
- How to convert manual construction
- How to convert mutable patterns
- When to prefer each approach

---

## Success Criteria

**Implementation complete when:**
1. ✅ Syntax parses correctly
2. ✅ Type checking works
3. ✅ Codegen produces correct code
4. ✅ Interpreter supports it
5. ✅ All tests pass
6. ✅ sandbox.rs migration reduced by 50%+
7. ✅ Documentation written
8. ✅ 15+ blocked migrations can proceed

---

## Conclusion

**Struct update syntax is CRITICAL for Simple's success.**

**Without it:**
- Builder patterns result in +171% code expansion
- 15+ migrations blocked
- 2,400+ lines of Rust → 6,500+ lines of Simple
- Migration process severely handicapped

**With it:**
- Builder patterns result in +20% code expansion (acceptable)
- All migrations unblocked
- 2,400+ lines of Rust → 2,900+ lines of Simple
- Migration process can continue smoothly

**Recommendation:** **Implement as P0 priority** (9-12 hours estimated)

**Impact:** Unlocks ~15 migrations, saves ~3,600 lines of boilerplate, makes Simple viable for real-world code.

---

**Status:** Ready for implementation
**Estimated effort:** 9-12 hours
**Return on investment:** Massive (unlocks major functionality)
**Risk:** Low (well-understood feature, proven in Rust)
