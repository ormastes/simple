# TODO: Remove `Any` Type from Compiler

**Priority:** P2 (Medium)
**Status:** Planned
**Effort:** Large (8-12 weeks)
**Created:** 2026-02-08

## Background

The `Any` type is currently used throughout the compiler and standard library as a type-erased container. While convenient, it has several drawbacks:

1. **Type Safety Loss:** Defeats the purpose of static typing
2. **Runtime Overhead:** Requires boxing/unboxing and type checking
3. **Error Prone:** Type errors caught at runtime instead of compile time
4. **API Clarity:** Unclear what types are actually expected

## Current Usage

Found **85 files** using `Any` type across the codebase:

### Type Alias (1 file)
- `src/std/actors/actor.spl:273`: `type Any = text` (temporary workaround)

### Concurrency/Runtime FFI (15 files)
**High Priority - Core Runtime:**
- `src/std/concurrent.spl` - Channel, HashMap FFI (5 uses)
- `src/std/concurrent/actor.spl` - Actor spawn/send (4 uses)
- `src/std/concurrent/channel.spl` - Channel send (2 uses)
- `src/std/concurrent/mutex.spl` - Mutex operations (7 uses)
- `src/std/concurrent/rwlock.spl` - RwLock operations (9 uses)
- `src/std/concurrent/thread.spl` - Thread spawn (4 uses)
- `src/std/concurrent/collections.spl` - HashMap/BTreeMap insert (4 uses)

### Compiler Internals (12 files)
**Medium Priority - Type System:**
- `src/compiler/di.spl` - Dependency injection (4 uses)
- `src/compiler/instantiation.spl` - Generic instantiation cache (1 use)
- `src/compiler/init.spl` - Initialization data (1 use)
- `src/compiler/compilation_context.spl` - Type storage (2 uses)
- `src/compiler/macro_contracts.spl` - Introduced classes (1 use)
- `src/compiler/blocks/value.spl` - Custom block values (1 use)
- `src/compiler/monomorphize/engine.spl` - Monomorphization cache (6 uses)
- `src/compiler/api_surface.spl` - Field type fallback (1 use)
- `src/compiler/async_integration.spl` - Result type placeholder (1 use)
- `src/compiler/driver.spl` - Compilation results (1 use)

### Documentation (1 file)
- `src/std/actors/actor.spl` - Comment: "would be [Any]" (1 use)

### Test Files (2 files)
- `test/lib/std/unit/dap/dap_spec.spl` - Cast to `List<Dict<text, Any>>` (2 uses)

### External Files (54 files)
- VSCode extension, Python bridges, syntax files - ignore

## Replacement Strategy

### Phase 1: Concurrency Runtime FFI (4 weeks) ⭐ **START HERE**

Replace `Any` in FFI declarations with typed alternatives:

**Option 1: Generic FFI Functions**
```simple
# Before
extern fn rt_channel_send(channel_id: i64, value: Any)

# After
extern fn rt_channel_send<T>(channel_id: i64, value: T)
```

**Option 2: RuntimeValue Type**
```simple
# Use existing RuntimeValue type from runtime
extern fn rt_channel_send(channel_id: i64, value: RuntimeValue)
```

**Option 3: Concrete Union Types**
```simple
# Define specific value types
enum ChannelValue:
    Int(i64)
    Text(text)
    Bool(bool)
    Custom(RuntimeValue)

extern fn rt_channel_send(channel_id: i64, value: ChannelValue)
```

**Files to Update (Priority Order):**
1. ✅ `src/std/concurrent/channel.spl` - Channel send (2 uses)
2. ✅ `src/std/concurrent/actor.spl` - Actor spawn/send (4 uses)
3. ✅ `src/std/concurrent/mutex.spl` - Mutex lock/unlock (7 uses)
4. ✅ `src/std/concurrent/rwlock.spl` - RwLock read/write (9 uses)
5. ✅ `src/std/concurrent/thread.spl` - Thread spawn (4 uses)
6. ✅ `src/std/concurrent/collections.spl` - HashMap/BTreeMap (4 uses)
7. ✅ `src/std/concurrent.spl` - Main concurrency module (5 uses)

**Estimated Effort:** 4 weeks (1 week per group)

### Phase 2: Compiler Type System (6 weeks)

Replace `Any` in compiler internals with proper types:

**DI Container (src/compiler/di.spl):**
```simple
# Before
class Container:
    bindings: Dict<text, fn() -> Any>
    singletons: Dict<text, Any>

# After (Option 1: Generic container)
class Container<T>:
    bindings: Dict<text, fn() -> T>
    singletons: Dict<text, T>

# After (Option 2: Typed registrations)
class TypedBinding<T>:
    factory: fn() -> T
    singleton: T?

class Container:
    bindings: Dict<text, TypedBinding<RuntimeValue>>
```

**Monomorphization Engine (src/compiler/monomorphize/):**
```simple
# Before
class MonomorphizationEngine:
    specialized_classes: {text: Any}
    generic_classes: {text: Any}

# After
class MonomorphizationEngine:
    specialized_classes: {text: ClassDefinition}
    generic_classes: {text: GenericClassDef}
```

**Compilation Context (src/compiler/compilation_context.spl):**
```simple
# Before
class CompilationContext:
    types: Dict<text, Any>

# After
class CompilationContext:
    types: Dict<text, TypeInfo>

enum TypeInfo:
    Primitive(PrimitiveType)
    Class(ClassDef)
    Generic(GenericDef)
    Function(FunctionType)
```

**Files to Update:**
1. ✅ `src/compiler/di.spl` (4 uses)
2. ✅ `src/compiler/monomorphize/engine.spl` (6 uses)
3. ✅ `src/compiler/compilation_context.spl` (2 uses)
4. ✅ `src/compiler/instantiation.spl` (1 use)
5. ✅ `src/compiler/macro_contracts.spl` (1 use)
6. ✅ `src/compiler/blocks/value.spl` (1 use)
7. ✅ `src/compiler/init.spl` (1 use)
8. ✅ `src/compiler/driver.spl` (1 use)
9. ✅ `src/compiler/async_integration.spl` (1 use)
10. ✅ `src/compiler/api_surface.spl` (1 use - fallback)

**Estimated Effort:** 6 weeks

### Phase 3: Test Files (1 week)

**DAP Tests (test/lib/std/unit/dap/dap_spec.spl):**
```simple
# Before
val bps = result.get("breakpoints") as List<Dict<text, Any>>
val threads = result.get("threads") as List<Dict<text, Any>>

# After (Option 1: Specific types)
val bps = result.get("breakpoints") as List<BreakpointDict>
val threads = result.get("threads") as List<ThreadDict>

# After (Option 2: Remove cast)
val bps_text = result.get("breakpoints") ?? ""
expect(bps_text.contains("\"id\":\"1\""))
```

**Files to Update:**
1. ✅ `test/lib/std/unit/dap/dap_spec.spl` (2 uses)

**Estimated Effort:** 1 week

### Phase 4: Type Alias Removal (1 week)

Remove the temporary type alias:

**src/std/actors/actor.spl:**
```simple
# Before
type Any = text  # Temporary workaround

# After
# Remove line completely
# Update args field to use proper type
class ActorMessage:
    args: [RuntimeValue]  # Or specific union type
```

**Estimated Effort:** 1 week

## Implementation Order

### Recommended Sequence (12 weeks total)

**Week 1-4: Concurrency Runtime FFI** ⭐
- Week 1: Channel + Actor
- Week 2: Mutex + RwLock
- Week 3: Thread + Collections
- Week 4: Main concurrent.spl + integration testing

**Week 5-10: Compiler Type System**
- Week 5: DI Container + Instantiation
- Week 6-7: Monomorphization Engine (complex)
- Week 8: Compilation Context + Macro Contracts
- Week 9: Block Values + Init
- Week 10: Driver + Async + API Surface

**Week 11: Test Files**
- Week 11: DAP tests + verification

**Week 12: Cleanup & Documentation**
- Week 12: Remove type alias, update docs, final testing

## Benefits

### Type Safety ✅
- Catch type errors at compile time
- Better IDE autocomplete
- Clearer API contracts

### Performance ✅
- Eliminate runtime type checking
- Reduce boxing/unboxing overhead
- Enable better optimizations

### Code Quality ✅
- Self-documenting code
- Easier to understand APIs
- Fewer runtime errors

### Maintainability ✅
- Easier refactoring
- Better error messages
- Clearer dependencies

## Risks & Mitigation

### Risk 1: Breaking Changes
**Impact:** High - Affects 85 files
**Mitigation:**
- Phase implementation over 12 weeks
- Maintain backward compatibility where possible
- Create migration guide
- Run full test suite after each phase

### Risk 2: Generic System Complexity
**Impact:** Medium - May require generic constraint improvements
**Mitigation:**
- Start with simple cases (channels, actors)
- Use RuntimeValue for complex cases initially
- Iterate based on real usage patterns

### Risk 3: Runtime FFI Contracts
**Impact:** High - Must match Rust FFI signatures
**Mitigation:**
- Verify FFI changes with runtime team
- Test each FFI function thoroughly
- Update Rust side simultaneously

### Risk 4: Performance Regression
**Impact:** Medium - More specific types may add overhead
**Mitigation:**
- Benchmark before/after each phase
- Profile critical paths
- Optimize hot paths

## Testing Strategy

### Phase Testing
1. **Unit Tests:** Add tests for new typed APIs
2. **Integration Tests:** Verify cross-module compatibility
3. **Regression Tests:** Ensure existing functionality unchanged
4. **Performance Tests:** Benchmark critical operations

### Coverage Goals
- 100% test coverage for changed modules
- No performance regression
- All existing tests pass
- New type-safe tests added

## Migration Path

### For Library Users

**Before:**
```simple
use std.concurrent.{channel_send}

val ch = channel_create()
channel_send(ch, "any value")  # Accepts Any
```

**After:**
```simple
use std.concurrent.{channel_send, ChannelValue}

val ch = channel_create<text>()  # Generic channel
channel_send(ch, "typed value")  # Type-checked

# OR with union types
val ch = channel_create()
channel_send(ch, ChannelValue.Text("value"))  # Explicit variant
```

### For Compiler Developers

**Before:**
```simple
class Container:
    singletons: Dict<text, Any>

container.singletons["foo"] = some_value  # No type checking
```

**After:**
```simple
class Container:
    singletons: Dict<text, RuntimeValue>

container.singletons["foo"] = RuntimeValue.from(some_value)  # Typed
```

## Success Metrics

- [ ] Zero uses of `Any` type in src/compiler/ (except deprecated)
- [ ] Zero uses of `Any` type in src/std/concurrent/ (except deprecated)
- [ ] All tests passing (current: 262/273 debug/DAP)
- [ ] No performance regression (<5% slowdown)
- [ ] Documentation updated
- [ ] Migration guide complete

## Related Work

- [ ] Improve generic constraint system (if needed)
- [ ] Add RuntimeValue helpers for common conversions
- [ ] Create typed wrapper APIs for FFI
- [ ] Document type-safe patterns

## References

- **Type Safety:** `doc/design/type_system_design.md`
- **Runtime FFI:** `src/std/runtime/value.spl`
- **Generic System:** `doc/guide/generics_guide.md`
- **This Report:** `doc/report/debug_dap_complete_session_2026-02-08.md` (DAP `Any` limitation)

## Decision Log

**2026-02-08:** Created TODO list based on DAP test analysis
- Motivation: 2 DAP tests failing due to `Any` type casts
- Decision: Remove `Any` entirely for better type safety
- Approach: 4-phase migration over 12 weeks
- Priority: P2 (after current test fixes complete)

---

**Next Steps:**
1. ✅ Get team approval for removal strategy
2. ✅ Create tracking issue in bug database
3. ✅ Schedule Phase 1 for Q2 2026
4. ✅ Assign owner for each phase
5. ✅ Set up CI checks to prevent new `Any` usage

**Owner:** TBD
**Start Date:** TBD (after current session complete)
**Target Completion:** Q2 2026
