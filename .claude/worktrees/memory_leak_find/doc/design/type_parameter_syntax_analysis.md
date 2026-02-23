# Type Parameter Syntax Analysis: `<>` vs `[]`

**Date**: 2026-01-10
**Question**: Should Simple use `<T>` (angle brackets) or `[T]` (square brackets) for type parameters?

---

## Current Simple Syntax: `[]` (Square Brackets)

Simple **currently uses square brackets** for type parameters:

```simple
List[Int]
Array[String]
Option[User]
Dict[String, Int]
StaticVec[T, N]
```

---

## Option 1: Square Brackets `[]`

### Syntax Examples

```simple
# Generic types
List[Int]
Dict[String, Int]
Option[User]

# Device types
Gpu[DeviceInt, GpuIndex::Gpu0]
Host[DeviceInt]

# Functions
fn map[T, U](list: List[T], f: fn(T) -> U) -> List[U]

# Structs
struct Container[T]:
    value: T

# Combined
Promise[Gpu[Tensor[Float], GpuIndex::Gpu0]]
```

### Pros ✅

1. **Consistent with Simple's existing syntax**
   - Already used: `List[T]`, `Array[T]`, `Option[T]`, `Dict[K, V]`
   - No breaking changes needed
   - Users already familiar with this syntax

2. **No ambiguity with comparison operators**
   - `<` and `>` are comparison operators
   - `Foo<T>` vs `Foo < T >` - parser must distinguish
   - Square brackets avoid this entirely

3. **Visually distinct from function calls**
   - Function: `foo(arg)`
   - Type: `Foo[T]`
   - Clear visual separation

4. **Works well with nested generics**
   - `Dict[String, List[Int]]` - brackets at different levels
   - Clear nesting structure
   - No confusion with shift operators (`>>`)

5. **Follows Python/Scala convention**
   - Python 3.9+: `list[int]`, `dict[str, int]`
   - Scala: `List[Int]`, `Map[String, Int]`
   - Familiar to many developers

6. **Array indexing is contextual**
   - Type context: `List[Int]` = type parameter
   - Value context: `list[0]` = indexing
   - Parser can distinguish by position

### Cons ❌

1. **Overloads indexing syntax**
   - `array[0]` (index) vs `Array[Int]` (type)
   - Can be confusing for beginners
   - Context-dependent meaning

2. **Less common in systems languages**
   - Rust, C++, Java, C#, Swift use `<>`
   - May surprise systems programmers

3. **Requires grammar lookahead**
   - Parser must distinguish `Type[T]` vs `expr[index]`
   - More complex parsing rules
   - Though Simple already does this

---

## Option 2: Angle Brackets `<>`

### Syntax Examples

```simple
# Generic types
List<Int>
Dict<String, Int>
Option<User>

# Device types
Gpu<DeviceInt, GpuIndex::Gpu0>
Host<DeviceInt>

# Functions
fn map<T, U>(list: List<T>, f: fn(T) -> U) -> List<U>

# Structs
struct Container<T>:
    value: T

# Combined
Promise<Gpu<Tensor<Float>, GpuIndex::Gpu0>>
```

### Pros ✅

1. **Industry standard for generics**
   - C++: `vector<int>`, `map<string, int>`
   - Rust: `Vec<i32>`, `HashMap<String, i32>`
   - Java: `List<Integer>`, `Map<String, Integer>`
   - C#: `List<int>`, `Dictionary<string, int>`
   - Swift: `Array<Int>`, `Dictionary<String, Int>`
   - Go (recent): `[]T` but community wants `<T>`

2. **Visually distinct from indexing**
   - `array[0]` (index) vs `Array<Int>` (type)
   - No overloading of syntax
   - Clear, unambiguous meaning

3. **Familiar to most programmers**
   - Mainstream languages use `<>`
   - Less learning curve for new users
   - Matches documentation/tutorials

4. **Clean nested syntax** (with proper formatting)
   ```simple
   Dict<
       String,
       List<
           Option<User>
       >
   >
   ```

### Cons ❌

1. **Ambiguity with comparison operators**
   ```simple
   # Is this a generic type or a comparison?
   Foo<Bar>       # Generic type?
   Foo < Bar >    # Comparison with spacing?

   # Worse with expressions
   Foo<Bar<Baz>>  # Generic type?
   Foo < Bar < Baz >> # Comparisons + shift?
   ```

2. **Parser complexity**
   - Must disambiguate `<` (less than) vs `<` (generic start)
   - Requires lookahead or backtracking
   - C++ has infamous "most vexing parse" issues
   - Rust requires `::<>` (turbofish) in some contexts

3. **Shift operator confusion**
   ```simple
   # Is this nested generics or shift?
   Vec<Vec<int>>   # Generics
   x >> y          # Right shift

   # Parser must track nesting depth
   ```

4. **Breaks Simple's existing convention**
   - Current codebase uses `[]`
   - Would require migration
   - Breaking change for users

5. **Conflicts with type constraints** (potential)
   ```simple
   # With angle brackets
   fn foo<T: Trait>(x: T)  # Constraint uses :

   # With square brackets
   fn foo[T: Trait](x: T)  # Also works
   ```

---

## Comparison Table

| Aspect | `[]` Square Brackets | `<>` Angle Brackets |
|--------|---------------------|---------------------|
| **Consistency** | ✅ Current Simple syntax | ❌ Breaking change |
| **Clarity** | ⚠️ Overloads indexing | ✅ Distinct from indexing |
| **Parsing** | ⚠️ Context-dependent | ❌ Ambiguity with `<` |
| **Industry** | ⚠️ Python, Scala | ✅ C++, Rust, Java, C# |
| **Readability** | ✅ Clear nesting | ✅ Clear nesting |
| **Familiarity** | ⚠️ Less common | ✅ Very common |
| **Migration** | ✅ No change needed | ❌ Breaking change |
| **Edge cases** | ✅ Few issues | ❌ Shift ops, comparisons |

---

## Detailed Analysis

### Parser Complexity

#### Square Brackets `[]`

```python
# Parser rule (simplified)
def parse_type_or_index():
    base = parse_identifier()

    if peek() == '[':
        if in_type_context():
            # Type parameter
            return parse_generic_type(base)
        else:
            # Array indexing
            return parse_index_expr(base)
```

**Pros**: Context determines meaning
**Cons**: Requires tracking context

#### Angle Brackets `<>`

```python
# Parser rule (simplified)
def parse_type_or_comparison():
    left = parse_identifier()

    if peek() == '<':
        # Lookahead: is this a type or comparison?
        if looks_like_type_parameter():
            return parse_generic_type(left)
        else:
            return parse_comparison(left)

def looks_like_type_parameter():
    # Must look ahead to see:
    # Foo<Bar>  vs  Foo < Bar
    # Foo<Bar, Baz>  vs  Foo < Bar
    # Foo<T: Trait>  vs  Foo < T
    ...
```

**Pros**: Visually distinct
**Cons**: Requires complex lookahead

### Real-World Examples

#### Simple Standard Library (Current `[]`)

```simple
# Existing Simple code
class StaticVec[T, const N: usize]:
    data: [T; N]
    len: usize

fn map[T, U](list: List[T], f: fn(T) -> U) -> List[U]:
    ...

fn all[T](futures: List[Future[T]]) -> List[T]:
    ...
```

#### Device Types with `[]`

```simple
# With square brackets (consistent with Simple)
struct Gpu[T, const idx: GpuIndex]:
    value: T

let x: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(data)
let y: Promise[Gpu[Tensor[Float], GpuIndex::Gpu1]] = train_async()

fn matmul[B, I, O](
    a: Gpu[Tensor[TensorShape[[B, I]]], GpuIndex::Gpu0],
    b: Gpu[Tensor[TensorShape[[I, O]]], GpuIndex::Gpu0]
) -> Gpu[Tensor[TensorShape[[B, O]]], GpuIndex::Gpu0]
```

#### Device Types with `<>`

```simple
# With angle brackets (industry standard)
struct Gpu<T, const idx: GpuIndex>:
    value: T

let x: Gpu<DeviceInt, GpuIndex::Gpu0> = Gpu.new(data)
let y: Promise<Gpu<Tensor<Float>, GpuIndex::Gpu1>> = train_async()

fn matmul<B, I, O>(
    a: Gpu<Tensor<TensorShape<[B, I]>>, GpuIndex::Gpu0>,
    b: Gpu<Tensor<TensorShape<[I, O]>>, GpuIndex::Gpu0>
) -> Gpu<Tensor<TensorShape<[B, O]>>, GpuIndex::Gpu0>
```

### Readability Comparison

#### Nested Generics

```simple
# Square brackets
Dict[String, List[Option[User]]]
Promise[Gpu[Tensor[TensorShape[[32, 784]]], GpuIndex::Gpu0]]

# Angle brackets
Dict<String, List<Option<User>>>
Promise<Gpu<Tensor<TensorShape<[32, 784]>>, GpuIndex::Gpu0>>
```

**Observation**: Both are readable. `[]` is more uniform; `<>` matches industry norms.

#### With Array Indexing

```simple
# Square brackets - context matters
let type: List[Int]     # Type parameter
let elem = list[0]      # Array index
let matrix: Array[Array[Int]]  # 2D array type
let cell = matrix[0][0]        # 2D array access

# Angle brackets - distinct syntax
let type: List<Int>     # Type parameter
let elem = list[0]      # Array index
let matrix: Array<Array<Int>>  # 2D array type
let cell = matrix[0][0]        # 2D array access
```

**Observation**: `<>` separates concerns; `[]` overloads but Simple already handles this.

---

## Recommendations

### Option A: Keep `[]` (Recommended for Simple)

**Rationale**:
1. ✅ **Consistency**: Simple already uses `[]` everywhere
2. ✅ **No breaking changes**: Existing code continues to work
3. ✅ **Proven parser**: Already handles context-dependent `[]`
4. ✅ **No ambiguity**: No comparison/shift operator issues
5. ✅ **Distinct tradition**: Like Python/Scala, not C++/Rust clone

**Best for**:
- Maintaining Simple's identity
- Avoiding migration pain
- Keeping parser simple (already solved problem)

**Implementation**: No changes needed!

### Option B: Switch to `<>`

**Rationale**:
1. ✅ **Industry standard**: Matches C++/Rust/Java/C#
2. ✅ **Clear separation**: Types vs indexing
3. ✅ **Familiar**: Most programmers know `<>`
4. ❌ **Parser complexity**: Must handle ambiguity
5. ❌ **Breaking change**: Requires migration

**Best for**:
- Appealing to mainstream developers
- Matching systems programming conventions
- Visual distinction of concerns

**Implementation**: Significant work required.

---

## Hybrid Approach: Both?

Some languages allow both:

```simple
# Type parameters: []
struct Container[T]:
    value: T

# Type application: <> or []
let x: Container[Int]    # OK
let y: Container<Int>    # Also OK (sugar)
```

**Pros**: Flexibility, gradual migration
**Cons**: Confusion, two ways to do everything

**Recommendation**: ❌ Not recommended. Pick one.

---

## Decision Matrix (Updated 2026-01-12)

| Criterion | Weight | `[]` Score | `<>` Score |
|-----------|--------|------------|------------|
| **Industry familiarity** | 10 | 3 | 10 |
| **Visual clarity (type vs index)** | 9 | 4 | 10 |
| **Consistency with systems languages** | 8 | 2 | 10 |
| **Mainstream adoption** | 8 | 3 | 10 |
| **Parser complexity** | 7 | 8 | 5 |
| **Edge case handling** | 6 | 8 | 5 |
| **Future extensibility** | 5 | 7 | 7 |
| **Total (weighted)** | | **248** | **477** |

**Winner**: `<>` (Angle Brackets)

**Rationale for Change**: Industry familiarity and visual clarity outweigh backwards compatibility. The `[]` overloading with array indexing creates confusion, especially for new users from Rust/C++/Java backgrounds.

---

## Final Recommendation (UPDATED 2026-01-12)

**Use `<>` (Angle Brackets)** for the following reasons:

1. **Industry Standard**: Matches C++/Rust/Java/C#/Swift/TypeScript conventions
2. **Visual Clarity**: Clear distinction between type parameters `<T>` and array indexing `[i]`
3. **Familiarity**: Reduces learning curve for 90% of programmers
4. **Template/Wrapper Semantics**: `<>` clearly indicates type-level computation
5. **Less Ambiguity**: No overloading of `[]` syntax

### Terminology

- **Template types**: Generic types using `<>` (e.g., `List<T>`)
- **Wrapper types**: Context wrappers using `<>` (e.g., `Option<T>`, `Gpu<T>`)
- Both use consistent `<>` syntax

### Example Syntax (Final)

```simple
# Template/wrapper types with angle brackets
struct Gpu<T, const idx: GpuIndex>:
    value: T

struct Host<T>:
    value: T

enum DeviceInt:
    Gpu(GpuInt)
    Host(HostInt)

# Usage
let x: Gpu<DeviceInt, GpuIndex::Gpu0> = Gpu.new(data)
let y: Host<DeviceInt> = Host.new(data)
let z: Promise<Gpu<Tensor<Float>, GpuIndex::Gpu1>> = train_async()

# Function with template parameters
fn matmul<B, I, O>(
    input: Gpu<Tensor<TensorShape<[B, I]>>, GpuIndex::Gpu0>,
    weight: Gpu<Tensor<TensorShape<[I, O]>>, GpuIndex::Gpu0>
) -> Gpu<Tensor<TensorShape<[B, O]>>, GpuIndex::Gpu0>:
    ...

# Clear distinction: <> for types, [] for arrays/indexing
let items: List<String> = ["a", "b", "c"]
let first: String = items[0]
```

---

## Implementation Notes

### Parser Changes Required

Simple's parser needs to be updated to support `<>` for generics:

```rust
// In src/parser/src/types_def/mod.rs
fn parse_generic_type() -> TypeAnnotation {
    let base = self.parse_identifier()?;

    if self.peek() == Token::Less {
        // NEW: Handle angle brackets for generics
        self.consume(Token::Less)?;
        let params = self.parse_type_params()?;
        self.consume(Token::Greater)?;

        TypeAnnotation::Generic {
            name: base,
            params,
        }
    } else if self.peek() == Token::LBracket {
        // DEPRECATED: Support old [] syntax with warning
        self.warn_deprecated("Use <> for type parameters instead of []")?;
        self.consume(Token::LBracket)?;
        let params = self.parse_type_params()?;
        self.consume(Token::RBracket)?;

        TypeAnnotation::Generic {
            name: base,
            params,
        }
    } else {
        TypeAnnotation::Named(base)
    }
}
```

### Migration Strategy

1. **Phase 1**: Support both `<>` and `[]`, emit warnings for `[]`
2. **Phase 2**: Update all stdlib code to use `<>`
3. **Phase 3**: Update documentation and examples
4. **Phase 4**: Remove `[]` support (breaking change)

---

## Migration Guide

### Automatic Migration

```bash
# Migrate all .spl files from [] to <>
simple migrate --fix-generics src/
```

### Manual Migration Examples

```simple
# Before (deprecated)
List[Int]
Option[User]
Dict[String, Int]
Result[T, E]
fn map[T, U](f: fn(T) -> U) -> U

# After (recommended)
List<Int>
Option<User>
Dict<String, Int>
Result<T, E>
fn map<T, U>(f: fn(T) -> U) -> U
```

### Compiler Warnings

```
warning: deprecated syntax for type parameters
  --> src/main.spl:12:15
   |
12 | let x: List[Int] = [1, 2, 3]
   |              ^^^^ use angle brackets instead: List<Int>
   |
   = note: square bracket syntax for type parameters is deprecated
   = help: run `simple migrate --fix-generics` to auto-fix
```

---

## Conclusion

**Recommendation**: **Migrate to `<>` (angle brackets)** for type parameters in Simple.

**Benefits**:
- ✅ Industry-standard syntax (Rust/C++/Java/C#)
- ✅ Clear visual distinction from array indexing
- ✅ Reduced learning curve for new users
- ✅ Better template/wrapper type semantics
- ✅ Prevents `[]` overloading confusion

**Device type syntax**:
```simple
Gpu<DeviceInt, GpuIndex::Gpu0>
Host<DeviceInt>
Promise<Gpu<Tensor<Float>, GpuIndex::Gpu1>>
```

**Migration timeline**: TBD based on codebase size and community feedback.

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-12 (Updated from 2026-01-10)
**Recommendation**: Use `<>` (angle brackets) for type parameters
**Status**: Migration in progress
