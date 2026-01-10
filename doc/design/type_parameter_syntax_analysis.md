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

## Decision Matrix

| Criterion | Weight | `[]` Score | `<>` Score |
|-----------|--------|------------|------------|
| **Consistency with Simple** | 10 | 10 | 0 |
| **Parser simplicity** | 8 | 8 | 3 |
| **Industry familiarity** | 7 | 3 | 10 |
| **Visual clarity** | 6 | 6 | 8 |
| **No breaking changes** | 9 | 10 | 0 |
| **Edge case handling** | 7 | 8 | 4 |
| **Future extensibility** | 5 | 7 | 7 |
| **Total (weighted)** | | **352** | **232** |

**Winner**: `[]` (Square Brackets)

---

## Final Recommendation

**Use `[]` (Square Brackets)** for the following reasons:

1. **Consistency**: Simple already uses `[]` throughout the codebase
2. **No breaking changes**: Existing code continues to work
3. **Parser simplicity**: Already solved, no new complexity
4. **Distinctive**: Sets Simple apart from C++/Rust clones
5. **Python/Scala lineage**: Good company for modern languages

### Example Syntax (Final)

```simple
# Device types with square brackets
struct Gpu[T, const idx: GpuIndex]:
    value: T

struct Host[T]:
    value: T

enum DeviceInt:
    Gpu(GpuInt)
    Host(HostInt)

# Usage
let x: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(data)
let y: Host[DeviceInt] = Host.new(data)
let z: Promise[Gpu[Tensor[Float], GpuIndex::Gpu1]] = train_async()

# Function
fn matmul[B, I, O](
    input: Gpu[Tensor[TensorShape[[B, I]]], GpuIndex::Gpu0],
    weight: Gpu[Tensor[TensorShape[[I, O]]], GpuIndex::Gpu0]
) -> Gpu[Tensor[TensorShape[[B, O]]], GpuIndex::Gpu0]:
    ...
```

---

## Implementation Notes

### Parser (Already Implemented)

Simple's parser already handles `[]` for generics:

```rust
// In src/parser/src/types_def/mod.rs
fn parse_generic_type() -> TypeAnnotation {
    let base = self.parse_identifier()?;

    if self.peek() == Token::LBracket {
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

**No changes needed!**

---

## Conclusion

**Recommendation**: **Continue using `[]` (square brackets)** for type parameters in Simple.

**Benefits**:
- ✅ Consistent with existing Simple syntax
- ✅ No breaking changes
- ✅ No parser modifications needed
- ✅ Avoids comparison operator ambiguity
- ✅ Distinctive language design

**Device type syntax**:
```simple
Gpu[DeviceInt, GpuIndex::Gpu0]
Host[DeviceInt]
Promise[Gpu[Tensor[Float], GpuIndex::Gpu1]]
```

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Recommendation**: Use `[]` (square brackets) for consistency
