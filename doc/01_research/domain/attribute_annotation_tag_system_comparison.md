# Attribute / Annotation / Tag System Comparison Across Languages

**Date:** 2026-03-29
**Purpose:** Research for designing Simple's tag system
**Scope:** 10 languages, syntax choices, compile-time vs runtime, pain points, evolution

---

## Table of Contents

1. [Rust](#1-rust)
2. [Java](#2-java)
3. [Python](#3-python)
4. [C#](#4-c-sharp)
5. [Kotlin](#5-kotlin)
6. [Swift](#6-swift)
7. [Zig](#7-zig)
8. [Go](#8-go)
9. [TypeScript](#9-typescript)
10. [C/C++](#10-cc)
11. [Comparative Analysis](#11-comparative-analysis)
12. [Design Recommendations for Simple](#12-design-recommendations-for-simple)

---

## 1. Rust

### Syntax

```rust
// Outer attribute (applies to the NEXT item)
#[derive(Debug, Clone)]
#[cfg(target_os = "linux")]
struct Point { x: f64, y: f64 }

// Inner attribute (applies to the ENCLOSING item)
#![allow(dead_code)]       // crate-level or module-level
#![feature(async_closure)]  // nightly feature gates

// Key built-in attributes
#[test]
#[inline(always)]
#[repr(C)]
#[must_use]
#[deprecated(since = "1.0", note = "use new_fn instead")]
#[allow(unused_variables)]
#[cfg(feature = "serde")]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
```

### Why This Syntax

- `#[...]` was chosen to be visually distinct from code, clearly "meta" information
- The `#` prefix echoes C preprocessor directives, signaling "this is not normal code"
- Inner `#![...]` vs outer `#[...]` distinction uses the `!` (bang) to mean "applies inward" -- consistent with Rust's general use of `!` for negation/inversion
- Square brackets `[]` contain attribute arguments, avoiding ambiguity with function calls `()` or generics `<>`

### Unified vs Multiple Systems

**ONE unified system** with multiple categories:
- **Built-in attributes**: `#[test]`, `#[cfg]`, `#[inline]`, `#[repr]` -- compiler-intrinsic
- **Derive macros**: `#[derive(Debug)]` -- code generation at compile time
- **Attribute macros**: `#[tokio::main]` -- arbitrary code transformation
- **Tool attributes**: `#[rustfmt::skip]`, `#[clippy::allow]` -- tool-specific

All share the same `#[...]` syntax, but they have very different semantics under the hood.

### Compile-Time vs Runtime

**Exclusively compile-time.** Attributes are processed during compilation and have zero runtime overhead. There is no reflection system to query attributes at runtime. This is a deliberate design choice favoring zero-cost abstractions.

- `#[cfg(...)]` performs conditional compilation (dead code is completely removed)
- `#[derive(...)]` generates code at compile time via proc macros
- `#[inline]` is a compiler hint
- `#[test]` marks functions for the test harness (conditional compilation)

### Common Pain Points

1. **Proc macro complexity**: Writing custom derive or attribute macros requires a separate crate, understanding `TokenStream`, and fighting the `syn`/`quote` ecosystem. The learning curve is steep.
2. **Error messages from macros**: When a derive macro fails, error messages can be cryptic, pointing to generated code the user never wrote.
3. **`cfg` can hide bugs**: Conditional compilation means code for other platforms may not even be type-checked. `cfg` errors are discovered only when building for that target.
4. **Inner attribute placement**: `#![...]` must appear at the very top of a file/module, which is a source of confusion for newcomers.
5. **No runtime reflection**: Sometimes you genuinely need runtime metadata (serialization format discovery, plugin systems). Rust forces you to use proc macros to generate the equivalent, adding complexity.
6. **Attribute ordering matters** for some proc macros but not others, which is confusing.

### Evolution

- **Pre-1.0**: Attributes existed from early Rust, inspired by C/C++ `__attribute__` but with cleaner syntax.
- **Rust 1.0 (2015)**: Stable attributes for `cfg`, `test`, `derive` (only built-in derives).
- **Rust 1.15 (2017)**: Custom derive macros stabilized (`#[derive(Serialize)]`). This was transformative.
- **Rust 1.30 (2018)**: Attribute procedural macros (`#[proc_macro_attribute]`) stabilized, enabling `#[tokio::main]`, `#[async_trait]`, etc.
- **Ongoing**: `#[diagnostic]` namespace for custom error messages. Discussion about attribute syntax for expressions (not just items).
- **Regret**: The distinction between `#[...]` and `#![...]` is a constant source of beginner confusion. Some have argued a single form with explicit target specification would be cleaner.

---

## 2. Java

### Syntax

```java
// Built-in annotations
@Override
public String toString() { ... }

@Deprecated(since = "9", forRemoval = true)
public void oldMethod() { ... }

@SuppressWarnings("unchecked")
List<String> list = (List<String>) raw;

// Custom annotation definition
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface MyAnnotation {
    String value() default "";
    int priority() default 0;
}

// Usage
@MyAnnotation(value = "hello", priority = 5)
public void myMethod() { ... }

// Repeating annotations (Java 8+)
@Schedule(dayOfMonth = "last")
@Schedule(dayOfWeek = "Fri", hour = "23")
public void doPeriodicCleanup() { ... }

// Type annotations (Java 8+)
@NonNull String name;
List<@NonNull String> names;
```

### Why This Syntax

- `@` prefix was chosen because it was unused in Java and visually distinctive
- `@interface` for definition reuses the `interface` keyword, emphasizing that annotations are a kind of type
- The syntax was designed to look like a modifier (like `public`, `static`) -- it attaches to declarations

### Unified vs Multiple Systems

**ONE unified system** but with distinct retention policies that create effective sub-systems:

- **`RetentionPolicy.SOURCE`**: Discarded by compiler after processing (like `@Override`, `@SuppressWarnings`). Only for compile-time checks.
- **`RetentionPolicy.CLASS`**: Written to `.class` file but not available via reflection at runtime. Default. Used by bytecode analysis tools.
- **`RetentionPolicy.RUNTIME`**: Available via reflection at runtime. Used by frameworks (Spring, JPA, JUnit).

### Compile-Time vs Runtime

Java explicitly distinguishes via `@Retention`:

| Retention | Available at compile time | In bytecode | Available at runtime |
|-----------|--------------------------|-------------|---------------------|
| SOURCE    | Yes                      | No          | No                  |
| CLASS     | Yes                      | Yes         | No                  |
| RUNTIME   | Yes                      | Yes         | Yes (reflection)    |

Runtime access via reflection:
```java
Method m = MyClass.class.getMethod("myMethod");
MyAnnotation ann = m.getAnnotation(MyAnnotation.class);
String val = ann.value(); // "hello"
```

### Target Element Types

```java
@Target({
    ElementType.TYPE,            // class, interface, enum
    ElementType.FIELD,           // field declaration
    ElementType.METHOD,          // method declaration
    ElementType.PARAMETER,       // formal parameter
    ElementType.CONSTRUCTOR,     // constructor
    ElementType.LOCAL_VARIABLE,  // local variable
    ElementType.ANNOTATION_TYPE, // annotation type itself
    ElementType.PACKAGE,         // package declaration
    ElementType.TYPE_PARAMETER,  // type parameter (Java 8)
    ElementType.TYPE_USE,        // any type use (Java 8)
    ElementType.MODULE,          // module declaration (Java 9)
    ElementType.RECORD_COMPONENT // record component (Java 16)
})
```

### Common Pain Points

1. **Annotation processing is complex**: Writing annotation processors requires understanding the `javax.annotation.processing` API, round-based processing, and generated source integration.
2. **No code generation in annotations themselves**: Annotations are purely declarative metadata. Any behavior requires a separate processor or runtime framework. This leads to "magic" frameworks (Spring, Hibernate) where annotations trigger complex runtime behavior that is hard to trace.
3. **Default retention is CLASS, not RUNTIME**: This trips up many developers who define custom annotations and wonder why reflection cannot find them. Most custom annotations should be RUNTIME.
4. **Annotation values are very restricted**: Only primitives, String, Class, enums, other annotations, and arrays thereof. No arbitrary objects, no lambdas, no complex expressions.
5. **Repeating annotations ceremony**: Before Java 8, you needed a container annotation. Java 8 added `@Repeatable` but still requires a container type definition.
6. **No inheritance of annotations**: By default, annotations on a superclass are not inherited by subclasses unless the annotation is marked `@Inherited`, and even then only for class-level annotations.

### Evolution

- **Java 5 (2004)**: Annotations introduced. Built-in: `@Override`, `@Deprecated`, `@SuppressWarnings`. Annotation processing API.
- **Java 6 (2006)**: Pluggable annotation processing (JSR 269) replaced `apt` tool. Better IDE integration.
- **Java 7 (2011)**: `@SafeVarargs` added.
- **Java 8 (2014)**: Major expansion -- `@Repeatable` annotations, type annotations (`ElementType.TYPE_USE`, `ElementType.TYPE_PARAMETER`). This was a big redesign driven by checker frameworks like Checker Framework wanting to annotate types in `List<@NonNull String>`.
- **Java 9+ (2017+)**: `@Deprecated(forRemoval=true)`, module annotations.
- **Regret**: The `@interface` syntax for defining annotations is widely considered confusing -- it looks like defining an interface but has completely different semantics. The restriction on annotation values (no arbitrary types) is limiting. The three retention levels create confusion about which to use.

---

## 3. Python

### Syntax

```python
# Basic decorator
@log_calls
def my_function():
    pass

# Decorator with arguments
@retry(max_attempts=3, delay=1.0)
def fetch_data():
    pass

# Stacked decorators (applied bottom-up)
@app.route("/api/users")
@require_auth
@validate_json
def get_users():
    pass

# Class decorators
@dataclass
@total_ordering
class Point:
    x: float
    y: float

# Decorators are just functions
def log_calls(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        print(f"Calling {func.__name__}")
        return func(*args, **kwargs)
    return wrapper

# Decorator with arguments is a decorator factory
def retry(max_attempts=3, delay=1.0):
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            for attempt in range(max_attempts):
                try:
                    return func(*args, **kwargs)
                except Exception:
                    if attempt == max_attempts - 1:
                        raise
                    time.sleep(delay)
        return wrapper
    return decorator
```

### Why This Syntax

- `@` was chosen as a concise prefix that is visually distinctive
- The PEP 318 discussion (2003-2004) considered many alternatives:
  - `def foo() [decorator]:` -- after the function header
  - `decorate(decorator) def foo():` -- keyword-based
  - `|decorator| def foo():` -- pipe-delimited
- `@decorator` before the `def` won because it is easy to read, clearly precedes the decorated entity, and does not require modifying the function signature syntax
- Stacking with multiple `@` lines was a natural extension

### Unified vs Multiple Systems

**Effectively TWO systems that serve different purposes:**

1. **Decorators (`@`)**: Code transformation at definition time. Can wrap, replace, or modify callables and classes.
2. **Type hints / annotations**: `def foo(x: int) -> str:` -- These are stored in `__annotations__` dict but have NO runtime effect by default. Tools like mypy, Pydantic, and FastAPI read them.

These are separate systems by design. Decorators are executable code; type hints are passive metadata.

Additionally, Python has **no compile-time annotation system** since it is interpreted. All decorators execute at import/definition time (which is runtime).

### Compile-Time vs Runtime

**Everything is runtime.** Python has no compilation phase in the traditional sense. Decorators execute when the module is imported, which is "definition time" but still runtime. There is no mechanism for compile-time-only metadata that gets stripped.

Type hints are available at runtime via `__annotations__` but by convention are not used for runtime logic (though Pydantic and FastAPI violate this convention deliberately).

### Common Pain Points

1. **Decorator stacking order is confusing**: `@A @B @C def f()` means `A(B(C(f)))`. The bottom decorator is applied first. This is counterintuitive to many.
2. **Decorator factories are verbose**: A decorator that takes arguments requires three levels of nesting (factory -> decorator -> wrapper). This is the most common source of decorator bugs.
3. **`functools.wraps` is easy to forget**: Without it, the decorated function loses its name, docstring, and signature. This is a footgun.
4. **Debugging decorated functions**: Stack traces show the wrapper, not the original function. Breakpoints can be confusing.
5. **No standard way to introspect decorators**: Given a decorated function, there is no built-in way to discover which decorators were applied or in what order.
6. **Performance overhead**: Every decorator adds a function call layer. Stacking many decorators on hot paths can measurably slow code.
7. **Decorators can do anything**: Since they are just functions, a decorator can completely replace the decorated function with something unrelated. This flexibility is both a strength and a source of confusion.

### Evolution

- **Python 2.4 (2004)**: Function decorators introduced (PEP 318).
- **Python 3.0 (2008)**: Function annotations introduced (PEP 3107) -- `def foo(x: expr) -> expr:`. Initially no defined semantics.
- **Python 3.5 (2015)**: Type hints formalized (PEP 484). `typing` module added.
- **Python 3.6 (2016)**: Variable annotations `x: int = 5` (PEP 526).
- **Python 3.7 (2018)**: `dataclasses` -- the `@dataclass` decorator became the poster child for decorator power. `from __future__ import annotations` for lazy evaluation.
- **Python 3.9 (2020)**: Relaxed decorator syntax (PEP 614) -- any expression, not just dotted names, can follow `@`.
- **Python 3.10+ (2021+)**: `ParamSpec` and `Concatenate` for better decorator typing. PEP 649 (deferred evaluation of annotations) ongoing.
- **Regret/tension**: The dual system of decorators (code) + annotations (metadata) is a source of confusion. PEP 649 attempts to resolve the performance issue of evaluating annotation expressions eagerly. The `@dataclass` pattern has led to more and more "magic" decorators that heavily transform classes, which some consider un-Pythonic.

---

## 4. C# (C Sharp)

### Syntax

```csharp
// Built-in attributes
[Obsolete("Use NewMethod instead", error: true)]
public void OldMethod() { }

[Serializable]
public class MyData { }

// Multiple attributes in one bracket
[Serializable, JsonProperty("name")]
public string Name { get; set; }

// Attribute with named parameters
[DllImport("user32.dll", SetLastError = true, CharSet = CharSet.Auto)]
static extern int MessageBox(IntPtr hWnd, String text, String caption, uint type);

// Attribute targets (explicit)
[assembly: AssemblyVersion("1.0.0.0")]   // assembly-level
[module: SuppressMessage("Style", "IDE0003")]
[return: MarshalAs(UnmanagedType.Bool)]   // return value
[method: SecurityCritical]                // method
[field: NonSerialized]                    // backing field of auto-property
[property: JsonRequired]                  // property
[param: CallerMemberName]                // parameter

// Custom attribute definition
[AttributeUsage(AttributeTargets.Class | AttributeTargets.Method,
    AllowMultiple = true, Inherited = false)]
public class CacheAttribute : Attribute
{
    public int Duration { get; set; }
    public string VaryByParam { get; set; }

    public CacheAttribute(int duration)
    {
        Duration = duration;
    }
}

// Usage
[Cache(300, VaryByParam = "id")]
public ActionResult GetUser(int id) { }

// Conditional compilation (separate from attributes)
#if DEBUG
    Console.WriteLine("Debug mode");
#endif

// Caller info attributes (compile-time metadata injection)
void Log(string msg,
    [CallerMemberName] string member = "",
    [CallerFilePath] string file = "",
    [CallerLineNumber] int line = 0)
{
    Console.WriteLine($"{file}:{line} [{member}] {msg}");
}
```

### Why This Syntax

- `[...]` was chosen as clean and distinctive. The square brackets were not used for indexing in the declaration context, avoiding ambiguity.
- The `[target: ...]` prefix syntax for explicit targets was added to disambiguate when an attribute could apply to multiple things (e.g., a property vs its backing field).
- C# attributes are full classes inheriting from `System.Attribute`, making them part of the type system rather than a separate metadata language.

### Unified vs Multiple Systems

**TWO distinct systems:**

1. **Attributes `[...]`**: Metadata attached to declarations. Full runtime reflection support. These are classes.
2. **Preprocessor directives `#if/#endif`**: Compile-time conditional compilation. Text-based, not part of the type system. Inherited from C/C++.

The attribute system is unified and consistent. The preprocessor is a legacy parallel system.

Additionally, C# has **XML documentation comments** (`///`) which are yet another metadata system processed by tooling.

### Compile-Time vs Runtime

C# attributes are primarily **runtime** metadata, accessible via reflection:

```csharp
var attrs = typeof(MyClass).GetCustomAttributes(typeof(CacheAttribute), true);
```

However, some attributes are also processed at **compile time**:
- `[Obsolete]` generates compiler warnings/errors
- `[Conditional("DEBUG")]` removes method calls at compile time
- `[CallerMemberName]` injects caller info at compile time
- `[Flags]` affects how enums are displayed

Source generators (C# 9+) can also read attributes at compile time to generate code, similar to Rust proc macros.

### Common Pain Points

1. **Reflection performance**: Runtime attribute lookup via reflection is slow. Caching is needed for hot paths.
2. **Stringly-typed configuration**: Many attributes use string parameters (`[Route("api/users")]`) which are not checked at compile time.
3. **Limited compile-time code generation**: Before source generators (2020), attributes were purely declarative. You needed PostSharp or Fody for AOP-style code weaving.
4. **Attribute constructor limitations**: Like Java, attribute parameters are restricted to constants, typeof, enum values, and arrays thereof.
5. **Target ambiguity**: For auto-properties, attributes can apply to the property, backing field, getter, or setter. The `[field:]` target prefix was added to resolve this but is easy to forget.
6. **No attribute composition**: You cannot define an attribute that "includes" another attribute. Each must be listed separately.

### Evolution

- **C# 1.0 (2002)**: Attributes introduced. Reflection-based. `[Serializable]`, `[DllImport]`, `[Obsolete]`.
- **C# 2.0 (2005)**: `[Conditional]` attribute for conditional method compilation.
- **C# 3.0 (2007)**: LINQ attributes, expression trees.
- **C# 5.0 (2012)**: `[CallerMemberName]`, `[CallerFilePath]`, `[CallerLineNumber]` -- compile-time caller info injection.
- **C# 7.3 (2018)**: Attribute targets for backing fields of auto-properties.
- **C# 8.0 (2019)**: Nullable reference type annotations (separate system from attributes, but related).
- **C# 9.0 (2020)**: **Source generators** -- game changer. Compile-time code generation driven by attributes, similar to Rust proc macros.
- **C# 10+ (2021+)**: Generic attributes, `[CallerArgumentExpression]`.
- **Regret**: The preprocessor (`#if`) being separate from attributes is messy. Many wish conditional compilation were integrated into the attribute system (as Rust does with `#[cfg]`).

---

## 5. Kotlin

### Syntax

```kotlin
// Basic annotations
@Deprecated("Use newMethod", ReplaceWith("newMethod()"))
fun oldMethod() { }

@JvmStatic
@JvmOverloads
fun process(name: String, count: Int = 1) { }

// Annotation targets (use-site targets)
class MyClass(
    @field:JsonProperty("user_name")    // applies to backing field
    @get:JsonProperty("user_name")      // applies to getter
    @set:JsonProperty("user_name")      // applies to setter
    @param:JsonProperty("user_name")    // applies to constructor param
    val userName: String
)

// All annotation targets
@file:JvmName("Utils")                   // file-level (must be first)
@property:Deprecated("old")              // Kotlin property
@field:Transient                         // JVM field
@get:JvmName("getUserName")            // getter
@set:JvmName("setUserName")            // setter
@setparam:NotNull                        // setter parameter
@delegate:Transient                      // delegate field
@receiver:NotNull                        // extension receiver

// Custom annotation
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION)
@Retention(AnnotationRetention.RUNTIME)
@Repeatable
@MustBeDocumented
annotation class Fancy(val name: String, val priority: Int = 0)

// Annotation on expressions (Kotlin-specific)
val list = @Suppress("UNCHECKED_CAST") (raw as List<String>)

// Annotation on lambdas
val f = @MyAnnotation { x: Int -> x * 2 }
```

### Why This Syntax

- `@Annotation` was adopted from Java for familiarity, since Kotlin targets the JVM and needs annotation interop
- Use-site targets (`@field:`, `@get:`) were added because Kotlin's concise property syntax maps to multiple JVM constructs (field + getter + setter + parameter). Without targets, it is ambiguous where the annotation goes
- `annotation class` instead of Java's `@interface` -- clearer that annotations are class types

### Unified vs Multiple Systems

**ONE primary system** (annotations) with strong JVM interop considerations:

- Kotlin annotations map directly to Java annotations on the JVM
- Use-site targets are a Kotlin-specific extension to handle the impedance mismatch between Kotlin properties and Java fields/getters/setters
- The `@file:` target is unique to Kotlin (no Java equivalent)

Kotlin does NOT have a separate preprocessor or conditional compilation system. There are compiler plugins (like `kotlinx.serialization`, `compose`) that act on annotations but are integrated into the compiler pipeline.

### Compile-Time vs Runtime

Same three-level retention as Java:
- `AnnotationRetention.SOURCE` -- compile-time only
- `AnnotationRetention.BINARY` -- in bytecode, no reflection (Java's CLASS)
- `AnnotationRetention.RUNTIME` -- full reflection access

**Default is RUNTIME** (unlike Java's CLASS default). This was a deliberate improvement.

Kotlin compiler plugins (like `@Serializable`) process annotations at compile time to generate code, similar to Java annotation processors but more tightly integrated.

### Common Pain Points

1. **Use-site target verbosity**: `@field:JsonProperty("x") @get:JsonProperty("x")` -- sometimes you need the same annotation on multiple targets, leading to repetition.
2. **Default target confusion**: Without an explicit use-site target, the annotation goes to the "first applicable" target in a priority order (param > property > field). This ordering is documented but frequently forgotten.
3. **Java interop friction**: Some Java annotations do not map cleanly to Kotlin constructs. `@JvmField`, `@JvmStatic`, `@JvmOverloads` are "escape hatches" needed because Kotlin and Java semantics differ.
4. **Compiler plugins are opaque**: `@Serializable`, `@Composable` etc. trigger significant compiler transformations, but this is invisible and hard to debug.

### Evolution

- **Kotlin 1.0 (2016)**: Annotation system launched, closely mirroring Java but with use-site targets and `annotation class` syntax.
- **Kotlin 1.1 (2017)**: `@Repeatable` support.
- **Kotlin 1.3 (2018)**: Better annotation processing (KAPT improvements).
- **Kotlin 1.5+ (2021+)**: KSP (Kotlin Symbol Processing) as a replacement for KAPT -- faster, Kotlin-native annotation processing.
- **Kotlin 2.0 (2024)**: K2 compiler with better plugin architecture.
- **Regret**: The KAPT (Kotlin Annotation Processing Tool) approach of generating Java stubs for annotation processing was slow and hacky. KSP was created to fix this. The use-site target system, while necessary for JVM mapping, adds cognitive overhead.

---

## 6. Swift

### Syntax

```swift
// Built-in attributes
@available(iOS 15, macOS 12, *)
func newFeature() { }

@available(*, deprecated, renamed: "newName")
func oldName() { }

@discardableResult
func process() -> Bool { }

@objc(MySwiftClass)
class MyClass: NSObject { }

@frozen
enum Direction { case north, south, east, west }

@inlinable
public func square(_ x: Int) -> Int { x * x }

@MainActor
class ViewModel: ObservableObject { }

@propertyWrapper
struct Clamped<Value: Comparable> {
    var wrappedValue: Value
    let range: ClosedRange<Value>

    init(wrappedValue: Value, _ range: ClosedRange<Value>) {
        self.wrappedValue = min(max(wrappedValue, range.lowerBound), range.upperBound)
        self.range = range
    }
}

// Usage of property wrapper
struct Settings {
    @Clamped(0...100) var volume: Int = 50
    @Clamped(0.0...1.0) var brightness: Double = 0.8
}

// Result builders (formerly function builders)
@resultBuilder
struct HTMLBuilder { ... }

@HTMLBuilder
func makeBody() -> HTML { ... }

// Attached macros (Swift 5.9+)
@Observable
class Model { var count = 0 }

@Model
struct User { var name: String }

// Freestanding macros
let value = #stringify(1 + 2)  // freestanding with #
```

### Why This Syntax

- `@attribute` was chosen for visual clarity and to be consistent with Objective-C's `@` usage (`@interface`, `@property`, `@selector`)
- Attributes precede the declaration they modify, similar to access modifiers
- No `#[]` or `[]` style -- Swift wanted to distinguish from array literals and ObjC's method call syntax
- The `#` prefix for freestanding macros (Swift 5.9) distinguishes them from attached `@` macros

### Unified vs Multiple Systems

**ONE primary system** (`@attribute`) but with distinct categories that have evolved significantly:

1. **Built-in attributes**: `@available`, `@discardableResult`, `@frozen`, `@inlinable` -- compiler-understood, fixed set
2. **Property wrappers** (`@propertyWrapper`): User-definable, transform property access
3. **Result builders** (`@resultBuilder`): User-definable, transform blocks of code (SwiftUI's foundation)
4. **Macros** (Swift 5.9+): `@Observable`, `#stringify` -- full code generation

All use `@` syntax (except freestanding macros using `#`), creating a unified appearance. But the underlying mechanisms are very different.

Swift also has `#if` for conditional compilation, which is a **separate preprocessor-like system**:
```swift
#if DEBUG
print("debug")
#endif
```

### Compile-Time vs Runtime

**Primarily compile-time.** Swift has limited runtime reflection (Mirror type), and attributes are generally not queryable at runtime.

- `@available` triggers compile-time availability checking
- `@frozen` affects ABI decisions at compile time
- `@propertyWrapper` generates code at compile time
- `@objc` generates Objective-C runtime metadata (an exception -- this IS runtime-visible)
- Macros expand at compile time

### Common Pain Points

1. **`@available` syntax is verbose**: Platform availability checks require listing each platform. `@available(iOS 15, macOS 12, tvOS 15, watchOS 8, *)` for every function is noisy.
2. **Property wrappers have limitations**: Cannot compose multiple property wrappers easily. The `wrappedValue`/`projectedValue` protocol is implicit (no formal protocol).
3. **ABI attributes are confusing**: `@frozen`, `@inlinable`, `@usableFromInline` -- these are library evolution attributes that most developers should not need but must understand for public frameworks.
4. **Macro system complexity**: Swift 5.9 macros require a separate Swift package for macro implementation, similar to Rust proc macros requiring a separate crate.
5. **`#if` is not integrated with attributes**: Conditional compilation uses a separate `#if` preprocessor, not the `@` attribute system. You cannot write `@cfg(DEBUG)` like Rust.

### Evolution

- **Swift 1.0 (2014)**: Basic attributes: `@objc`, `@IBOutlet`, `@IBAction`, `@lazy` (later became keyword).
- **Swift 2.0 (2015)**: `@available` for platform availability checking. `@testable` for test imports.
- **Swift 3.0 (2016)**: `@discardableResult`, `@escaping`. Several attributes became keywords instead (`lazy`, `optional`).
- **Swift 4.0-4.2 (2017-2018)**: `@dynamicMemberLookup`, `@dynamicCallable`. `#if canImport()`.
- **Swift 5.0 (2019)**: ABI stability attributes: `@frozen`, `@inlinable`, `@usableFromInline`.
- **Swift 5.1 (2019)**: `@propertyWrapper` (previously `@_propertyDelegate`). `@resultBuilder` (previously `@_functionBuilder`).
- **Swift 5.4 (2021)**: `@resultBuilder` officially stabilized.
- **Swift 5.9 (2023)**: **Macros** -- `@attached` macros and `#freestanding` macros. Major new capability.
- **Regret**: Several things that started as attributes (`lazy`, `optional`, `mutating`) were later converted to keywords, suggesting the attribute system was initially overloaded. The `@_` prefix convention for unstable attributes is ugly and there is no clear path to stability for many of them.

---

## 7. Zig

### Syntax

```zig
// Built-in functions (prefixed with @)
const result = @intCast(u32, value);
const aligned = @alignOf(MyStruct);
const info = @typeInfo(MyStruct);
const name = @typeName(MyStruct);
const ptr = @ptrCast(*u8, raw_ptr);

// Comptime -- the annotation system IS the language
fn Vector(comptime T: type, comptime len: usize) type {
    return struct {
        data: [len]T,

        const Self = @This();

        pub fn dot(self: Self, other: Self) T {
            var sum: T = 0;
            comptime var i: usize = 0;
            inline while (i < len) : (i += 1) {
                sum += self.data[i] * other.data[i];
            }
            return sum;
        }
    };
}

// "Annotations" via comptime and conventions
pub fn export_symbol(comptime name: []const u8) void {
    // compile-time string manipulation
}

// Test attribute (built-in)
test "my test" {
    try expect(add(2, 3) == 5);
}

// Extern/calling conventions
extern "c" fn my_c_func(x: c_int) c_int { ... }

// Packed struct (alignment annotation)
const Flags = packed struct {
    flag_a: bool,
    flag_b: bool,
    padding: u6,
};

// Export control
export fn visible_to_c() void { ... }

// Inline annotation
inline fn always_inline() void { ... }
noinline fn never_inline() void { ... }
```

### Why This Syntax

- Zig's philosophy: **"no hidden control flow, no hidden allocations"**
- Instead of a separate annotation/attribute system, Zig uses `comptime` -- compile-time execution of regular Zig code
- `@builtins` are prefixed with `@` to clearly distinguish them from user code. They are compiler intrinsics, not a general annotation mechanism
- Keywords like `inline`, `noinline`, `export`, `extern` are used directly rather than through an attribute system

### Unified vs Multiple Systems

**Deliberately NO separate annotation system.** Zig's approach:

1. **`@builtins`**: Compiler intrinsics (`@intCast`, `@typeInfo`, `@compileLog`). Fixed set, not extensible by users.
2. **`comptime`**: Compile-time code execution replaces what other languages do with attributes/macros. Instead of `#[derive(Debug)]`, you write comptime code that generates the implementation.
3. **Keywords**: `inline`, `noinline`, `export`, `extern`, `packed`, `align(N)` are language keywords, not attributes.
4. **`test` blocks**: Built-in syntax, not an annotation on a function.

This is a fundamentally different philosophy: metadata is expressed through the language itself, not through a separate meta-language.

### Compile-Time vs Runtime

**`comptime` is THE compile-time system.** There is no runtime reflection or metadata. Everything is resolved at compile time:

- `comptime` blocks execute at compile time
- `@typeInfo` returns type metadata at compile time (no runtime cost)
- Generic types are monomorphized via comptime parameters
- There is NO way to query metadata at runtime (by design)

### Common Pain Points

1. **No user-defined attribute syntax**: You cannot write `@[my_custom_attribute]` on a declaration. If you want metadata, you must encode it in the type system or use conventions.
2. **Comptime code is powerful but complex**: Writing a "derive Debug" equivalent requires understanding Zig's comptime deeply. The code is more explicit but significantly more verbose.
3. **No ecosystem-standard decoration pattern**: Without attributes, libraries cannot standardize on annotation-driven patterns (like Spring's `@Autowired` or Rust's `#[serde(rename)]`).
4. **Limited tooling metadata**: IDE tools, documentation generators, and linters cannot easily discover semantic metadata about declarations.
5. **`@builtins` namespace is flat**: All built-in functions share the `@` prefix with no namespacing.

### Evolution

- Zig has been remarkably consistent in this regard. From early versions, the philosophy was "no hidden magic" and comptime was the answer to what other languages use attributes for.
- The `@` builtin set has grown over time but the fundamental design has not changed.
- **No regrets expressed**: The Zig team considers the lack of an attribute system a feature, not a limitation. The comptime approach is intentional.

---

## 8. Go

### Syntax

```go
// Struct tags (backtick-delimited key:"value" pairs)
type User struct {
    Name     string `json:"name" xml:"user_name" validate:"required"`
    Email    string `json:"email" validate:"required,email"`
    Age      int    `json:"age,omitempty" validate:"gte=0,lte=130"`
    Password string `json:"-"` // excluded from JSON
    internal string // unexported, no tag
}

// Accessing tags at runtime via reflection
field, _ := reflect.TypeOf(User{}).FieldByName("Name")
jsonTag := field.Tag.Get("json")    // "name"
xmlTag := field.Tag.Get("xml")      // "user_name"
rawTag := field.Tag                  // `json:"name" xml:"user_name" validate:"required"`

// Build tags / build constraints
//go:build linux && amd64
// +build linux,amd64  (old syntax, still supported)

// Compiler directives (comments with special prefixes)
//go:generate stringer -type=Color
//go:noinline
//go:nosplit
//go:linkname localName importpath.remoteName
//go:embed static/*
//go:noescape

// Embed directive (Go 1.16+)
import _ "embed"

//go:embed hello.txt
var greeting string

//go:embed static/*
var staticFiles embed.FS

// Cgo annotations
/*
#cgo LDFLAGS: -lm
#include <math.h>
*/
import "C"

// Deprecated marker (in doc comment)
// Deprecated: Use NewFunction instead.
func OldFunction() {}
```

### Why This Syntax

- **Struct tags**: Go chose backtick raw strings because they were already part of the language and could contain arbitrary key-value metadata. The `key:"value"` convention (not enforced by the language) emerged as a community standard.
- **`//go:` directives**: Using comments was deliberately chosen so they would NOT be part of the language grammar. This keeps the language spec simple and makes directives a "compiler implementation detail."
- Go's philosophy is extreme simplicity. Adding an attribute syntax to the grammar was rejected in favor of convention-based metadata.

### Unified vs Multiple Systems

**MULTIPLE separate, disconnected systems:**

1. **Struct tags** (backtick strings): Field-level metadata on struct fields only. Runtime-accessible via reflection. No compile-time processing. Convention-based parsing.
2. **`//go:` compiler directives** (magic comments): Compiler-processed pragmas. NOT accessible at runtime. NOT part of the language grammar.
3. **`//go:generate` directives**: Triggers external code generation tools. Run by `go generate` command, not by the compiler.
4. **`//go:embed` directives**: File embedding, processed by compiler.
5. **`//go:build` constraints**: Conditional compilation, processed by the build system.
6. **Doc comments** (`// Deprecated:`): Tooling conventions recognized by `go vet`, `gopls`, `godoc`.

These are explicitly NOT unified. Each has its own parsing rules and processing pipeline.

### Compile-Time vs Runtime

| System | Compile-time | Runtime |
|--------|-------------|---------|
| Struct tags | No (opaque strings) | Yes (reflection) |
| `//go:noinline` | Yes | No |
| `//go:embed` | Yes | The embedded data is available |
| `//go:build` | Yes (file selection) | No |
| `//go:generate` | Pre-compilation | No |

Struct tags are the only runtime-accessible metadata, and only via reflection which is slow and discouraged in hot paths.

### Common Pain Points

1. **Struct tags are stringly-typed**: `json:"name,omitempty"` is just a string. Typos are not caught at compile time. `json:"name,omtimepy"` silently does nothing.
2. **No validation of struct tags**: The compiler does not validate tag syntax. `go vet` catches some issues but not all.
3. **Tags only on struct fields**: You cannot put tags on functions, types, methods, or packages. If you need metadata on a function, there is no standard way.
4. **`//go:` directives are invisible to the language**: Tools cannot reliably parse them because they are comments. Different tools have different comment-directive syntaxes.
5. **No user-defined directives**: You cannot create `//mylib:validate` directives that the compiler processes. Only `//go:generate` lets you run arbitrary tools.
6. **Multiple incompatible systems**: Struct tags, compiler directives, build constraints, and go:generate all work differently. There is no unified metadata model.
7. **Reflection is slow**: Runtime access to struct tags requires reflection, which is orders of magnitude slower than direct field access. This limits the usefulness of runtime metadata.

### Evolution

- **Go 1.0 (2012)**: Struct tags existed from day one. `//go:` directives for `noinline`, `nosplit` etc.
- **Go 1.4 (2014)**: `//go:generate` introduced for code generation.
- **Go 1.16 (2021)**: `//go:embed` for file embedding. This was a significant new directive.
- **Go 1.17 (2021)**: New `//go:build` syntax for build constraints, replacing the confusing `// +build` syntax.
- **Ongoing**: Proposals for generalized annotations have been repeatedly rejected. The Go team is philosophically opposed to a general attribute system, preferring explicit code over metadata.
- **Regret/criticism**: The struct tag system is widely regarded as Go's weakest metadata mechanism. The stringly-typed nature causes bugs. The inability to annotate anything other than struct fields is limiting. But the Go team has not shown interest in changing this.

---

## 9. TypeScript

### Syntax

```typescript
// Stage 3 Decorators (TC39 proposal, supported in TS 5.0+)
@logged
class MyClass {
    @validate
    accessor name: string = "";

    @bound
    greet() { return `Hello, ${this.name}`; }
}

// Decorator implementation
function logged(target: typeof MyClass, context: ClassDecoratorContext) {
    console.log(`Class ${context.name} defined`);
    return target;  // can return replacement
}

function validate<T>(
    target: ClassAccessorDecoratorTarget<MyClass, T>,
    context: ClassAccessorDecoratorContext<MyClass, T>
) {
    return {
        set(value: T) { /* validation logic */ target.set.call(this, value); },
        get() { return target.get.call(this); }
    };
}

// Legacy/experimental decorators (TS pre-5.0, different API)
// Required: "experimentalDecorators": true in tsconfig
function legacyDecorator(target: any, propertyKey: string, descriptor: PropertyDescriptor) {
    // different signature than stage 3
}

// JSDoc annotations (compile-time, for type checking)
/** @deprecated Use newFunction instead */
function oldFunction() {}

/** @readonly */
/** @type {string} */
let name;

/** @template T */
/** @param {T} value */
/** @returns {T[]} */
function wrap(value) { return [value]; }

/** @satisfies {Record<string, number>} */
const sizes = { small: 1, medium: 2, large: 3 };

// Triple-slash directives
/// <reference path="types.d.ts" />
/// <reference types="node" />
/// <reference lib="dom" />

// TypeScript-specific modifiers (keyword-based, not decorators)
abstract class Base { }
readonly name: string;
override toString() { }
```

### Why This Syntax

- `@decorator` was adopted from the TC39 decorator proposal for JavaScript. TypeScript wanted to align with the JS standard.
- JSDoc `/** @tag */` was adopted because it already existed in the JavaScript ecosystem (JSDoc has been around since 1999).
- Triple-slash directives `///` were a TypeScript-specific invention for module resolution, predating ES modules.

### Unified vs Multiple Systems

**MULTIPLE overlapping systems:**

1. **Decorators (`@`)**: Stage 3 TC39 proposal. Apply to classes, methods, fields, accessors. Runtime code transformation.
2. **JSDoc annotations (`/** @tag */`)**: In comments. Compile-time type information. No runtime effect.
3. **Triple-slash directives (`///`)**: Module resolution hints. Compile-time only. Being deprecated in favor of `import`.
4. **TypeScript modifiers**: `abstract`, `readonly`, `override`, `declare` -- keywords, not decorators.
5. **`as const`, `satisfies`**: Type assertion keywords that act as annotations.

These systems are NOT unified. Decorators are runtime; JSDoc is compile-time; modifiers are keywords.

### Compile-Time vs Runtime

| System | Compile-time | Runtime |
|--------|-------------|---------|
| Decorators | No (TS just emits them) | Yes (execute at class definition) |
| JSDoc | Yes (type checking) | No (comments, stripped) |
| `///` directives | Yes (module resolution) | No (stripped) |
| `reflect-metadata` | Emit-time | Yes (via Reflect API) |
| TS modifiers | Yes (type checking) | No (erased) |

The `reflect-metadata` polyfill (used by Angular, NestJS) enables runtime reflection of type information, but it is not part of the language standard.

### Common Pain Points

1. **Two incompatible decorator versions**: Legacy experimental decorators (TS <5.0) and Stage 3 decorators (TS 5.0+) have different APIs, different behavior, and are not compatible. Migrating is painful.
2. **Decorator metadata is lost at runtime**: TypeScript types are erased at runtime. Decorators can see classes/methods but not their types without `reflect-metadata`.
3. **JSDoc and TypeScript types overlap**: You can annotate types in JSDoc or in TS syntax. Having two ways to do the same thing is confusing.
4. **No standard attribute system**: Unlike Rust or C#, there is no built-in way to attach arbitrary metadata to declarations that the compiler understands.
5. **Decorator proposal instability**: The TC39 decorator proposal went through multiple incompatible revisions (stage 1 in 2014, stage 2 in 2018, stage 3 in 2022). This caused ecosystem fragmentation.

### Evolution

- **TypeScript 1.5 (2015)**: Experimental decorators (`experimentalDecorators` flag), based on early TC39 proposal.
- **2015-2022**: Angular, NestJS, MobX, TypeORM all built on experimental decorators. Massive ecosystem dependency.
- **TypeScript 4.x**: JSDoc type annotations expanded (`@satisfies`, `@overload`).
- **TypeScript 5.0 (2023)**: Stage 3 decorators (TC39 proposal). Different API from experimental decorators. Both supported simultaneously via tsconfig flag.
- **TypeScript 5.2+ (2023+)**: Decorator metadata proposal support.
- **Regret**: Shipping experimental decorators before the TC39 proposal stabilized created a massive compatibility problem. The Angular team had to maintain compatibility with both versions. This is widely considered one of TypeScript's biggest design mistakes.

---

## 10. C/C++

### Syntax

```c
// GCC __attribute__ (C and C++)
__attribute__((unused))
static void helper_fn(void) { }

__attribute__((deprecated("use new_fn")))
void old_fn(void);

__attribute__((aligned(16)))
struct Vector4 { float x, y, z, w; };

__attribute__((packed))
struct Header { uint8_t type; uint32_t length; };

__attribute__((visibility("default")))
void public_api(void);

__attribute__((format(printf, 1, 2)))
void my_printf(const char *fmt, ...);

__attribute__((warn_unused_result))
int important_fn(void);

// Multiple attributes
__attribute__((noinline, cold))
void error_handler(void);

// C++11 standard attributes [[...]]
[[nodiscard]] int compute();
[[deprecated("use v2")]] void old_api();
[[maybe_unused]] static void helper();
[[noreturn]] void abort_program();
[[fallthrough]];  // in switch cases
[[likely]] if (condition) { }    // C++20
[[unlikely]] if (error) { }     // C++20
[[no_unique_address]] Empty e;  // C++20
[[assume(x > 0)]];             // C++23

// Vendor extensions in [[...]] syntax
[[gnu::always_inline]]
[[clang::optnone]]
[[msvc::no_unique_address]]

// MSVC __declspec
__declspec(dllexport) void api_fn(void);
__declspec(dllimport) void external_fn(void);
__declspec(deprecated("old")) void legacy(void);
__declspec(align(16)) struct AlignedData { };
__declspec(novtable) class Interface { };

// Pragmas
#pragma once
#pragma pack(push, 1)
struct PackedData { /* ... */ };
#pragma pack(pop)

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
// code with intentionally unused vars
#pragma GCC diagnostic pop

#pragma omp parallel for
for (int i = 0; i < n; i++) { }

// C11 _Alignas (keyword-based)
_Alignas(16) float data[4];

// C23 standard attributes (same as C++11)
[[nodiscard]] int must_check(void);
```

### Why This Syntax

- **`__attribute__(())`**: GCC introduced this in the 1990s. Double parentheses allow macro expansion of attribute lists. The `__` prefix marks it as an extension. It is verbose by design to discourage overuse and make extensions visually distinct from standard code.
- **`[[...]]`**: C++11 standardized this to replace vendor-specific `__attribute__`. Double brackets were chosen to avoid conflicts with existing syntax. They are clean and unambiguous.
- **`#pragma`**: Inherited from early C. Originally meant "implementation-defined behavior." Each compiler defines its own pragmas.
- **`__declspec`**: Microsoft's alternative to GCC's `__attribute__`. Similar purpose, different syntax.

### Unified vs Multiple Systems

**FOUR+ competing systems (the most fragmented of any language):**

1. **`__attribute__(())`**: GCC/Clang extension. Function, variable, type attributes. Not standardized.
2. **`[[...]]`**: C++11/C23 standard. Subset of what `__attribute__` can do. Standardized and portable.
3. **`__declspec()`**: MSVC extension. Windows-specific (dllexport/dllimport, alignment).
4. **`#pragma`**: Compiler directives. Each compiler has different pragma sets. Some are standardized (`#pragma once` is de facto).
5. **Keywords**: `_Alignas`, `_Noreturn`, `inline`, `register`, `volatile` -- some metadata is baked into the language as keywords.
6. **`_Pragma()`**: C99 operator form of `#pragma`, usable inside macros.

The C++ committee has been slowly migrating `__attribute__` functionality into `[[...]]` syntax, but the process is incomplete and vendor extensions remain necessary for many use cases.

### Compile-Time vs Runtime

**Everything is compile-time.** C and C++ have no runtime reflection (except RTTI for `dynamic_cast`, which is limited).

- All attributes/pragmas are processed by the compiler and have no runtime representation
- There is no way to query "what attributes does this function have?" at runtime
- RTTI (`typeid`) provides only type names and hierarchy, not attribute metadata

### Common Pain Points

1. **Four incompatible syntaxes**: Portable code must handle GCC, Clang, MSVC, and standard attributes differently, typically with preprocessor macros.
2. **`__attribute__` is verbose and ugly**: The double-parentheses syntax is widely disliked.
3. **`[[...]]` is limited**: Many useful attributes (like `visibility`, `format`, `cleanup`) have no `[[...]]` equivalent yet. You still need `__attribute__` or `__declspec`.
4. **Pragma fragmentation**: `#pragma omp`, `#pragma acc`, `#pragma GCC`, `#pragma clang`, `#pragma STDC` -- completely different namespaces and semantics.
5. **Attribute ignorability**: The C++ standard says `[[...]]` attributes can be ignored by compilers. This means `[[nodiscard]]` is technically optional, leading to portability concerns.
6. **No user-defined attributes**: You cannot create custom `[[my_attr]]` in standard C++. Only the compiler and standard define attributes.
7. **Macro hell**: To write portable attribute code, you end up with:
   ```c
   #if defined(__GNUC__)
   #define UNUSED __attribute__((unused))
   #elif defined(_MSC_VER)
   #define UNUSED __pragma(warning(suppress: 4100))
   #else
   #define UNUSED [[maybe_unused]]
   #endif
   ```

### Evolution

- **1980s-1990s**: `#pragma` existed from early C. GCC introduced `__attribute__` in the 1990s.
- **C99 (1999)**: `_Pragma()` operator. `restrict` keyword.
- **C++11 (2011)**: `[[...]]` standard attribute syntax introduced. `[[noreturn]]`, `[[carries_dependency]]`.
- **C++14 (2014)**: `[[deprecated]]`.
- **C++17 (2017)**: `[[nodiscard]]`, `[[fallthrough]]`, `[[maybe_unused]]`. Significant expansion.
- **C++20 (2020)**: `[[likely]]`, `[[unlikely]]`, `[[no_unique_address]]`. `[[nodiscard("reason")]]` with message.
- **C++23 (2023)**: `[[assume(expr)]]`. More attribute standardization.
- **C23 (2023)**: C adopts `[[...]]` syntax from C++, replacing `_Noreturn` etc. with `[[noreturn]]`.
- **Ongoing**: C++ committee continues to standardize more attributes from vendor extensions into `[[...]]`.
- **Regret**: The biggest regret is not having a standard attribute syntax from the beginning. The proliferation of `__attribute__`, `__declspec`, and `#pragma` is universally considered a mess. The `[[...]]` standardization is a long-overdue fix, but backward compatibility means the old systems will never fully go away.

---

## 11. Comparative Analysis

### Syntax Comparison Table

| Language | Syntax | On definitions | On types | On expressions | User-extensible |
|----------|--------|---------------|----------|----------------|-----------------|
| Rust | `#[attr]` / `#![attr]` | Yes | Yes (limited) | Partial | Yes (proc macros) |
| Java | `@Annotation` | Yes | Yes (Java 8+) | No | Yes (`@interface`) |
| Python | `@decorator` | Yes (fn/class) | No | No | Yes (any function) |
| C# | `[Attribute]` | Yes | No | No | Yes (Attribute class) |
| Kotlin | `@Annotation` | Yes | Yes | Yes (expressions) | Yes (annotation class) |
| Swift | `@attribute` | Yes | No | No | Partial (wrappers, macros) |
| Zig | Keywords + `@builtin` | Keywords only | No | `@builtins` on exprs | No |
| Go | Struct tags + `//go:` | Fields only | No | No | No (conventions only) |
| TypeScript | `@decorator` | Yes (class-related) | No | No | Yes (any function) |
| C/C++ | `[[attr]]` + `__attribute__` + `#pragma` | Yes | Yes (C++11) | `[[likely]]` etc. | No (standard), Yes (compiler extensions) |

### System Unification Spectrum

```
Most Unified ←————————————————————————————————→ Most Fragmented

  Zig      Rust     Java    Kotlin    C#     Swift    Python    TS     Go     C/C++
  (none)   (one)    (one)   (one)    (two)   (two+)   (two)   (three) (five) (four+)
```

**Languages with ONE unified system:**
- **Rust**: `#[attr]` for everything (cfg, derive, test, inline, custom macros)
- **Java**: `@Annotation` for everything (with retention policies to distinguish compile vs runtime)
- **Kotlin**: `@Annotation` (inherited from Java, with use-site targets)

**Languages with TWO systems (kept separate intentionally):**
- **C#**: `[Attribute]` (metadata) + `#if` (conditional compilation). Separate because conditional compilation is text-level, not semantic.
- **Python**: `@decorator` (code transformation) + type hints (passive metadata). Separate because one is executable, the other is not.

**Languages with MULTIPLE systems:**
- **Go**: Struct tags + `//go:` directives + build constraints + doc comments. Fragmented by design philosophy ("simple language").
- **C/C++**: `[[attr]]` + `__attribute__` + `__declspec` + `#pragma`. Fragmented by history and vendor competition.
- **TypeScript**: Decorators + JSDoc + triple-slash + modifiers. Fragmented by JavaScript legacy and gradual typing.
- **Swift**: `@attribute` + property wrappers + result builders + macros + `#if`. Growing complexity.

### Compile-Time vs Runtime Matrix

| Language | Compile-time only | Runtime queryable | Both |
|----------|------------------|-------------------|------|
| Rust | ALL attributes | None (no reflection) | - |
| Java | `@Override` | `RUNTIME` retention | `CLASS` retention |
| Python | None (interpreted) | ALL (everything is runtime) | - |
| C# | `[Conditional]`, `#if` | Most `[Attributes]` | Source generators |
| Kotlin | `SOURCE` retention | `RUNTIME` retention (default) | `BINARY` |
| Swift | Most attributes | `@objc` metadata | - |
| Zig | ALL (comptime) | None (no reflection) | - |
| Go | `//go:` directives | Struct tags (reflection) | - |
| TypeScript | JSDoc, `///` | Decorators | - |
| C/C++ | ALL | None (no reflection) | - |

### Evolution Patterns

**Languages that started with multiple systems and partially merged:**
- **C/C++**: `__attribute__` (GCC) + `__declspec` (MSVC) partially merged into `[[...]]` (C++11/C23). Merger is ongoing but will never be complete due to backward compatibility.
- **C#**: Source generators (C# 9) unified the "compile-time attribute processing" story, bridging the gap between passive `[Attributes]` and code generation.

**Languages that deliberately keep systems separate:**
- **Python**: Decorators and type hints are intentionally different things. Decorators execute code; type hints are passive. Mixing them (as Pydantic does) is considered a pragmatic hack, not ideal design.
- **Go**: The Go team explicitly rejects proposals for a unified annotation system. Each metadata system serves a different purpose and different processing pipeline.
- **Swift**: `@attributes` and `#if` conditional compilation are separate because they operate at different levels (semantic vs textual).

**Languages that designed one system from the start:**
- **Rust**: The `#[attr]` system was designed holistically from the beginning. Even when proc macros added code generation, they used the same syntax.
- **Java**: `@Annotation` was designed as a complete system with retention policies, targets, and extensibility.

### What Works Well

1. **Rust's unified `#[attr]` syntax**: One syntax for everything (cfg, derive, test, custom). Consistent, learnable, extensible. The inner/outer distinction (`#![]` vs `#[]`) is a minor wart but overall the system is well-regarded.

2. **Java's retention policies**: Explicitly declaring SOURCE/CLASS/RUNTIME retention is clear and prevents confusion about when metadata is available. Many languages would benefit from this concept.

3. **Python's simplicity**: Decorators are just functions. No special syntax for defining them. No separate "annotation processor" concept. The mental model is trivially simple.

4. **C#'s attribute-as-class design**: Attributes are real types with constructors, validation, and IDE support. Rich metadata with compile-time checking of attribute arguments.

5. **Kotlin's use-site targets**: `@field:`, `@get:`, `@set:` elegantly solve the "which element does this annotate?" ambiguity. Other languages struggle with this (especially when one source construct maps to multiple compiled constructs).

6. **Zig's comptime approach**: No special system needed. If you want compile-time metadata, write comptime code. Radical simplicity, though it sacrifices conventionality.

### What Causes Confusion

1. **Multiple incompatible systems** (C/C++, Go, TypeScript): Developers must learn which system to use when. Cross-system interaction is weak or nonexistent.

2. **Implicit attribute targets**: When an attribute could apply to multiple things (property vs field vs getter), implicit resolution rules are a constant source of bugs (Kotlin, C#).

3. **Stringly-typed metadata** (Go struct tags, many C# attributes): No compile-time validation of string contents.

4. **Macro/attribute boundary blur** (Rust proc macros, Swift macros): When "metadata" can arbitrarily rewrite code, it becomes hard to understand what code actually does.

5. **Retention policy confusion** (Java default = CLASS, not RUNTIME): Wrong defaults cause subtle bugs.

6. **Decorator ordering** (Python: bottom-up application): Counterintuitive and a frequent source of bugs.

7. **Experimental features shipped too early** (TypeScript experimental decorators): Once an ecosystem depends on an unstable API, migration is painful.

---

## 12. Design Recommendations for Simple

Based on this research, here are key considerations for Simple's tag system design:

### Recommendation 1: ONE Unified Syntax

Use a single tag syntax for all metadata. Avoid having separate systems for different use cases. Rust and Java demonstrate that a unified system is learnable and powerful. C/C++ and Go demonstrate that multiple systems cause fragmentation and confusion.

### Recommendation 2: Explicit Targets When Ambiguous

Follow Kotlin's lead with explicit target specifiers. If a tag could apply to multiple elements (e.g., a property that compiles to a field + getter + setter), provide a target prefix syntax. Make the default target clear and documented.

### Recommendation 3: Distinguish Compile-Time vs Runtime

Consider Java's retention model but with better defaults:
- **Default should match the most common use case** (Java's CLASS default is widely considered wrong; RUNTIME would have been better)
- Make it explicit whether a tag is available at runtime, survives compilation, or is source-only
- If Simple has no runtime reflection, all tags are compile-time (like Rust/Zig), which simplifies things

### Recommendation 4: Typed, Not Stringly-Typed

Tag arguments should be typed and validated at compile time, not raw strings. Go's struct tags are the cautionary tale here. C#'s approach of making attributes real types with constructors is a good model.

### Recommendation 5: User-Extensible

Allow users to define custom tags. Rust, Java, C#, and Kotlin all support this and it is essential for library ecosystems (serialization, web frameworks, testing, etc.). Go's inability to do this is widely criticized.

### Recommendation 6: Composability

Allow tag composition -- defining a tag that implies other tags. This reduces repetition. Kotlin's type aliases for annotations and C#'s attribute combinations are partial models, but no language does this perfectly.

### Recommendation 7: Conditional Compilation via Tags, Not Preprocessor

Follow Rust's `#[cfg]` model rather than C/C++/C#/Swift's `#if` preprocessor. Having conditional compilation in the same system as other metadata is cleaner and allows the compiler to type-check all branches.

### Recommendation 8: Clear Ordering Semantics

If tags can be stacked (multiple tags on one item), define whether order matters and if so, what the application order is. Python's bottom-up decorator application is frequently confusing. Ideally, order should NOT matter for pure metadata tags; only for transformation tags should order be defined.

### Recommendation 9: Do Not Ship Unstable Tag APIs

TypeScript's experimental decorators are the cautionary tale. Do not stabilize a tag system that is likely to change. Better to delay than to create an ecosystem migration problem.

### Recommendation 10: Expression-Level Tags Are Valuable

Kotlin demonstrates that annotating expressions (not just declarations) is useful for things like suppressing warnings on specific casts, marking specific lambda behaviors, etc. Consider supporting this from the start rather than adding it later.

---

## Summary Matrix

| Criterion | Best Example | Worst Example | Simple Should... |
|-----------|-------------|---------------|-----------------|
| Unified syntax | Rust `#[attr]` | C/C++ (4 systems) | Use ONE syntax |
| Compile vs runtime | Java (explicit retention) | Python (everything runtime) | Be explicit |
| User extensibility | Java/C# (types) | Go/Zig (none) | Allow custom tags |
| Target clarity | Kotlin (`@field:`) | C# (implicit) | Support explicit targets |
| Type safety | C# (typed args) | Go (string tags) | Type-check tag args |
| Conditional compilation | Rust (`#[cfg]`) | C++ (`#ifdef`) | Integrate into tag system |
| Simplicity | Python (fn decorators) | Java (annotation processors) | Keep definition simple |
| Ecosystem readiness | Rust (proc macros) | TS (experimental decorators) | Stabilize before shipping |
