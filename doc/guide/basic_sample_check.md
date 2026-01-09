Below is a spec-to-sample “verification pack” aligned to your documentation index, with one or more runnable-style examples per spec area. I’m treating these as **system-check samples**: each file is designed to exercise a concrete rule or feature in the spec (including a few negative tests that should fail in compiler-mode or type-checking).

## 1) Language spec inventory (from your `doc/spec/language.md` index)

Core language specs: Syntax, Types, Units, Data Structures, Functions, Traits, Memory. ([GitHub][1])
Advanced specs: Concurrency, Metaprogramming, Stdlib, GPU & SIMD. ([GitHub][1])
Your `doc/README.md` also references `doc/spec/lexer_parser.md` and `doc/import_export_and__init__.md`, but those paths currently 404 via the same raw fetch method used for other docs. ([GitHub][2])

## 2) Checklist: spec → sample files

* **Syntax** (`doc/spec/syntax.md`) → `00_syntax_basics.spl`, `01_literals_strings_units.spl`, `02_calls_trailing_blocks.spl`, `03_functional_update_arrow.spl` ([GitHub][3])
* **Types** (`doc/spec/types.md`) → `10_types_mutability.spl`, `11_compound_types.spl` ([GitHub][4])
* **Units** (`doc/spec/units.md`) → `20_units_public_api_positive.spl`, `21_units_public_api_negative.spl` ([GitHub][5])
* **Data Structures** (`doc/spec/data_structures.md`) → `30_struct_class_semantics.spl`, `31_auto_forward_properties.spl` ([GitHub][6])
* **Functions & Pattern Matching** (`doc/spec/functions.md`) → `40_functions_closures.spl`, `41_match_exhaustive.spl`, `42_constructor_polymorphism.spl` ([GitHub][7])
* **Traits** (`doc/spec/traits.md`) → `50_traits_default_methods.spl`, `51_trait_bounds_polymorphism.spl` ([GitHub][8])
* **Memory** (`doc/spec/memory.md`) → `60_memory_gc_unique_shared_weak_handle.spl` ([GitHub][9])
* **Concurrency** (`doc/spec/concurrency.md`) + design notes (`doc/design/concurrency.md`) → `70_actors_send_recv_reply_join.spl`, `71_async_await_skeleton.spl` ([GitHub][10])
* **Metaprogramming** (`doc/spec/metaprogramming.md`) → `80_macro_define_counter.spl`, `81_dsl_trailing_blocks.spl` ([GitHub][11])
* **Stdlib** (`doc/spec/stdlib.md`) → `90_stdlib_semantic_types_and_variants.spl` ([GitHub][12])
* **GPU & SIMD** (`doc/spec/gpu_simd/README.md`) → `95_simd_vectors.spl`, `96_gpu_buffer_kernel_skeleton.spl` ([GitHub][13])

---

# 3) Sample code pack

## 00_syntax_basics.spl (indentation blocks, if/else, interpreter vs compiler mode)

```simple
# Default common imports are automatically available (print, etc.)
# No explicit import needed for basic I/O functions

# Interpreter-mode friendly (types optional). In compiler mode, add parameter/return types.
fn sign_desc(x):
    if x > 0:
        return "positive"
    else:
        return "non-positive"

# Cases without "let" - direct assignments and expressions
result = sign_desc(3)  # Direct assignment without let
print "sign_desc(3) = {result}"

# Direct expression evaluation
print "sign_desc(0) = {sign_desc(0)}"

# Type inference in function - return type inferred from body
fn double(x):  # Parameter and return types inferred
    x * 2  # Return type inferred as same as x's type

number = 21
doubled = double(number)  # Without let, direct assignment
print "double({number}) = {doubled}"
```

## 01_literals_strings_units.spl (numeric formats, interpolation, raw strings, unit suffix literals)

```simple
# Numeric literal formats & underscores :contentReference[oaicite:15]{index=15}
let dec = 1_000_000
let hex = 0xFF
let bin = 0b1111_0000
let oct = 0o755

# Interpolated string (double quotes interpolate by default)
print "dec={dec} hex={hex} bin={bin} oct={oct}"

# Raw string (single quotes = no interpolation / no escapes) :contentReference[oaicite:16]{index=16}
let path = 'C:\Users\name'
print "raw_path={path}"

# Unit-typed numeric literals (suffix with underscore) :contentReference[oaicite:17]{index=17}
let distance = 100_km
let duration = 2_hr
let user = 42_uid

print "distance={distance} duration={duration} user={user}"
```

## 02_calls_trailing_blocks.spl (statement-level no-paren calls, trailing block lambdas)

```simple
# No-parens calls allowed at statement level; nested calls should use parens.

fn format_pair(a, b):
    return "({a}, {b})"

# OK: outermost call can omit parens in statement position (DSL-style)
print format_pair(1, 2)

# Lambda cases - various lambda syntaxes
nums = [1, -2, 3, -4, 5]  # Without let

# Simple lambda with type inference
add_one = \x: x + 1  # Lambda type inferred from usage

# Filter with a trailing lambda block  
positives = nums.filter \x: x > 0

# Map with trailing block
doubled = positives.map \x: x * 2

# Multi-parameter lambda
zip_with = \a, b: (a, b)  # Types inferred
pairs = [1, 2, 3].zip([4, 5, 6]).map zip_with

# Lambda with closure over local variables
multiplier = 10
scaled = nums.map \x: x * multiplier  # Captures multiplier

# Complex lambda with block body
processed = nums.filter \x:
    abs_x = abs(x)
    abs_x > 2

doubled.each \item:
    print "item={item}"
```

## 03_functional_update_arrow.spl (`->` functional update sugar)

```simple
# `target->method(...)` means: target = target.method(...) :contentReference[oaicite:20]{index=20}

class Bag:
    items: [i64]
    fn append(x: i64) -> Bag:
        self.items.push(x)
        return self

    fn sort() -> Bag:
        self.items.sort()
        return self

let mut b = Bag(items: [])
b->append(3)->append(1)->append(2)->sort()

print "bag={b.items}"
```

---

## 09_type_inference.spl (type inference in functions, traits, and classes)

```simple
# Type inference in functions - parameter and return types inferred
fn add_nums(a, b):  # Types inferred from usage
    a + b  # Return type inferred

result = add_nums(1, 2)  # Function types inferred as i64 -> i64 -> i64
print "add result: {result}"

# Generic function with type inference
fn identity(x):  # Generic, type inferred per call site
    x

num_val = identity(42)      # T = i64
str_val = identity("hello") # T = str

# Type inference in trait implementations
trait Addable:
    fn add(other) -> Self  # Self type inferred

struct Point:
    x, y  # Field types inferred from constructor usage

impl Addable for Point:
    fn add(other):  # Parameter and return types inferred from trait
        Point(x: self.x + other.x, y: self.y + other.y)

# Type inference in classes
class Counter:
    value  # Type inferred from constructor
    
    fn increment():  # Return type inferred (void)
        self.value = self.value + 1
    
    fn get():  # Return type inferred from return expression
        self.value

counter = Counter(value: 0)  # value type inferred as i64
counter.increment()
print "counter: {counter.get()}"

# Method chaining with type inference
chain_result = [1, 2, 3, 4, 5]
    .filter(\x: x > 2)  # Types inferred through chain
    .map(\x: x * 2)
    .reduce(\acc, x: acc + x)

print "chain result: {chain_result}"
```

## 10_types_mutability.spl (struct immutability default, mut struct, class mutability default, immut class)

```simple
# Structs immutable by default; `mut struct` makes fields writable. :contentReference[oaicite:21]{index=21}

struct Point:
    x: f64
    y: f64

mut struct Cursor:
    x: f64
    y: f64

let p = Point(x: 1, y: 2)
# p.x = 9  # should be an error (immutable struct)

let c = Cursor(x: 0, y: 0)
c.x = 10
print "cursor=({c.x}, {c.y})"

# Classes mutable by default; `immut class` prevents mutation. :contentReference[oaicite:22]{index=22}
class Person:
    name: str
    age: i32
    fn birthday():
        self.age = self.age + 1

let a = Person(name: "Alice", age: 30)
a.birthday()
print "alice_age={a.age}"
```

## 11_compound_types.spl (tuples, lists, dicts; type annotations optional in interpreter)

```simple
# Compound type shapes with type inference and without let

pair = (1, "hello")  # Without let, tuple type inferred
match pair:
    case (n, s):
        print "n={n} s={s}"

list = [1, 2, 3]  # List type inferred as [i64]
print "len={list.len()}"

# Dictionary with inferred types
m = {"a": 1, "b": 2}  # Type inferred as {str: i64}
print "m[a]={m["a"]}"

# Complex nested structures without let
data = [
    {"name": "Alice", "age": 30},
    {"name": "Bob", "age": 25}
]  # Type: [{str: any}] or more specific inferred type

# Type inference with compound operations
ages = data.map(\person: person["age"])  # Type inferred as [i64]
avg_age = ages.sum() / ages.len()  # Type inferred as i64
print "average age: {avg_age}"

# Tuple destructuring without let
(first, second) = ("hello", "world")
print "first: {first}, second: {second}"
```

---

## 20_units_public_api_positive.spl (semantic types in public APIs)

```simple
# Rule: avoid bare primitives in public APIs; prefer unit/newtypes/enums/Option/Result. :contentReference[oaicite:24]{index=24}

# Assume UserId and FilePath are unit types provided/declared in your stdlib.
# Numeric unit literal example uses `_uid`. :contentReference[oaicite:25]{index=25}

pub fn get_user_id() -> UserId:
    return 42_uid

pub fn read_config(path: FilePath) -> Result[Bytes, IOError]:
    return std.fs.read_bytes(path)
```

## 21_units_public_api_negative.spl (expected warnings/errors)

```simple
# These are intended “negative tests” for the unit-type rules. :contentReference[oaicite:26]{index=26}

# WARNING (or error if deny enabled): bare primitive return in public API
pub fn bad_get_user_id() -> i64:
    return 42

# WARNING (or error if deny enabled): bare string in public API
pub fn bad_read_file(path: str) -> Bytes:
    return std.fs.read_bytes(path)

# ERROR (always): implicit nil without Option[...] in public API shape
pub fn bad_find_user(id: UserId) -> User:
    # if a user is not found, returning nil here should be illegal
    return nil
```

---

## 30_struct_class_semantics.spl (value copy vs reference semantics)

```simple
# Structs are value types (copy-on-assign); classes are reference types. :contentReference[oaicite:27]{index=27}

mut struct Cursor:
    x: i32
    y: i32

class Box:
    value: i32

let a = Cursor(x: 1, y: 2)
let b = a       # copy
b.x = 9
print "a.x={a.x} b.x={b.x}"   # expect a.x still 1

let p = Box(value: 10)
let q = p       # reference alias
q.value = 99
print "p.value={p.value} q.value={q.value}"  # expect both 99
```

## 31_auto_forward_properties.spl (get_/set_/is_ forwarding)

```simple
# Auto-forwarding properties for get_/set_/is_ prefixes. :contentReference[oaicite:28]{index=28}

class Config:
    _port: i32

    fn get_port() -> i32:
        return self._port

    fn set_port(p: i32):
        self._port = p

let mut cfg = Config(_port: 8080)

# Property-style access should forward to get_/set_
print "port={cfg.port}"
cfg.port = 9090
print "port={cfg.port}"
```

---

## 40_functions_closures.spl (first-class functions + closures)

```simple
# First-class functions and lambdas with backslash params.

fn add(a: i64, b: i64) -> i64:
    return a + b

f = add  # Without let, direct assignment
print "f(2,3)={f(2,3)}"

# Lambda cases with different patterns
multiplier = 3
scale = \x: x * multiplier  # Simple closure
print "scale(10)={scale(10)}"

# Lambda with multiple parameters
combine = \a, b, op: op(a, b)
result = combine(5, 3, add)
print "combine result: {result}"

# Lambda with conditional logic
check_sign = \n:
    if n > 0:
        "positive"
    elif n < 0:
        "negative" 
    else:
        "zero"

values = [-1, 0, 1]
signs = values.map(check_sign)  # Type inference for map
print "signs: {signs}"

# Higher-order function with lambda parameter
fn apply_twice(f, x):
    f(f(x))

# Without let - direct usage
double_twice = apply_twice(\x: x * 2, 5)
print "double twice: {double_twice}"  # Should be 20

# Closure capturing multiple variables
base = 10
offset = 5
transform = \x: (x + offset) * base
print "transform(3): {transform(3)}"  # (3 + 5) * 10 = 80
```

## 41_match_exhaustive.spl (pattern matching, guards, destructuring, exhaustiveness)

```simple
# Match patterns and exhaustiveness requirement. :contentReference[oaicite:30]{index=30}

enum Color:
    Red
    Green
    Blue

fn color_name(c: Color) -> str:
    match c:
        case Red:   return "red"
        case Green: return "green"
        case Blue:  return "blue"  # include all cases to satisfy exhaustiveness

print color_name(Color.Red)

let x = -5
match x:
    case n if n < 0: print "neg {n}"
    case n: print "non-neg {n}"
```

## 42_constructor_polymorphism.spl (constructor as first-class value)

```simple
# Constructor polymorphism is explicitly called out in the functions spec. :contentReference[oaicite:31]{index=31}

struct Point:
    x: i64
    y: i64

fn make_with(ctor, a: i64, b: i64):
    # ctor is a “constructor-like” callable
    return ctor(x: a, y: b)

let p = make_with(Point, 3, 4)
print "p=({p.x},{p.y})"
```

---

## 50_traits_default_methods.spl (trait with required + default method)

```simple
# Trait with required method + default method implementation. :contentReference[oaicite:32]{index=32}

trait Printable:
    fn stringify() -> str
    fn print_self():
        print self.stringify()

struct User:
    name: str

impl Printable for User:
    fn stringify() -> str:
        return "User(name={self.name})"

let u = User(name: "Kim")
u.print_self()
```

## 51_trait_bounds_polymorphism.spl (polymorphic function over a trait)

```simple
# Polymorphism over any type implementing a trait. :contentReference[oaicite:33]{index=33}

trait Named:
    fn name() -> str

struct Project:
    title: str

impl Named for Project:
    fn name() -> str:
        return self.title

fn greet(x: Named) -> str:
    return "hello {x.name()}"

print greet(Project(title: "simple"))
```

---

## 60_memory_gc_unique_shared_weak_handle.spl (GC T, unique &T, shared *T, weak -T, handle +T)

```simple
# Pointer kinds are explicit: T (GC), &T unique, *T shared, -T weak, +T handle. :contentReference[oaicite:34]{index=34}

class Player:
    name: str
    hp: i32

# GC-managed (default)
let p: Player = Player(name: "Hero", hp: 100)

# Unique owner
let u: &Player = new(&) Player(name: "Solo", hp: 50)
let v = move u
# print u.hp  # should be compile error: moved

# Shared owner
let s1: *Player = new* Player(name: "Shared", hp: 75)
let s2 = s1  # refcount +1

# Weak pointer
let w: -Player = weak_of(s1)
let maybe_strong = w.upgrade()
match maybe_strong:
    case Some(sp): print "upgraded hp={sp.hp}"
    case None: print "expired"

# Handle pointer (resource-like; runtime-managed pool)
let h: +Player = new+ Player(name: "HandleGuy", hp: 1)
with handle_get(h) as view:
    print "handle view hp={view.hp}"
```

---

## 70_actors_send_recv_reply_join.spl (spawn/send/recv/reply/join)

```simple
# Actor model primitives: spawn, send, recv, reply, join. :contentReference[oaicite:35]{index=35}

fn worker():
    loop:
        let msg = recv()
        match msg:
            case "ping":
                reply("pong")
            case "stop":
                reply("bye")
                return
            case _:
                reply("unknown")

let a = spawn worker()

send(a, "ping")
print "got={recv(a)}"   # expect pong

send(a, "stop")
print "got={recv(a)}"   # expect bye

join(a)
print "joined"
```

## 71_async_await_skeleton.spl (shape-only sample; aligns with concurrency direction)

```simple
# This is a shape-check sample: async/await is part of the concurrency spec scope. :contentReference[oaicite:36]{index=36}

async fn fetch_user(id: UserId) -> Result[User, NetError]:
    let resp = await http.get("/users/{id}")
    return parse_user(resp)

async fn main():
    let r = await fetch_user(42_uid)
    match r:
        case Ok(u): print "user={u}"
        case Err(e): print "err={e}"
```

---

## 80_macro_define_counter.spl (macro that generates static + functions)

```simple
# Macro system: compile-time codegen with declared names/types; example macro in spec. :contentReference[oaicite:37]{index=37}

macro define_counter(name: Ident):
    gen_code:
        mut static {name}: i64 = 0

        fn {name}_increment() -> i64:
            {name} = {name} + 1
            return {name}

        fn {name}_reset():
            {name} = 0

define_counter(Requests)

print Requests_increment()
print Requests_increment()
Requests_reset()
print Requests_increment()
```

## 81_dsl_trailing_blocks.spl (macro + trailing blocks = DSL-style)

```simple
# Combines “DSL-ish” call style + trailing blocks from syntax spec. :contentReference[oaicite:38]{index=38}

class Router:
    routes: {str: fn() -> str}

    fn get(path: str, handler: fn() -> str):
        self.routes[path] = handler

let mut r = Router(routes: {})

r.get "/health", \: "ok"
r.get "/hello", \: "hello"

print r.routes["/health"]()
print r.routes["/hello"]()
```

---

## 90_stdlib_semantic_types_and_variants.spl (semantic-only APIs + variants notion)

```simple
# Stdlib goals: variants (async/sync, gc/no_gc, platform overlays) + semantic types in public APIs. :contentReference[oaicite:39]{index=39}

# Example: “semantic types only” in the boundary
pub fn app_config_path() -> FilePath:
    return "/etc/simple/app.toml"_file

pub fn load_config(path: FilePath) -> Result[Config, ConfigError]:
    let bytes = std.fs.read_bytes(path)?
    return std.config.parse(bytes)

# Variant usage is implementation-defined; treat as a config-driven import resolution demo.
# (Your stdlib spec describes the variant-aware layout/goal, not the concrete syntax here.) :contentReference[oaicite:40]{index=40}
```

---

## 95_simd_vectors.spl (vec[N,T], lane-wise ops, reductions)

```simple
# SIMD vector types and ops. :contentReference[oaicite:41]{index=41}

type f32x4 = vec[4, f32]

let a: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let b: f32x4 = vec[5.0, 6.0, 7.0, 8.0]

let sum = a + b
print "sum0={sum[0]} sum_all={sum.sum()}"
print "all_positive={(a > 0.0).all()}"
```

## 96_gpu_buffer_kernel_skeleton.spl (device/context/buffer/kernel shape)

```simple
# GPU API surface + buffer upload/download shape. :contentReference[oaicite:42]{index=42}

use gpu

let ctx = gpu.Context.default()
let buf: gpu.Buffer[f32] = ctx.alloc(1024)

let host_data: [f32; 1024] = [...]
buf.upload(host_data)

# Kernel shape (details depend on your eventual compiler/runtime implementation)
@gpu.kernel
fn scale2(in: gpu.Buffer[f32], out: gpu.Buffer[f32]):
    let i = gpu.global_id()
    out[i] = in[i] * 2.0

ctx.launch(scale2, grid: 1024, args: (buf, buf))

let result = buf.download()
print "result0={result[0]}"
```

---

## Notes on gaps I could not cover from the repo docs (yet)

* The documentation index references **Lexer & Parser** and **Import/Export + `__init__` module system**, but the specific referenced markdown paths are not currently retrievable (404) via GitHub’s raw endpoint in this session. ([GitHub][2])
* If you re-add those files (or confirm the correct paths), I can extend this pack with:

  * token/grammar-driven “parser golden” samples (1 file per grammar production),
  * module layout samples (`__init__.spl` directory defaults, export/import visibility, macro import rules, etc.).

If you want, I can also reformat the above into an actual `samples/` directory layout (one file per section, with a top-level `SAMPLES.md` runner checklist) consistent with how you plan to execute interpreter-mode vs compiler-mode checks.

[1]: https://github.com/ormastes/simple/blob/main/doc/spec/language.md?raw=1 "raw.githubusercontent.com"
[2]: https://github.com/ormastes/simple/blob/main/doc/README.md?raw=1 "raw.githubusercontent.com"
[3]: https://github.com/ormastes/simple/blob/main/doc/spec/syntax.md?raw=1 "raw.githubusercontent.com"
[4]: https://github.com/ormastes/simple/blob/main/doc/spec/types.md?raw=1 "raw.githubusercontent.com"
[5]: https://github.com/ormastes/simple/blob/main/doc/spec/units.md?raw=1 "raw.githubusercontent.com"
[6]: https://github.com/ormastes/simple/blob/main/doc/spec/data_structures.md?raw=1 "raw.githubusercontent.com"
[7]: https://github.com/ormastes/simple/blob/main/doc/spec/functions.md?raw=1 "raw.githubusercontent.com"
[8]: https://github.com/ormastes/simple/blob/main/doc/spec/traits.md?raw=1 "raw.githubusercontent.com"
[9]: https://github.com/ormastes/simple/blob/main/doc/spec/memory.md?raw=1 "raw.githubusercontent.com"
[10]: https://github.com/ormastes/simple/blob/main/doc/spec/concurrency.md?raw=1 "raw.githubusercontent.com"
[11]: https://github.com/ormastes/simple/blob/main/doc/spec/metaprogramming.md?raw=1 "raw.githubusercontent.com"
[12]: https://github.com/ormastes/simple/blob/main/doc/spec/stdlib.md?raw=1 "raw.githubusercontent.com"
[13]: https://github.com/ormastes/simple/blob/main/doc/spec/gpu_simd/README.md?raw=1 "raw.githubusercontent.com"
