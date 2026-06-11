# Should return 0 (0 + 0)

> 0

<!-- sdn-diagram:id=static_method_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_method_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_method_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_method_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Should return 0 (0 + 0)

0

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/static_method_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

0

        it "compiles static method with parameters":
            val code = """
            class Rectangle:
                width: i64
                height: i64

                static fn create(w: i64, h: i64) -> Rectangle:
                    Rectangle(width: w, height: h)

            fn main() -> i64:
                val r = Rectangle.create(5, 3)
                r.width * r.height

## Scenarios

### Static Method Codegen

#### Basic static method calls

#### compiles simple static method with no parameters

1. static fn origin
2. Point
3. fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Point:
    x: i64
    y: i64

    static fn origin() -> Point:
        Point(x: 0, y: 0)

fn main() -> i64:
    val p = Point.origin()
    p.x + p.y
"""

# Should return 0 (0 + 0)
# Test will be enabled when native mode is working
0
```

</details>

#### compiles static method with parameters

1. static fn create
2. Rectangle
3. fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Rectangle:
    width: i64
    height: i64

    static fn create(w: i64, h: i64) -> Rectangle:
        Rectangle(width: w, height: h)

fn main() -> i64:
    val r = Rectangle.create(5, 3)
    r.width * r.height
"""

# Should return 15 (5 * 3)
0
```

</details>

#### compiles static method with return value

1. static fn add
2. static fn multiply
3. fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Math:
    static fn add(a: i64, b: i64) -> i64:
        a + b

    static fn multiply(a: i64, b: i64) -> i64:
        a * b

fn main() -> i64:
    val sum = Math.add(5, 3)
    val product = Math.multiply(4, 2)
    sum + product
"""

# Should return 16 (8 + 8)
0
```

</details>

#### Static method chaining

#### compiles chained static and instance methods

1. static fn new
2. Builder
3. me set
4. fn get
5. fn main
6. var b = Builder new
7. b set
8. b get


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Builder:
    value: i64

    static fn new() -> Builder:
        Builder(value: 0)

    me set(v: i64):
        self.value = v

    fn get() -> i64:
        self.value

fn main() -> i64:
    var b = Builder.new()
    b.set(42)
    b.get()
"""

# Should return 42
0
```

</details>

#### compiles multiple static calls in sequence

1. static fn zero
2. Counter
3. static fn from
4. Counter
5. fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Counter:
    count: i64

    static fn zero() -> Counter:
        Counter(count: 0)

    static fn from(n: i64) -> Counter:
        Counter(count: n)

fn main() -> i64:
    val c1 = Counter.zero()
    val c2 = Counter.from(10)
    c1.count + c2.count
"""

# Should return 10 (0 + 10)
0
```

</details>

#### Static vs instance disambiguation

#### correctly distinguishes static and instance methods

1. static fn create
2. Calculator
3. fn double
4. me add
5. fn main
6. var calc = Calculator create
7. calc add


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Calculator:
    value: i64

    # Static method - no self
    static fn create(init: i64) -> Calculator:
        Calculator(value: init)

    # Instance method - has self
    fn double() -> i64:
        self.value * 2

    # Instance method - modifies self
    me add(x: i64):
        self.value = self.value + x

fn main() -> i64:
    var calc = Calculator.create(5)
    val doubled = calc.double()
    calc.add(3)
    doubled + calc.value
"""

# Should return 18 (10 + 8)
0
```

</details>

#### handles same method name as static and instance

1. static fn get name
2. fn get name
3. fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Factory:
    name: text

    # Static version
    static fn get_name() -> text:
        "Factory"

    # Instance version
    fn get_name() -> text:
        self.name

fn main() -> i64:
    val static_name = Factory.get_name()
    val instance = Factory(name: "MyFactory")
    val instance_name = instance.get_name()

    if static_name == "Factory" and instance_name == "MyFactory":
        1
    else:
        0
"""

# Should return 1 (both work correctly)
0
```

</details>

#### Static methods calling other methods

#### compiles static method calling another static method

1. static fn square
2. static fn sum of squares
3. Math square
4. fn main
5. Math sum of squares


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Math:
    static fn square(x: i64) -> i64:
        x * x

    static fn sum_of_squares(a: i64, b: i64) -> i64:
        Math.square(a) + Math.square(b)

fn main() -> i64:
    Math.sum_of_squares(3, 4)
"""

# Should return 25 (9 + 16)
0
```

</details>

#### compiles static method calling instance method on created object

1. static fn origin
2. Point
3. static fn manhattan from origin
4. p manhattan
5. fn manhattan
6. fn main
7. Point manhattan from origin


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Point:
    x: i64
    y: i64

    static fn origin() -> Point:
        Point(x: 0, y: 0)

    static fn manhattan_from_origin(x: i64, y: i64) -> i64:
        val p = Point(x: x, y: y)
        p.manhattan()

    fn manhattan() -> i64:
        self.x + self.y

fn main() -> i64:
    Point.manhattan_from_origin(3, 4)
"""

# Should return 7 (3 + 4)
0
```

</details>

#### Edge cases

#### handles static method with no return value

1. static fn log
2. fn main
3. Logger log


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Logger:
    static fn log(message: text):
        print message

fn main() -> i64:
    Logger.log("test")
    42
"""

# Should return 42 (and print "test")
0
```

</details>

#### handles static method in nested class

1. static fn value
2. fn main
3. Outer Inner value


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Outer:
    class Inner:
        static fn value() -> i64:
            100

fn main() -> i64:
    Outer.Inner.value()
"""

# Should return 100
0
```

</details>

#### handles static method with multiple return points

1. static fn validate
2. fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Validator:
    static fn validate(x: i64) -> i64:
        if x < 0:
            return 0
        if x > 100:
            return 100
        x

fn main() -> i64:
    val a = Validator.validate(-5)
    val b = Validator.validate(50)
    val c = Validator.validate(150)
    a + b + c
"""

# Should return 150 (0 + 50 + 100)
0
```

</details>

#### Performance and stress tests

<details>
<summary>Advanced: handles 1000 static method calls efficiently</summary>

#### handles 1000 static method calls efficiently _(slow)_

1. static fn increment
2. fn main
3. result = Counter increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Counter:
    static fn increment(x: i64) -> i64:
        x + 1

fn main() -> i64:
    var result = 0
    for i in 0..1000:
        result = Counter.increment(result)
    result
"""

# Should return 1000
0
```

</details>


</details>

<details>
<summary>Advanced: handles deep call stack with static methods</summary>

#### handles deep call stack with static methods _(slow)_

1. static fn fib
2. Fibonacci fib
3. fn main
4. Fibonacci fib


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Fibonacci:
    static fn fib(n: i64) -> i64:
        if n <= 1:
            n
        else:
            Fibonacci.fib(n - 1) + Fibonacci.fib(n - 2)

fn main() -> i64:
    Fibonacci.fib(10)
"""

# Should return 55 (10th Fibonacci number)
0
```

</details>


</details>

<details>
<summary>Advanced: handles static method with many parameters</summary>

#### handles static method with many parameters _(slow)_

1. static fn sum8
2. fn main
3. Calculator sum8


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Calculator:
    static fn sum8(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64) -> i64:
        a + b + c + d + e + f + g + h

fn main() -> i64:
    Calculator.sum8(1, 2, 3, 4, 5, 6, 7, 8)
"""

# Should return 36 (sum of 1..8)
0
```

</details>


</details>

#### Type system integration

#### handles generic static methods

1. static fn create<T>
2. Container
3. fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Container<T>:
    value: T

    static fn create<T>(v: T) -> Container<T>:
        Container(value: v)

fn main() -> i64:
    val c = Container.create(42)
    c.value
"""

# Should return 42
0
```

</details>

#### handles static method returning Option

1. static fn parse int
2. Some
3. fn main
4. result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Parser:
    static fn parse_int(s: text) -> i64?:
        if s == "42":
            Some(42)
        else:
            None

fn main() -> i64:
    val result = Parser.parse_int("42")
    if result.?:
        result.unwrap()
    else:
        0
"""

# Should return 42
0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
