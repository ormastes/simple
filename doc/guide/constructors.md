# Constructors in Simple

Simple uses **static methods** for constructors, following a pattern similar to Rust and modern languages.

## Basic Constructor Pattern

### Struct with Constructor

```simple
struct Point:
    x: i64
    y: i64

impl Point:
    # Constructor - fn new() is implicitly static at module level
    fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)

    # Alternative constructor (also implicitly static)
    fn origin() -> Point:
        return Point(x: 0, y: 0)

# ✅ PRIMARY: Direct construction works!
val p1 = Point(3, 4)

# ✅ OPTIONAL: Or use .new() if you defined it
val p2 = Point.new(3, 4)
val p3 = Point.origin()
```

### Class with Constructor

```simple
class Person:
    name: String
    age: i64

impl Person:
    # Can use explicit 'static' if you prefer clarity
    static fn new(name: String, age: i64) -> Person:
        return Person(name: name, age: age)

# Usage
val alice = Person.new("Alice", 30)
```

## Constructor Patterns

### 1. Basic Constructor

```simple
struct Rectangle:
    width: i64
    height: i64

impl Rectangle:
    static fn new(width: i64, height: i64) -> Rectangle:
        return Rectangle(width: width, height: height)

val rect = Rectangle.new(10, 20)
```

### 2. Default Constructor

```simple
impl Rectangle:
    static fn default() -> Rectangle:
        return Rectangle(width: 0, height: 0)

val empty = Rectangle.default()
```

### 3. Multiple Constructors (Named Constructors)

```simple
impl Rectangle:
    # Main constructor
    static fn new(width: i64, height: i64) -> Rectangle:
        return Rectangle(width: width, height: height)

    # Square constructor
    static fn square(size: i64) -> Rectangle:
        return Rectangle { width: size, height: size }

    # From area
    static fn from_area(area: i64) -> Rectangle:
        val side = sqrt(area) as i64
        return Rectangle(width: side, height: side)

# Usage
val rect = Rectangle.new(10, 20)
val sq = Rectangle.square(15)
val area_rect = Rectangle.from_area(100)
```

### 4. Constructor with Validation

```simple
struct PositiveNumber:
    value: i64

impl PositiveNumber:
    static fn new(value: i64) -> Option<PositiveNumber>:
        if value > 0:
            return Some(PositiveNumber(value: value))
        else:
            return None

# Usage with pattern matching
match PositiveNumber.new(42):
    case Some(num):
        print "Valid: {num.value}"
    case None:
        print "Invalid number"
```

### 5. Builder Pattern

```simple
struct Config:
    host: String
    port: i64
    timeout: i64
    retries: i64

impl Config:
    # Start with defaults
    static fn builder() -> Config:
        return Config(
            host: "localhost",
            port: 8080,
            timeout: 30,
            retries: 3
        )

    # Fluent setters
    me with_host(host: String) -> Config:
        self.host = host
        return self

    me with_port(port: i64) -> Config:
        self.port = port
        return self

    me with_timeout(timeout: i64) -> Config:
        self.timeout = timeout
        return self

# Usage - fluent API
val config = Config.builder()
    .with_host("example.com")
    .with_port(9000)
    .with_timeout(60)
```

## Method Types in Constructors

### Static Methods (Constructors)

```simple
impl Point:
    # No 'self' - operates on type, not instance
    static fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)
```

### Instance Methods (Immutable)

```simple
impl Point:
    # Implicit 'self' - readonly access
    fn distance_from_origin() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)
```

### Mutable Methods

```simple
impl Point:
    # 'me' keyword - can modify self
    me move_by(dx: i64, dy: i64):
        self.x = self.x + dx
        self.y = self.y + dy
```

## Calling Syntax

### ✅ Preferred: Dot Syntax

```simple
# Static methods (constructors)
val obj = MyStruct.new()
val date = Date.today()
val result = Result.ok(42)

# Instance methods
obj.method()
val value = obj.get_value()
```

### ❌ Deprecated: Double-Colon Syntax

```simple
# This shows a deprecation warning
val obj = MyStruct::new()  # Warning: Use dot syntax instead
```

## Complete Example

```simple
# Define a struct
struct BankAccount:
    account_number: String
    balance: i64
    owner: String

impl BankAccount:
    # Constructor
    static fn new(account_number: String, owner: String) -> BankAccount:
        return BankAccount(
            account_number: account_number,
            balance: 0,
            owner: owner
        )

    # Constructor with initial deposit
    static fn with_deposit(account_number: String, owner: String, initial: i64) -> BankAccount:
        return BankAccount(
            account_number: account_number,
            balance: initial,
            owner: owner
        )

    # Immutable query
    fn get_balance() -> i64:
        return self.balance

    # Mutable operation
    me deposit(amount: i64):
        self.balance = self.balance + amount

    # Mutable operation with result
    me withdraw(amount: i64) -> bool:
        if amount <= self.balance:
            self.balance = self.balance - amount
            return true
        else:
            return false

# Usage
val account = BankAccount.new("ACC-001", "Alice")
account.deposit(1000)

val rich_account = BankAccount.with_deposit("ACC-002", "Bob", 5000)

if account.withdraw(500):
    print "Withdrawal successful. Balance: {account.get_balance()}"
else:
    print "Insufficient funds"
```

## Generic Constructors

```simple
struct Container<T>:
    value: T

impl<T> Container<T>:
    static fn new(value: T) -> Container<T>:
        return Container(value: value)

    fn get() -> T:
        return self.value

# Usage
val int_container = Container.new(42)
val str_container = Container.new("hello")
```

## Common Patterns

### Option/Result Style

```simple
# Option constructor (from stdlib)
val some_value = Some(42)
val no_value = None

# Result constructor (from stdlib)
val success = Ok(100)
val failure = Err("error message")
```

### Collection Constructors

```simple
# List
val empty_list = List.new()
val with_items = List.from([1, 2, 3])

# Map
val empty_map = Map.new()
val with_data = Map.from({"key": "value"})

# Set
val empty_set = Set.new()
val with_elements = Set.from([1, 2, 3])
```

## Best Practices

1. **Use `new` for main constructor**: Convention for the primary way to create an instance
2. **Named constructors for variants**: Use descriptive names (`from_string`, `default`, `empty`)
3. **Return Option/Result for fallible constructors**: When validation is needed
4. **Use dot syntax**: `Type.new()` is preferred over deprecated `Type::new()`
5. **Keep constructors simple**: Move complex logic to separate methods
6. **Use builder pattern for many parameters**: When you have >3-4 parameters

## See Also

- [Coding Standards](../../.claude/skills/coding.md) - Full syntax reference
- [Methods](./methods.md) - Method types and usage
- [Generics](./generics.md) - Generic types and functions
- [Pattern Matching](./pattern_matching.md) - Using constructors with match
