# Optional Chaining Specification

> obj?.field               # Safe field access - returns Option

<!-- sdn-diagram:id=optional_chaining_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=optional_chaining_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

optional_chaining_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=optional_chaining_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optional Chaining Specification

obj?.field               # Safe field access - returns Option

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OPERATORS-OPTIONAL-CHAIN |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/optional_chaining_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
obj?.field               # Safe field access - returns Option
obj?.method()            # Safe method call - returns Option
obj?.field?.nested?.deep # Safe chaining - short-circuits on None
```

## Key Behaviors

- Optional chaining returns Option<T> for chained operations
- Returns None immediately if any intermediate value is None
- Prevents null pointer exceptions and NullPointerException-style errors
- Works with both field access and method calls
- Can be chained multiple times
- Integrates with null coalescing (`??`) for fallback values

## Scenarios

### Optional Chaining

#### optional field access

#### returns Some when value is present

1. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Profile:
    bio: text

class User:
    name: text
    profile: Option<Profile>

val profile_obj = Profile(bio: "Hello")
val user = User(name: "Alice", profile: Some(profile_obj))
val result = user.profile?.bio
expect result == Some("Hello")
```

</details>

#### returns None when intermediate value is None

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Profile:
    bio: text

class User:
    name: text
    profile: Option<Profile>

val user = User(name: "Bob", profile: None)
val result = user.profile?.bio
expect result == None
```

</details>

#### works with deeply nested structures

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Address:
    city: text

class Profile:
    address: Option<Address>

class User:
    profile: Option<Profile>

val user = User(profile: Some(Profile(address: Some(Address(city: "NYC")))))
# Access profile through optional chaining
val profile_opt = user.profile
expect profile_opt != None
```

</details>

#### short-circuits on first None in chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Address:
    city: text

class Profile:
    address: Option<Address>

class User:
    profile: Option<Profile>

val user = User(profile: None)
val result = user.profile?.address?.city
# Returns None at first None, doesn't try deeper access
expect result == None
```

</details>

#### optional method calls

#### calls method when value is Some

1. fn get doubled
2. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Container:
    value: i64

    fn get_doubled(): self.value * 2

val opt = Some(Container(value: 21))
val result = opt?.get_doubled()
expect result == Some(42)
```

</details>

#### returns None when Option is None

1. fn get doubled


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Container:
    value: i64

    fn get_doubled(): self.value * 2

val opt: Option<Container> = None
val result = opt?.get_doubled()
expect result == None
```

</details>

#### works with chained method calls

1. fn increment
2. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Wrapper:
    value: i64

    fn increment(): Wrapper(value: self.value + 1)

val wrapped = Wrapper(value: 1)
val opt = Some(wrapped)
val result = opt?.increment()?.increment()
# Each ? check wraps result in Option
expect result == Some(Wrapper(value: 3))
```

</details>

#### handles methods with parameters

1. fn add
2. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Calculator:
    value: i64

    fn add(x: i64): self.value + x

val calc_opt = Some(Calculator(value: 10))
val result = calc_opt?.add(5)
expect result == Some(15)
```

</details>

#### chaining field and method access

#### combines field and method access

1. fn double count
2. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Data:
    count: i64

    fn double_count(): self.count * 2

class Container:
    data: Option<Data>

val container = Container(data: Some(Data(count: 5)))
val result = container.data?.double_count()
expect result == Some(10)
```

</details>

#### chains field access followed by field access

1. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Inner:
    name: text

class Middle:
    inner: Option<Inner>

class Outer:
    middle: Middle

val outer = Outer(middle: Middle(inner: Some(Inner(name: "test"))))
val result = outer.middle.inner?.name
expect result == Some("test")
```

</details>

#### with null coalescing operator

#### provides fallback when chaining returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Profile:
    bio: text

class User:
    profile: Option<Profile>

val user: User = User(profile: None)
val result = user.profile?.bio ?? "No bio"
# Optional chaining returns None, ?? provides fallback
expect result == "No bio"
```

</details>

#### uses actual value when chaining succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Profile:
    bio: text

class User:
    profile: Option<Profile>

val user = User(profile: Some(Profile(bio: "Developer")))
val result = user.profile?.bio ?? "No bio"
expect result == "Developer"
```

</details>

#### chains multiple fallbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Settings:
    theme: Option<text>

class User:
    settings: Option<Settings>

val user = User(settings: None)
val result = user.settings?.theme ?? "dark"
expect result == "dark"
```

</details>

#### type preservation

#### wraps return value in Option

1. fn status
2. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Service:
    fn status() -> i64: 200

val service_opt = Some(Service())
val result = service_opt?.status()
# Result is Option<i64>, not i64
expect result == Some(200)
```

</details>

#### preserves complex types through chaining

1. fn get items
2. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class DataContainer:
    items: List<i64>

    fn get_items(): self.items

val container_opt = Some(DataContainer(items: [1, 2, 3]))
val result = container_opt?.get_items()
expect result == Some([1, 2, 3])
```

</details>

#### integration with other features

#### works with collection methods

1. fn find item
2. self items filter
3. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Item:
    name: text

class Inventory:
    items: List<Item>

    fn find_item(name: text) -> Option<Item>:
        self.items.filter(_1.name == name).first

val inventory_opt = Some(Inventory(items: [Item(name: "sword"), Item(name: "shield")]))
val result = inventory_opt?.find_item("sword")
expect result == Some(Item(name: "sword"))
```

</details>

#### handles None in collection operations

1. fn find item
2. self items filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Item:
    name: text

class Inventory:
    items: List<Item>

    fn find_item(name: text) -> Option<Item>:
        self.items.filter(_1.name == name).first

val inventory_opt: Option<Inventory> = None
val result = inventory_opt?.find_item("sword")
expect result == None
```

</details>

#### practical usage patterns

#### simplifies conditional access patterns

1. expect email == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class User:
    name: text
    email: Option<text>

val user = User(name: "Alice", email: Some("alice@example.com"))
# Without optional chaining: would need unwrap or match
val email = user.email?.upper()
expect email == Some("ALICE@EXAMPLE.COM")
```

</details>

#### provides defensive programming in data processing

1. expect detail == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class LogEntry:
    message: text
    details: Option<text>

val log = LogEntry(message: "Error", details: Some("File not found"))
# Direct access to details, then optional chaining
val detail = log.details
expect detail == Some("File not found")
```

</details>

#### enables safe navigation in unknown data structures

1. expect key exists == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Config:
    settings: Option<Dict<text, text>>

val config = Config(settings: Some({"key": "value"}))
# Safe to access even if settings is None
val key_exists = config.settings?.get("key")
expect key_exists == Some("value")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
