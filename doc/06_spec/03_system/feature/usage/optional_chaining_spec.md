# Optional Chaining Specification

> obj?.field               # Safe field access - returns Option

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
| Updated | 2026-08-26 |
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

- returns Some when value is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns Some when value is present")
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

- returns None when intermediate value is None


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns None when intermediate value is None")
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

- works with deeply nested structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with deeply nested structures")
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

- short-circuits on first None in chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("short-circuits on first None in chain")
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

- calls method when value is Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls method when value is Some")
class Container:
    value: i64

    fn get_doubled(): self.value * 2

val opt = Some(Container(value: 21))
val result = opt?.get_doubled()
expect result == Some(42)
```

</details>

#### returns None when Option is None

- returns None when Option is None


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns None when Option is None")
class Container:
    value: i64

    fn get_doubled(): self.value * 2

val opt: Option<Container> = None
val result = opt?.get_doubled()
expect result == None
```

</details>

#### works with chained method calls

- works with chained method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with chained method calls")
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

- handles methods with parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles methods with parameters")
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

- combines field and method access


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines field and method access")
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

- chains field access followed by field access


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains field access followed by field access")
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

- provides fallback when chaining returns None


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides fallback when chaining returns None")
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

- uses actual value when chaining succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses actual value when chaining succeeds")
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

- chains multiple fallbacks


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains multiple fallbacks")
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

- wraps return value in Option


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps return value in Option")
class Service:
    fn status() -> i64: 200

val service_opt = Some(Service())
val result = service_opt?.status()
# Result is Option<i64>, not i64
expect result == Some(200)
```

</details>

#### preserves complex types through chaining

- preserves complex types through chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves complex types through chaining")
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

- works with collection methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with collection methods")
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

- handles None in collection operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles None in collection operations")
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

- simplifies conditional access patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("simplifies conditional access patterns")
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

- provides defensive programming in data processing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides defensive programming in data processing")
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

- enables safe navigation in unknown data structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables safe navigation in unknown data structures")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a175f3b631dc958fe58ca76a8ac5ef4df47eaa92759679c8a139f4cf257975e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a175f3b631dc958fe58ca76a8ac5ef4df47eaa92759679c8a139f4cf257975e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a175f3b631dc958fe58ca76a8ac5ef4df47eaa92759679c8a139f4cf257975e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/optional_chaining_spec.spl
mirror: doc/06_spec/03_system/feature/usage/optional_chaining_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/optional_chaining_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/optional_chaining_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/optional_chaining_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Some when value is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/optional_chaining_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns None when intermediate value is None' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/optional_chaining_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with deeply nested structures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
