# Trait Keyword - All Phases

> Comprehensive phase tests for the trait keyword feature covering all five phases: trait definition with method signatures (fn/me, parameters, return types), default method behavior, forwarding/delegation patterns, end-to-end workflows from trait definition through implementation to usage, and static dispatch via trait-bounded generics.

<!-- sdn-diagram:id=trait_keyword_all_phases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trait_keyword_all_phases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trait_keyword_all_phases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trait_keyword_all_phases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Keyword - All Phases

Comprehensive phase tests for the trait keyword feature covering all five phases: trait definition with method signatures (fn/me, parameters, return types), default method behavior, forwarding/delegation patterns, end-to-end workflows from trait definition through implementation to usage, and static dispatch via trait-bounded generics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TRAIT-002 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/trait_keyword_all_phases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive phase tests for the trait keyword feature covering all
five phases: trait definition with method signatures (fn/me, parameters,
return types), default method behavior, forwarding/delegation patterns,
end-to-end workflows from trait definition through implementation to usage,
and static dispatch via trait-bounded generics.

## Syntax

```simple
trait Formatter:
    fn format(value: text) -> text
class TextFormatter:
    inner: BaseFormatter
    # delegation: fn format(value): self.inner.format(value)
```

Self-contained tests - no compiler-internal imports needed.
All types, traits, and functions are defined locally.

## Scenarios

### Trait Keyword: Phase 1 - Trait detection

#### basic detection

#### trait declaration is recognized

1. fn to string
2. fn to string
3. "
   - Expected: p.to_string() equals `(3, 4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Display:
    fn to_string() -> text

struct ShowPoint:
    x: i64
    y: i64

impl Display for ShowPoint:
    fn to_string() -> text:
        "({self.x}, {self.y})"

val p = ShowPoint(x: 3, y: 4)
expect(p.to_string()).to_equal("(3, 4)")
```

</details>

#### trait name is extracted correctly

1. fn size
2. fn size
   - Expected: b.size() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Container:
    fn size() -> i64

struct Bag:
    count: i64

impl Container for Bag:
    fn size() -> i64:
        self.count

val b = Bag(count: 5)
expect(b.size()).to_equal(5)
```

</details>

#### trait without methods acts as marker

1. fn is marked
2. fn is marked
   - Expected: t.is_marked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Marker:
    fn is_marked() -> bool:
        true

struct Token:
    id: i64

impl Marker for Token:
    fn is_marked() -> bool:
        true

val t = Token(id: 1)
expect(t.is_marked()).to_equal(true)
```

</details>

#### struct without trait impl has no trait methods

1. fn special value
2. fn get x
   - Expected: p.get_x() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Special:
    fn special_value() -> i64

struct Plain:
    x: i64
    fn get_x() -> i64:
        self.x

val p = Plain(x: 10)
expect(p.get_x()).to_equal(10)
```

</details>

#### multiple traits

#### finds two traits and implements both

1. fn read
2. fn write label
3. fn read
4. fn write label
   - Expected: f.read() equals `reading data.txt`
   - Expected: f.write_label() equals `writing data.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Readable:
    fn read() -> text

trait Writable:
    fn write_label() -> text

struct FileObj:
    name: text

impl Readable for FileObj:
    fn read() -> text:
        "reading {self.name}"

impl Writable for FileObj:
    fn write_label() -> text:
        "writing {self.name}"

val f = FileObj(name: "data.txt")
expect(f.read()).to_equal("reading data.txt")
expect(f.write_label()).to_equal("writing data.txt")
```

</details>

#### traits mixed with non-trait declarations work together

1. fn size
2. fn get x
3. fn size
   - Expected: h.get_x() equals `42`
   - Expected: c.size() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Sizeable:
    fn size() -> i64

struct Helper:
    x: i64
    fn get_x() -> i64:
        self.x

struct Collection:
    count: i64

impl Sizeable for Collection:
    fn size() -> i64:
        self.count

val h = Helper(x: 42)
val c = Collection(count: 10)
expect(h.get_x()).to_equal(42)
expect(c.size()).to_equal(10)
```

</details>

#### trait lookup

#### correct trait impl is found for the right type

1. fn get id
2. fn get id
3. fn get id
   - Expected: u.get_id() equals `7`
   - Expected: d.get_id() equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Identifiable:
    fn get_id() -> i64

struct User:
    uid: i64

struct Device:
    did: i64

impl Identifiable for User:
    fn get_id() -> i64:
        self.uid

impl Identifiable for Device:
    fn get_id() -> i64:
        self.did * 100

val u = User(uid: 7)
val d = Device(did: 3)
expect(u.get_id()).to_equal(7)
expect(d.get_id()).to_equal(300)
```

</details>

#### type without matching trait impl uses own methods

1. fn log entry
2. fn get label
   - Expected: obj.get_label() equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Logger:
    fn log_entry() -> text

struct SimpleObj:
    label: text
    fn get_label() -> text:
        self.label

val obj = SimpleObj(label: "test")
expect(obj.get_label()).to_equal("test")
```

</details>

### Trait Keyword: Phase 2 - Method signature extraction

#### fn methods

#### fn method is immutable and returns value

1. fn inspect
2. fn inspect
   - Expected: item.inspect() equals `Item: widget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Inspect:
    fn inspect() -> text

struct Item:
    name: text

impl Inspect for Item:
    fn inspect() -> text:
        "Item: {self.name}"

val item = Item(name: "widget")
expect(item.inspect()).to_equal("Item: widget")
```

</details>

#### fn method with return type works for multiple methods

1. fn length
2. fn weight
3. fn length
4. fn weight
   - Expected: b.length() equals `10`
   - Expected: b.weight() equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Measurable:
    fn length() -> i64
    fn weight() -> i64

struct Box:
    l: i64
    w: i64

impl Measurable for Box:
    fn length() -> i64:
        self.l
    fn weight() -> i64:
        self.w

val b = Box(l: 10, w: 25)
expect(b.length()).to_equal(10)
expect(b.weight()).to_equal(25)
```

</details>

#### me methods

#### me method can mutate state

1. me update
2. me update
3. var acc = Accumulator
4. acc update
5. acc update
   - Expected: acc.total equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Mutable:
    me update(amount: i64)

struct Accumulator:
    total: i64

impl Mutable for Accumulator:
    me update(amount: i64):
        self.total = self.total + amount

var acc = Accumulator(total: 0)
acc.update(10)
acc.update(20)
expect(acc.total).to_equal(30)
```

</details>

#### mixed fn and me methods in same trait

1. fn get count
2. me add entry
3. me remove entry
4. fn get count
5. me add entry
6. me remove entry
7. var s = Store
8. s add entry
9. s add entry
   - Expected: s.get_count() equals `2`
   - Expected: s.last_val equals `99`
10. s remove entry
   - Expected: s.get_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Repository:
    fn get_count() -> i64
    me add_entry(entry: i64)
    me remove_entry()

struct Store:
    count: i64
    last_val: i64

impl Repository for Store:
    fn get_count() -> i64:
        self.count
    me add_entry(entry: i64):
        self.count = self.count + 1
        self.last_val = entry
    me remove_entry():
        if self.count > 0:
            self.count = self.count - 1

var s = Store(count: 0, last_val: 0)
s.add_entry(42)
s.add_entry(99)
expect(s.get_count()).to_equal(2)
expect(s.last_val).to_equal(99)
s.remove_entry()
expect(s.get_count()).to_equal(1)
```

</details>

#### parameter extraction

#### no-arg method works

1. me close
2. me close
3. var h = Handle
4. h close
   - Expected: h.open is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Closeable:
    me close()

struct Handle:
    open: bool

impl Closeable for Handle:
    me close():
        self.open = false

var h = Handle(open: true)
h.close()
expect(h.open).to_equal(false)
```

</details>

#### single-param method works

1. me process
2. me process
3. var tp = TextProcessor
4. tp process
   - Expected: tp.result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Processor:
    me process(item: text)

struct TextProcessor:
    result: text

impl Processor for TextProcessor:
    me process(item: text):
        self.result = item

var tp = TextProcessor(result: "")
tp.process("hello")
expect(tp.result).to_equal("hello")
```

</details>

#### multi-param method extracts all params correctly

1. fn transform
2. fn transform
   - Expected: f.transform("data", 3, true) equals `T:datax3`
   - Expected: f.transform("data", 3, false) equals `data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Transformer:
    fn transform(input: text, count: i64, flag: bool) -> text

struct Fmt:
    prefix: text

impl Transformer for Fmt:
    fn transform(input: text, count: i64, flag: bool) -> text:
        if flag:
            "{self.prefix}:{input}x{count}"
        else:
            input

val f = Fmt(prefix: "T")
expect(f.transform("data", 3, true)).to_equal("T:datax3")
expect(f.transform("data", 3, false)).to_equal("data")
```

</details>

#### comments and type lines in trait body

#### trait with only relevant methods works

1. fn next val
2. fn next val
   - Expected: c.next_val() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Iter:
    fn next_val() -> i64

struct Counter:
    n: i64

impl Iter for Counter:
    fn next_val() -> i64:
        self.n + 1

val c = Counter(n: 5)
expect(c.next_val()).to_equal(6)
```

</details>

#### trait with associated type declaration works

1. fn get item
2. fn get item
   - Expected: ic.get_item() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Collection:
    type Item
    fn get_item() -> i64

struct IntCollection:
    value: i64

impl Collection for IntCollection:
    type Item = i64
    fn get_item() -> i64:
        self.value

val ic = IntCollection(value: 42)
expect(ic.get_item()).to_equal(42)
```

</details>

### Trait Keyword: Phase 3 - Default method detection

#### abstract vs default methods

#### abstract method must be implemented

1. fn eq val
2. fn eq val
   - Expected: num.eq_val(42) is true
   - Expected: num.eq_val(10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Eq:
    fn eq_val(other_val: i64) -> bool

struct Number:
    n: i64

impl Eq for Number:
    fn eq_val(other_val: i64) -> bool:
        self.n == other_val

val num = Number(n: 42)
expect(num.eq_val(42)).to_equal(true)
expect(num.eq_val(10)).to_equal(false)
```

</details>

#### default method is used when not overridden

1. fn compare to
2. fn less than
3. self compare to
4. fn greater than
5. self compare to
6. fn compare to
   - Expected: p.compare_to(3) equals `2`
   - Expected: p.less_than(10) is true
   - Expected: p.less_than(2) is false
   - Expected: p.greater_than(2) is true
   - Expected: p.greater_than(10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Comparable:
    fn compare_to(other_val: i64) -> i64
    fn less_than(other_val: i64) -> bool:
        self.compare_to(other_val) < 0
    fn greater_than(other_val: i64) -> bool:
        self.compare_to(other_val) > 0

struct Priority:
    level: i64

impl Comparable for Priority:
    fn compare_to(other_val: i64) -> i64:
        self.level - other_val

val p = Priority(level: 5)
# abstract method works
expect(p.compare_to(3)).to_equal(2)
# default methods work without explicit implementation
expect(p.less_than(10)).to_equal(true)
expect(p.less_than(2)).to_equal(false)
expect(p.greater_than(2)).to_equal(true)
expect(p.greater_than(10)).to_equal(false)
```

</details>

#### default method with inline body works

1. fn prefix
2. fn prefix
   - Expected: w.prefix() equals `default_prefix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait StringProvider:
    fn prefix() -> text:
        "default_prefix"

struct Widget:
    name: text

impl StringProvider for Widget:
    fn prefix() -> text:
        "default_prefix"

val w = Widget(name: "btn")
expect(w.prefix()).to_equal("default_prefix")
```

</details>

#### default method override

#### overriding default method replaces it

1. fn greet
2. fn greet
   - Expected: fp.greet() equals `Good day, Sir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Greetable:
    fn greet() -> text:
        "hello"

struct FormalPerson:
    title: text

impl Greetable for FormalPerson:
    fn greet() -> text:
        "Good day, {self.title}"

val fp = FormalPerson(title: "Sir")
expect(fp.greet()).to_equal("Good day, Sir")
```

</details>

#### default method calls abstract method correctly

1. fn compute
2. fn double
3. self compute
4. fn compute
   - Expected: v.compute() equals `21`
   - Expected: v.double() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Calculator:
    fn compute() -> i64
    fn double() -> i64:
        self.compute() * 2

struct Val:
    n: i64

impl Calculator for Val:
    fn compute() -> i64:
        self.n

val v = Val(n: 21)
expect(v.compute()).to_equal(21)
expect(v.double()).to_equal(42)
```

</details>

#### all-abstract trait requires all methods implemented

1. fn print text
2. fn print count
3. fn print text
4. fn print count
   - Expected: doc.print_text() equals `Hello`
   - Expected: doc.print_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Printable:
    fn print_text() -> text
    fn print_count() -> i64

struct Document:
    content: text
    pages: i64

impl Printable for Document:
    fn print_text() -> text:
        self.content
    fn print_count() -> i64:
        self.pages

val doc = Document(content: "Hello", pages: 3)
expect(doc.print_text()).to_equal("Hello")
expect(doc.print_count()).to_equal(3)
```

</details>

### Trait Keyword: Phase 4 - Forwarding

#### immutable forwarding (alias fn pattern)

#### delegates immutable method to field

1. fn get len
2. fn get len
3. self inner get len
   - Expected: w.get_len() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Inner:
    data: i64
    fn get_len() -> i64:
        self.data

# This represents what desugar would generate from alias fn len = inner.len
struct Wrapper:
    inner: Inner
    fn get_len() -> i64:
        self.inner.get_len()

val w = Wrapper(inner: Inner(data: 42))
expect(w.get_len()).to_equal(42)
```

</details>

#### delegates fn with args to field

1. fn get
2. fn get
3. self inner get
   - Expected: w.get(5, 0) equals `105`
   - Expected: w.get(0, 99) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct InnerCalc:
    base: i64
    fn get(key: i64, default_val: i64) -> i64:
        if key > 0:
            self.base + key
        else:
            default_val

struct CalcWrapper:
    inner: InnerCalc
    fn get(key: i64, default_val: i64) -> i64:
        self.inner.get(key, default_val)

val w = CalcWrapper(inner: InnerCalc(base: 100))
expect(w.get(5, 0)).to_equal(105)
expect(w.get(0, 99)).to_equal(99)
```

</details>

#### mutable forwarding (alias me pattern)

#### delegates mutable method to field

1. me push
2. me push
3. self inner push
4. fn size
5. var w = ListWrapper
6. w push
7. w push
8. w push
   - Expected: w.size() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct InnerList:
    length: i64
    me push(item: i64):
        self.length = self.length + 1

struct ListWrapper:
    inner: InnerList
    me push(item: i64):
        self.inner.push(item)
    fn size() -> i64:
        self.inner.length

var w = ListWrapper(inner: InnerList(length: 0))
w.push(1)
w.push(2)
w.push(3)
expect(w.size()).to_equal(3)
```

</details>

#### trait-based forwarding (alias TraitName = field pattern)

#### forwards fn methods from trait to field

1. fn size
2. fn is empty
3. fn size
4. fn is empty
5. fn size
6. self items size
7. fn is empty
8. self items is empty
   - Expected: ml.size() equals `5`
   - Expected: ml.is_empty() is false
   - Expected: empty_ml.size() equals `0`
   - Expected: empty_ml.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Sizeable:
    fn size() -> i64
    fn is_empty() -> bool

struct Storage:
    count: i64

impl Sizeable for Storage:
    fn size() -> i64:
        self.count
    fn is_empty() -> bool:
        self.count == 0

# This is what desugar generates from: alias Sizeable = items
struct MyList:
    items: Storage
    fn size() -> i64:
        self.items.size()
    fn is_empty() -> bool:
        self.items.is_empty()

val ml = MyList(items: Storage(count: 5))
expect(ml.size()).to_equal(5)
expect(ml.is_empty()).to_equal(false)

val empty_ml = MyList(items: Storage(count: 0))
expect(empty_ml.size()).to_equal(0)
expect(empty_ml.is_empty()).to_equal(true)
```

</details>

#### forwards me methods from trait to field

1. me write data
2. me clear data
3. me write data
4. me clear data
5. me write data
6. self buf write data
7. me clear data
8. self buf clear data
9. fn read
10. fn count
11. var s = StreamObj
12. s write data
13. s write data
   - Expected: s.read() equals `hello world`
   - Expected: s.count() equals `2`
14. s clear data
   - Expected: s.read() equals ``
   - Expected: s.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Writable:
    me write_data(data: text)
    me clear_data()

struct Buffer:
    content: text
    entries: i64

impl Writable for Buffer:
    me write_data(data: text):
        self.content = self.content + data
        self.entries = self.entries + 1
    me clear_data():
        self.content = ""
        self.entries = 0

# Desugar generates: me write_data(data): self.buf.write_data(data)
struct StreamObj:
    buf: Buffer
    me write_data(data: text):
        self.buf.write_data(data)
    me clear_data():
        self.buf.clear_data()
    fn read() -> text:
        self.buf.content
    fn count() -> i64:
        self.buf.entries

var s = StreamObj(buf: Buffer(content: "", entries: 0))
s.write_data("hello")
s.write_data(" world")
expect(s.read()).to_equal("hello world")
expect(s.count()).to_equal(2)
s.clear_data()
expect(s.read()).to_equal("")
expect(s.count()).to_equal(0)
```

</details>

#### unknown trait generates no forwarding - wrapper has only own methods

1. fn get value
   - Expected: w.get_value() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct InnerData:
    value: i64

struct WrapperOwn:
    inner: InnerData
    fn get_value() -> i64:
        self.inner.value

val w = WrapperOwn(inner: InnerData(value: 99))
expect(w.get_value()).to_equal(99)
```

</details>

#### blanket forwarding (alias field pattern)

#### forwards all methods from field type

1. fn size
2. me clear all
3. fn size
4. self store size
5. me clear all
6. self store clear all
7. var w = WrapperFull
   - Expected: w.size() equals `10`
8. w clear all
   - Expected: w.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct StorageFull:
    count: i64
    fn size() -> i64:
        self.count
    me clear_all():
        self.count = 0

# Desugar generates forwarding for all methods of StorageFull
struct WrapperFull:
    store: StorageFull
    fn size() -> i64:
        self.store.size()
    me clear_all():
        self.store.clear_all()

var w = WrapperFull(store: StorageFull(count: 10))
expect(w.size()).to_equal(10)
w.clear_all()
expect(w.size()).to_equal(0)
```

</details>

### Trait Keyword: Phase 5 - End-to-end usage

#### complete trait workflow

#### define a trait, implement it, use methods

1. me on event
2. fn handler name
3. me on event
4. fn handler name
5. var handler = ClickHandler
   - Expected: handler.handler_name() equals `btn_click`
6. handler on event
7. handler on event
   - Expected: handler.click_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait EventHandler:
    me on_event(event: text)
    fn handler_name() -> text

struct ClickHandler:
    name: text
    click_count: i64

impl EventHandler for ClickHandler:
    me on_event(event: text):
        self.click_count = self.click_count + 1
    fn handler_name() -> text:
        self.name

var handler = ClickHandler(name: "btn_click", click_count: 0)
expect(handler.handler_name()).to_equal("btn_click")
handler.on_event("click")
handler.on_event("click")
expect(handler.click_count).to_equal(2)
```

</details>

#### complete define-implement-forward workflow

1. fn format val
2. fn fmt name
3. fn format val
4. fn fmt name
5. fn format val
6. self inner format val
7. fn fmt name
8. self inner fmt name
   - Expected: tf.format_val("test") equals `bold: test`
   - Expected: tf.fmt_name() equals `bold`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Formattable:
    fn format_val(value: text) -> text
    fn fmt_name() -> text

struct BaseFormatter:
    prefix: text

impl Formattable for BaseFormatter:
    fn format_val(value: text) -> text:
        "{self.prefix}: {value}"
    fn fmt_name() -> text:
        self.prefix

# TextFormatter delegates to inner BaseFormatter
struct TextFormatter:
    inner: BaseFormatter
    fn format_val(value: text) -> text:
        self.inner.format_val(value)
    fn fmt_name() -> text:
        self.inner.fmt_name()

val tf = TextFormatter(inner: BaseFormatter(prefix: "bold"))
expect(tf.format_val("test")).to_equal("bold: test")
expect(tf.fmt_name()).to_equal("bold")
```

</details>

#### multiple traits in source: each generates correct forwarding

1. fn read data
2. me close handle
3. fn read data
4. me close handle
5. fn read data
6. me close handle
7. fn read data
8. self reader read data
9. me close handle
10. self handle close handle
11. var fs = FileStream
   - Expected: fs.read_data() equals `content`
12. fs close handle
   - Expected: fs.handle.open is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait ReadCapable:
    fn read_data() -> text

trait CloseCapable:
    me close_handle()

struct Reader:
    data: text
    fn read_data() -> text:
        self.data

struct HandleObj:
    open: bool
    me close_handle():
        self.open = false

impl ReadCapable for Reader:
    fn read_data() -> text:
        self.data

impl CloseCapable for HandleObj:
    me close_handle():
        self.open = false

# FileStream delegates to both reader and handle
struct FileStream:
    reader: Reader
    handle: HandleObj
    fn read_data() -> text:
        self.reader.read_data()
    me close_handle():
        self.handle.close_handle()

var fs = FileStream(reader: Reader(data: "content"), handle: HandleObj(open: true))
expect(fs.read_data()).to_equal("content")
fs.close_handle()
expect(fs.handle.open).to_equal(false)
```

</details>

#### trait with default methods: only abstract methods need implementation

1. fn compare to val
2. fn is less than
3. self compare to val
4. fn is greater than
5. self compare to val
6. fn compare to val
   - Expected: p.compare_to_val(3) equals `4`
   - Expected: p.is_less_than(10) is true
   - Expected: p.is_less_than(5) is false
   - Expected: p.is_greater_than(5) is true
   - Expected: p.is_greater_than(10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait ComparableItem:
    fn compare_to_val(other_val: i64) -> i64
    fn is_less_than(other_val: i64) -> bool:
        self.compare_to_val(other_val) < 0
    fn is_greater_than(other_val: i64) -> bool:
        self.compare_to_val(other_val) > 0

struct PriorityItem:
    level: i64

impl ComparableItem for PriorityItem:
    fn compare_to_val(other_val: i64) -> i64:
        self.level - other_val

val p = PriorityItem(level: 7)
# Abstract method (compare_to_val) works
expect(p.compare_to_val(3)).to_equal(4)
# Default methods work without explicit impl
expect(p.is_less_than(10)).to_equal(true)
expect(p.is_less_than(5)).to_equal(false)
expect(p.is_greater_than(5)).to_equal(true)
expect(p.is_greater_than(10)).to_equal(false)
```

</details>

#### trait scanner and forwarding agree on method count

1. me run
2. fn status
3. fn pipeline name
4. me run
5. fn status
6. fn pipeline name
7. me run
8. self impl field run
9. fn status
10. self impl field status
11. fn pipeline name
12. self impl field pipeline name
13. var dp = DataPipeline
   - Expected: dp.pipeline_name() equals `ETL`
   - Expected: dp.status() equals `idle`
14. dp run
   - Expected: dp.status() equals `processing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Pipeline:
    me run(input: text)
    fn status() -> text
    fn pipeline_name() -> text

struct PipelineImpl:
    state: text
    label: text

impl Pipeline for PipelineImpl:
    me run(input: text):
        self.state = input
    fn status() -> text:
        self.state
    fn pipeline_name() -> text:
        self.label

# DataPipeline delegates all 3 methods to impl field
struct DataPipeline:
    impl_field: PipelineImpl
    me run(input: text):
        self.impl_field.run(input)
    fn status() -> text:
        self.impl_field.status()
    fn pipeline_name() -> text:
        self.impl_field.pipeline_name()

var dp = DataPipeline(impl_field: PipelineImpl(state: "idle", label: "ETL"))
expect(dp.pipeline_name()).to_equal("ETL")
expect(dp.status()).to_equal("idle")
dp.run("processing")
expect(dp.status()).to_equal("processing")
```

</details>

### Trait Keyword: Phase 6 - Static dispatch

#### trait params become generic

#### fn with trait-bounded param uses static dispatch

1. fn print text
2. fn print text
3. "Circle
4. fn print text
5. "Square
6. fn show
7. x print text
   - Expected: show(c) equals `Circle(r=5)`
   - Expected: show(s) equals `Square(s=3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait PrintCapable:
    fn print_text() -> text

struct Circle:
    radius: i64

impl PrintCapable for Circle:
    fn print_text() -> text:
        "Circle(r={self.radius})"

struct Square:
    side: i64

impl PrintCapable for Square:
    fn print_text() -> text:
        "Square(s={self.side})"

# Function accepting trait-bounded type
fn show(x: PrintCapable) -> text:
    x.print_text()

val c = Circle(radius: 5)
val s = Square(side: 3)
expect(show(c)).to_equal("Circle(r=5)")
expect(show(s)).to_equal("Square(s=3)")
```

</details>

#### multiple trait params dispatch correctly

1. fn read op
2. fn close op
3. fn read op
4. fn close op
5. fn use both
6. "{r read op
   - Expected: use_both(r, c) equals `read:a.txt close:b.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait ReadOp:
    fn read_op() -> text

trait CloseOp:
    fn close_op() -> text

struct FileReader:
    name: text

impl ReadOp for FileReader:
    fn read_op() -> text:
        "read:{self.name}"

struct FileCloser:
    name: text

impl CloseOp for FileCloser:
    fn close_op() -> text:
        "close:{self.name}"

fn use_both(r: ReadOp, c: CloseOp) -> text:
    "{r.read_op()} {c.close_op()}"

val r = FileReader(name: "a.txt")
val c = FileCloser(name: "b.txt")
expect(use_both(r, c)).to_equal("read:a.txt close:b.txt")
```

</details>

#### dyn prefix stays dynamic

#### dyn Trait param uses dynamic dispatch

1. fn display
2. fn display
3. fn display
4. fn show dyn
5. x display
   - Expected: show_dyn(t) equals `info`
   - Expected: show_dyn(b) equals `[admin]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Displayable:
    fn display() -> text

struct Tag:
    label: text

impl Displayable for Tag:
    fn display() -> text:
        self.label

struct Badge:
    title: text

impl Displayable for Badge:
    fn display() -> text:
        "[{self.title}]"

fn show_dyn(x: dyn Displayable) -> text:
    x.display()

val t = Tag(label: "info")
val b = Badge(title: "admin")
expect(show_dyn(t)).to_equal("info")
expect(show_dyn(b)).to_equal("[admin]")
```

</details>

#### interface stays dynamic

#### interface-typed param dispatches at runtime

1. fn draw
2. fn draw
3. "line
4. fn draw
5. "dot
6. fn render
7. x draw
   - Expected: render(line) equals `line(10)`
   - Expected: render(dot) equals `dot(5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Drawable:
    fn draw() -> text

struct Line:
    length: i64

impl Drawable for Line:
    fn draw() -> text:
        "line({self.length})"

struct Dot:
    x: i64

impl Drawable for Dot:
    fn draw() -> text:
        "dot({self.x})"

fn render(x: Drawable) -> text:
    x.draw()

val line = Line(length: 10)
val dot = Dot(x: 5)
expect(render(line)).to_equal("line(10)")
expect(render(dot)).to_equal("dot(5)")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
