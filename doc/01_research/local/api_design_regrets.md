# API Design Regrets from Major Languages

A compilation of design mistakes, regrets, and lessons learned from Rust, Python, Ruby, Scala, Go, and Java that should inform Simple's stdlib design.

---

## 1. Null References - "The Billion Dollar Mistake"

**Source:** Tony Hoare (inventor of null), [InfoQ 2009](https://www.infoq.com/presentations/Null-References-The-Billion-Dollar-Mistake-Tony-Hoare/)

**The Mistake:**
- Null was added to ALGOL W in 1965 because it was "easy to implement"
- Hoare knew of better solutions (disjoint unions) but took the shortcut
- Led to "innumerable errors, vulnerabilities, and system crashes"

**Simple's Approach:**
- Already uses `Option[T]` - good!
- **Recommendation:** Never add implicit null. `Option[T]` must always be explicit.
- **Recommendation:** Consider `#[deny(implicit_nil)]` as default lint

---

## 2. String Types Complexity

### 2.1 Rust: String vs &str

**Source:** [Rust String/str discussion](https://dx13.co.uk/articles/2024/02/24/rust-string-and-str/)

**The Problem:**
- Two string types confuse newcomers
- Verbose `.to_string()` calls everywhere
- Additional complexity: `OsStr`, `OsString`, `CStr`, `CString`, `Path`, `PathBuf`

**Lessons:**
- Ownership vs borrowing distinction is valuable but adds cognitive load
- API should accept `impl Into<String>` for ergonomics

**Simple's Approach:**
- Consider single `str` type with internal ownership tracking
- **Recommendation:** If multiple string types needed, provide clear guidelines in stdlib docs
- **Recommendation:** Use unit types (`FilePath`, `Url`) instead of bare strings

### 2.2 Python 2→3: Unicode vs Bytes

**Source:** [Armin Ronacher on Python Unicode](https://lucumr.pocoo.org/2014/1/5/unicode-in-2-and-3/)

**The Problem:**
- Python 2 mixed text and bytes silently
- Python 3 fix was correct but broke massive amounts of code
- File streams became confusing (text vs binary modes)

**Lessons:**
- Get string encoding right from the start
- Mixing text and binary should be a compile-time error

**Simple's Approach:**
- `str` = UTF-8 text (always valid)
- `Bytes` = binary data
- **Recommendation:** Never allow implicit conversion between them

---

## 3. Error Handling

### 3.1 Java: Checked Exceptions

**Source:** [Checked Exceptions critique](https://literatejava.com/exceptions/checked-exceptions-javas-biggest-mistake/)

**The Mistake:**
- Checked exceptions seemed good in theory
- In practice: massive boilerplate, cascading signatures
- Modern JVM languages (Kotlin, Scala, Groovy) all rejected them
- Java 8 Streams API abandoned them

**Lessons:**
- Forcing declaration at every call site doesn't improve error handling
- Library designers got the boundary wrong (which exceptions to check)

**Simple's Approach:**
- Use `Result[T, E]` like Rust - good!
- **Recommendation:** Don't require exhaustive error declaration in signatures
- **Recommendation:** Consider effect system for tracking "can fail" vs "pure"

### 3.2 Rust: unwrap() Encourages Panics

**Source:** [unwrap debate](https://www.thecodedmessage.com/posts/2022-07-14-programming-unwrap/)

**The Problem:**
- `unwrap()` makes panicking too easy
- Doesn't indicate possibility of panic in name
- CloudFlare outage linked to unwrap misuse

**Proposed Alternatives:**
- `unwrap_or_panic()` - explicit about behavior
- Only provide `expect(msg)` - forces documentation

**Simple's Approach:**
- **Recommendation:** Name it `unwrap_or_panic()` or only provide `expect(msg)`
- **Recommendation:** Lint warning for `unwrap()` in library code
- **Recommendation:** Consider `try_*` variants returning `Option` instead of panicking

### 3.3 Go: Verbose Error Handling + Nil Interface Pitfall

**Source:** [Go error handling](https://go.dev/blog/error-handling-and-go), [nil interface issues](https://hackernoon.com/go-interfaces-stepping-beyond-the-fundamentals)

**Problems:**
1. `if err != nil` boilerplate tops complaint surveys
2. Nil interface != interface holding nil pointer (subtle bug source)
3. Sentinel errors slow code by 500%

**Simple's Approach:**
- `Result[T, E]` with `?` operator avoids Go's verbosity
- **Recommendation:** Ensure `Option.None` and `nil` are never confused
- **Recommendation:** Consider "not found" as separate return value, not error

---

## 4. Implicit Conversions

### 4.1 Scala: Implicit Conversions

**Source:** [Scala implicit issues](https://soc.me/languages/implicit-numeric-conversions.html)

**The Mistake:**
- Three different uses of `implicit` keyword confused everyone
- Implicit numeric conversions "silently destroy data"
- Debugging implicits was nightmare

**Scala 3 Fix:**
- Split `implicit` into `given`/`using`
- Made dangerous conversions harder to use
- Require explicit import for implicit conversions

**Simple's Approach:**
- **Recommendation:** No implicit type conversions ever
- **Recommendation:** Explicit `.into()` or `.as_*()` for all conversions
- **Recommendation:** If extension methods exist, don't allow them to change types

### 4.2 Numeric Widening

**The Problem (from multiple languages):**
- `int` + `float` = `float` silently loses precision
- Division behavior differs: `5/2` = `2` (int) or `2.5` (float)?

**Simple's Approach:**
- **Recommendation:** Require explicit casts for all numeric conversions
- **Recommendation:** Use separate operators or explicit functions for integer vs float division

---

## 5. Collections API Issues

### 5.1 Scala: Collections Complexity ("Second System Syndrome")

**Source:** [Scala 2.13 Collections Rework](https://www.scala-lang.org/blog/2017/02/28/collections-rework.html)

**Problems:**
- `CanBuildFrom` was too complex
- Immutable operators on mutable collections confused users
- Lazy vs strict collections unclear
- Huge class hierarchy

**Simple's Approach:**
- **Recommendation:** Keep collections hierarchy flat
- **Recommendation:** Clear naming: `Vec` (mutable), `List` (immutable)
- **Recommendation:** Lazy collections should be obviously different type

### 5.2 Python: append() vs extend()

**Source:** [append vs extend confusion](https://www.freecodecamp.org/news/python-list-append-vs-python-list-extend/)

**The Problem:**
- `append([1,2,3])` creates nested list
- `extend([1,2,3])` adds elements
- Strings as iterables make `extend("abc")` add 'a','b','c'

**Simple's Approach:**
- **Recommendation:** Single method with clear semantics
- **Recommendation:** `push(item)` for single, `push_all(items)` for multiple
- **Recommendation:** Or require explicit type: `push(items: &[T])`

### 5.3 Rust: Iterator collect() Turbofish

**Source:** [turbofish discussion](https://techblog.tonsser.com/posts/what-is-rusts-turbofish)

**The Problem:**
- `.collect::<Vec<_>>()` syntax is awkward
- Inconsistent with `.into()` which can't use turbofish
- Type inference often fails

**Simple's Approach:**
- **Recommendation:** Prefer explicit constructors: `Vec.from_iter(iter)`
- **Recommendation:** Or return concrete type from iteration methods

---

## 6. Concurrency Design

### 6.1 Python/Ruby: GIL (Global Interpreter Lock)

**Source:** [Python GIL discussion](https://www.snaplogic.com/blog/an-open-letter-to-guido-van-rossum-mr-rossum-tear-down-that-gil)

**The Mistake:**
- GIL was expedient for single-core era
- Makes true parallelism impossible without multiprocessing
- Removing it would halve single-threaded performance

**Simple's Approach:**
- **Recommendation:** Design for parallelism from day 1
- **Recommendation:** Use actor model or ownership for thread safety
- Already has actors - good!

### 6.2 Async/Await: Function Coloring

**Source:** [Function coloring debate](https://www.thecodedmessage.com/posts/async-colors/)

**The Problem:**
- Async functions can't easily call sync functions and vice versa
- "Viral" nature spreads through codebase
- Go and Zig avoid this with green threads / stackful coroutines

**Counter-argument:**
- Colors reveal important effects (where can code yield?)
- Explicit is better than implicit for systems programming

**Simple's Approach:**
- Simple already has async - consider the tradeoffs
- **Recommendation:** Provide easy sync→async bridge (`block_on`)
- **Recommendation:** Document the coloring explicitly
- **Recommendation:** Consider effect system to track async-ness

---

## 7. Symbol vs String Confusion (Ruby)

**Source:** [Ruby symbols discussion](https://bugs.ruby-lang.org/issues/14277)

**The Problem:**
- `:symbol` vs `"string"` serve different purposes but often confused
- Hash keys: `hash[:key]` vs `hash["key"]` - which to use?
- JSON serialization loses symbol/string distinction
- `HashWithIndifferentAccess` was a bandaid

**Simple's Approach:**
- **Recommendation:** Don't have separate symbol type
- **Recommendation:** Use string interning internally for performance
- **Recommendation:** Or make symbols clearly different (like Erlang atoms)

---

## 8. Mutability Defaults

### 8.1 Most Languages: Mutable by Default

**The Problem:**
- Most bugs come from unexpected mutation
- Harder to reason about code
- Concurrency issues

**Simple's Approach:**
- Already has `#[immutable]` attribute - good!
- **Recommendation:** Consider immutable-by-default for core modules
- **Recommendation:** GPU/baremetal already use immutable - extend to more areas

---

## 9. Standard Library Scope

### 9.1 Rust: Minimal stdlib

**Source:** [Rust stdlib criticism](https://medium.com/@afreechameleon/rusts-stdlib-is-terrible-and-we-need-better-1e63d4430bf)

**Criticism:**
- No built-in async runtime
- Can't save structs to files
- HTTP client requires external crate

**Counter-argument:**
- Allows ecosystem to evolve
- Avoids blessing one implementation

### 9.2 Ruby: stdlib Quality Issues

**Source:** [Ruby stdlib criticism](https://news.ycombinator.com/item?id=1931202)

**Problems:**
- "Stdlib is a ghetto" - inconsistent quality
- Net::HTTP docs broken for years
- Solution: gemify everything (modular stdlib)

**Simple's Approach:**
- **Recommendation:** Clear quality bar for stdlib inclusion
- **Recommendation:** Modular stdlib (core vs extended)
- **Recommendation:** Good documentation from day 1

---

## 10. API Naming Conventions

### 10.1 Inconsistent Method Names

**Common Problems:**
- `size` vs `length` vs `count` vs `len`
- `remove` vs `delete` vs `drop`
- `find` vs `search` vs `lookup`

**Simple's Approach:**
- **Recommendation:** Pick one term per concept, document in style guide
- Suggested vocabulary:
  - Size/length: `len()` (always)
  - Remove element: `remove()` (returns removed), `delete()` (returns success)
  - Find: `find()` (returns Option), `get()` (may panic)
  - Check existence: `contains()` (bool), `has()` (avoid - ambiguous)

### 10.2 Mutable vs Immutable Method Naming

**Best Practice (already in Simple's doc):**
| Operation | Mutable | Immutable |
|-----------|---------|-----------|
| Sort | `sort()` | `sorted()` |
| Reverse | `reverse()` | `reversed()` |
| Filter | `filter()` | `filtered()` |
| Update | `set(i, v)` | `with(i, v)` |

---

## Summary: Top Recommendations for Simple

### Must Have (Critical)
1. No implicit null - `Option[T]` always explicit
2. No implicit type conversions
3. Clear text vs binary distinction (`str` vs `Bytes`)
4. `Result[T, E]` with `?` operator (already done)
5. Explicit numeric conversions

### Should Have (Important)
6. Rename `unwrap()` to `expect(msg)` or `unwrap_or_panic()`
7. Single string type (not String/str split)
8. Consistent method naming vocabulary
9. Flat collections hierarchy
10. Immutable-by-default where sensible

### Nice to Have (Future)
11. Effect system for tracking async/errors
12. Modular stdlib (core + extended)
13. Built-in async runtime in stdlib
14. String interning for identifier performance

---

## Sources

- [Tony Hoare: Null - The Billion Dollar Mistake](https://www.infoq.com/presentations/Null-References-The-Billion-Dollar-Mistake-Tony-Hoare/)
- [Rust String vs str](https://dx13.co.uk/articles/2024/02/24/rust-string-and-str/)
- [Python Unicode in 2 and 3](https://lucumr.pocoo.org/2014/1/5/unicode-in-2-and-3/)
- [Java Checked Exceptions Mistake](https://literatejava.com/exceptions/checked-exceptions-javas-biggest-mistake/)
- [Rust unwrap debate](https://www.thecodedmessage.com/posts/2022-07-14-programming-unwrap/)
- [Go Error Handling](https://go.dev/blog/error-handling-and-go)
- [Scala Implicit Conversions](https://soc.me/languages/implicit-numeric-conversions.html)
- [Scala 2.13 Collections Rework](https://www.scala-lang.org/blog/2017/02/28/collections-rework.html)
- [Rust Async Function Colors](https://www.thecodedmessage.com/posts/async-colors/)
- [Ruby Symbols vs Strings](https://bugs.ruby-lang.org/issues/14277)
- [Python Regrets - Guido van Rossum](https://legacy.python.org/doc/essays/ppt/regrets/PythonRegrets.pdf)
- [Ruby Stdlib Criticism](https://news.ycombinator.com/item?id=1931202)
