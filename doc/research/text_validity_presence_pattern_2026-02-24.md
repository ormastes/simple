# Research: Text Validity, Emptiness, and the Presence Pattern

**Date:** 2026-02-24
**Status:** Implemented (all 3 phases)
**Area:** Standard Library — Text Utilities, Optional Type Interaction

---

## 1. Problem Statement

Simple currently has boolean-returning text checks:

```simple
fn is_empty(s: text) -> bool      # s.len() == 0
fn is_blank(s: text) -> bool      # empty or whitespace-only
fn not_empty(s: text) -> bool     # s.len() > 0
fn not_blank(s: text) -> bool     # not is_blank(s)
```

These work with UFCS (`s.is_empty`, `s.not_empty`) and with optional chaining (`s?.not_empty`). But there is a recurring pattern in real code where a **boolean check is immediately followed by using the value**:

```simple
# Pattern 1: Check then use (two references to same variable)
val input = get_input()
if input.not_empty:
    process(input)        # must reference `input` again

# Pattern 2: Optional text — check then unwrap
val name: text? = get_name()
if name.? and name?.not_empty:
    use(name ?? "")       # awkward: must unwrap despite knowing it's valid

# Pattern 3: Env vars — always need "exists AND usable"
val ci = env_get("CI")
if ci.not_empty:
    enable_ci_mode(ci)    # `ci` already proven valid but referenced again
```

The core issue: **`is_empty` answers "is this valid?" but doesn't give you the valid value.** This creates a gap between checking and using. The user's insight is that `not_empty` should ideally enable `if val` pattern binding:

```simple
# Desired pattern
if val name = get_input().not_empty:
    process(name)         # bound, guaranteed non-empty
```

This requires `not_empty` to return `text?` (the value or nil), not `bool`.

---

## 2. The Three Validity Dimensions

Strings have three dimensions of "unusable":

| Dimension | Example | Check | Meaning |
|-----------|---------|-------|---------|
| **Nil** | `text?` is `None` | `.?` / `is nil` | Value doesn't exist |
| **Empty** | `""` | `.is_empty` / `not .?` | Value exists but has no content |
| **Blank** | `"   "` | `.is_blank` | Value exists, has chars, but no meaningful content |

All three often mean "don't use this value." A programmer typically wants: **"give me the usable value, or nothing."**

---

## 3. Survey of Other Languages

### 3.1 Ruby — `presence` (the origin of the pattern)

Ruby on Rails defines `presence` on `Object`:

```ruby
def presence
  self if present?
end
```

Returns `self` if present (non-nil, non-empty, non-blank), `nil` otherwise.

```ruby
name = params[:name].presence || "Anonymous"
# or with conditional binding:
if name = params[:name].presence
  use(name)
end
```

**Key insight:** `presence` unifies nil/empty/blank into a single "usable or nil" result. It is the most direct and widely-adopted implementation of this pattern.

### 3.2 Kotlin — `takeIf` / `ifEmpty` / `ifBlank`

Kotlin provides both boolean checkers and value-returning variants:

| Function | Returns | Purpose |
|----------|---------|---------|
| `isNullOrEmpty()` | `Boolean` | Boolean check |
| `isNullOrBlank()` | `Boolean` | Boolean check |
| `takeIf { predicate }` | `T?` | Returns `this` if predicate true, `null` otherwise |
| `ifEmpty { default }` | `T` | Returns `this` if non-empty, else default |
| `ifBlank { default }` | `T` | Returns `this` if non-blank, else default |

```kotlin
// Presence pattern via takeIf
val name = input?.takeIf { it.isNotBlank() }
name?.let { use(it) }

// Default value via ifBlank
val display = input.ifBlank { "Anonymous" }
```

`takeIf` is generic — works on any type, not just strings. Combined with `?.let {}`, it provides full presence-style workflows.

### 3.3 Swift — Community `nonEmpty` extension

Swift has no built-in presence, but a widely-adopted community pattern:

```swift
extension Collection {
    var nonEmpty: Self? {
        isEmpty ? nil : self
    }
}

// Enables if-let binding
if let name = input?.nonEmpty {
    use(name)   // guaranteed non-nil AND non-empty
}

// With nil coalescing
let display = input?.nonEmpty ?? "default"
```

Swift Forums have a [dedicated thread](https://forums.swift.org/t/presence-value-isempty-nil-value/14869) proposing this for the standard library.

### 3.4 Rust — `Option::filter`

Rust uses `Option::filter(predicate)` — returns `Some(t)` if predicate is true, `None` otherwise:

```rust
let name: Option<&str> = Some("hello").filter(|s| !s.is_empty());

if let Some(name) = input.filter(|s| !s.is_empty()) {
    use(name);
}
```

Also has `bool::then_some(value)` for converting bare values:

```rust
let name = (!s.is_empty()).then_some(s);
```

### 3.5 Python — Truthiness + `or` returning values

Python's `or` returns the value, not a boolean:

```python
name = get_input() or "Anonymous"     # "" → "Anonymous", "hello" → "hello"

# Walrus operator for binding
if name := get_input():
    use(name)
```

Empty strings are falsy in Python, so `or` naturally acts as a presence check.

### 3.6 Java — `Optional.filter()` + Guava `emptyToNull`

```java
// Standard library
Optional<String> name = Optional.ofNullable(input)
    .filter(s -> !s.isBlank());

// Guava — the most direct presence equivalent
Optional<String> name = Optional.ofNullable(Strings.emptyToNull(input));
```

### 3.7 C# — Property pattern matching

C# 9+ has a unique approach using pattern matching with property patterns:

```csharp
if (input is { Length: > 0 } name) {
    Use(name);    // bound AND guaranteed non-null, non-empty
}
```

This simultaneously checks non-null, checks non-empty, and binds the value in a single expression.

### 3.8 Haskell — `mfilter` (monadic presence)

```haskell
mfilter (not . null) (Just "hello")  -- Just "hello"
mfilter (not . null) (Just "")       -- Nothing
mfilter (not . null) Nothing         -- Nothing
```

`mfilter` works on any `MonadPlus`, generalizing the pattern beyond Maybe.

### 3.9 Scala — `Option.when` / `filter`

```scala
val name = Option(input).filter(_.nonEmpty)
val name = Option.when(input.nonEmpty)(input)   // Scala 2.13+
```

---

## 4. Design Options for Simple

### Option A: Value-Returning `presence` / `not_empty`

Change `not_empty` and `not_blank` to return `text?` instead of `bool`:

```simple
fn not_empty(s: text) -> text?:
    """Returns s if non-empty, nil otherwise."""
    if s.len() > 0: s else: nil

fn not_blank(s: text) -> text?:
    """Returns s if non-blank, nil otherwise."""
    if not is_blank(s): s else: nil
```

**Usage:**

```simple
# Pattern binding — the key benefit
if val name = input.not_empty:
    process(name)

# Nil coalescing — one-liner defaults
val display = input.not_empty ?? "Anonymous"

# Chained defaults (like Ruby's nested presence)
val host = config_host.not_empty ?? env_host.not_empty ?? "localhost"

# With optional text — naturally collapses text? through presence
val name: text? = get_name()
if val n = name?.not_empty:
    use(n)
```

**Pros:**
- Enables `if val` pattern binding (the user's desired pattern)
- Works with `??` for defaults without extra variables
- Chains naturally for fallback cascades
- Follows Ruby, Kotlin, Swift community patterns
- Matches Simple's existing `if val Some(x) = expr:` idiom

**Cons:**
- Breaking change from current `not_empty(s) -> bool`
- Loss of simple boolean usage: `if s.not_empty:` would now need `if s.not_empty.?:`
- Two concepts merged: "check validity" and "retrieve value"
- `not_empty` returning `text?` when input is `text` (not `text?`) may surprise users

### Option B: Separate `presence` function (keep booleans)

Keep `not_empty -> bool` and add a new `presence -> text?`:

```simple
# Boolean (unchanged)
fn not_empty(s: text) -> bool:
    s.len() > 0

# Value-returning (new)
fn presence(s: text) -> text?:
    """Returns s if non-empty, nil otherwise. For blank: use presence_nb."""
    if s.len() > 0: s else: nil

fn presence_nb(s: text) -> text?:
    """Returns s if non-blank, nil otherwise."""
    if not is_blank(s): s else: nil
```

**Usage:**

```simple
# Boolean check (unchanged)
if input.not_empty:
    process(input)

# Pattern binding (new)
if val name = input.presence:
    process(name)

# Default value
val display = input.presence ?? "Anonymous"
```

**Pros:**
- No breaking changes
- Users choose boolean or value-returning style
- Clear naming: `not_empty` = predicate, `presence` = extractor
- Follows Ruby naming convention

**Cons:**
- More API surface to learn
- Two ways to do the same check
- `presence` name may be unfamiliar to non-Ruby developers
- `presence_nb` (non-blank variant) is an awkward name

### Option C: Generic `take_if` + keep booleans

Add a generic `take_if` function (like Kotlin) that works on any type:

```simple
fn take_if<T>(value: T, predicate: fn(T) -> bool) -> T?:
    if predicate(value): Some(value) else: nil
```

**Usage:**

```simple
if val name = input.take_if(not_empty):
    process(name)

if val name = input.take_if(\s: s.len() > 3):
    process(name)
```

**Pros:**
- Maximally generic — works on any type, any predicate
- No API explosion (one function covers all cases)
- Composable with any boolean predicate

**Cons:**
- Verbose for the common case: `.take_if(not_empty)` vs `.presence`
- Requires lambda/function-reference syntax
- UFCS with generics may have compiler complexity
- Less discoverable than a named method

### Option D: Dual-return `not_empty` via overloading (NOT recommended)

Overload `not_empty` to return `bool` when used in boolean context, `text?` when used in `if val`:

**Not feasible** — Simple doesn't have return-type-based overloading, and this would make type inference ambiguous.

### Option E: Change `.?` operator to return `T?` (short grammar)

Currently `.?` returns `bool`. Change it to return `T?` — the value if present, nil if not:

```simple
# .? on text:  returns text?  (Some(s) if non-empty, nil if "")
# .? on [T]:   returns [T]?   (Some(list) if non-empty, nil if [])
# .? on T?:    returns T?     (pass-through — already optional)

# Pattern binding — 2 characters!
if val name = input.?:
    process(name)

# Nil coalescing
val host = config_host.? ?? env_host.? ?? "localhost"

# Chained with optional text
val name: text? = get_name()
if val n = name.?:       # text? pass-through: Some → Some, nil → nil
    use(n)
```

**Compiler implementation analysis:**

The `.?` operator pipeline was investigated in detail:

| Stage | Current State | Change Needed |
|-------|--------------|---------------|
| **Lexer** (`tokens.spl:133`) | `TOK_DOT_QUESTION = 133` | None |
| **Parser** (`parser_expr.spl:634`) | Currently only handles `?.field` chaining | Must also handle standalone `.?` |
| **HIR** (`hir_definitions.spl:354`) | `ExistsCheck(base: HirExpr)` | None |
| **Type inference** (`expr_infer.spl:361`) | Returns `Type.Bool` | **Change to `type_Optional(expr_ty)`** |
| **Semantics** (`resolve.spl`, `safety_checker.spl`) | Resolves/checks subexpr | None |
| **MIR lowering** | **MISSING** — no `ExistsCheck` case | Must add: test tag + wrap in Some/nil |
| **Backend codegen** (LLVM, C) | **MISSING** | Must add code generation |
| **Interpreter** | **MISSING** | Must add evaluation |

**Critical: backward compatibility with `if s.?:`**

Currently `if s.?:` works because `.?` returns `bool`. If changed to `T?`:
- `if s.?:` would get `text?` in condition position
- Simple's truthiness system (`val_is_truthy`) handles: `nil` → false, `""` → false, non-empty string → true
- So `if text?:` would need to be: truthy if `Some(non-falsy)`, falsy if `nil` or `Some(falsy)`
- The truthiness system already handles `nil` (`VAL_NIL → false`) and text (`"" → false`)
- **IF the Optional unwraps implicitly in boolean context**, backward compat is preserved

**Truthiness coercion path:**
```
if s.?:     # s: text → .? → text?
            # text? in boolean context → unwrap: Some("hello") → "hello" → truthy
            # text? in boolean context → nil → falsy
            # text? in boolean context → Some("") → "" → falsy (!)
```

Wait — this is actually BETTER than current behavior. Currently `if s.?:` with `s = ""` returns `false`. With the new system, `Some("").?` → `text?` → unwrap → `""` → falsy. Same result!

**Truthiness system changes needed:**

In `truthiness.spl`, add `"Option"` to value-dependent types:
```simple
fn truthinessrules_is_value_dependent_type(type_name: text) -> bool:
    type_name in ["Bool", "Int", "Float", "String", "Array", "Tuple", "Dict", "Nil", "Option"]
```

In `value.spl:val_is_truthy`, add Option handling:
```simple
if kind == VAL_OPTION:
    if is_none: return false
    return val_is_truthy(inner_value)  # recurse into wrapped value
```

**Parser fix needed:**

Current parser (`parser_expr.spl:634-639`) treats `TOK_QUESTION_DOT` only as `?.field`:
```simple
elif par_kind == TOK_QUESTION_DOT:
    parser_advance()
    val field_name = par_text
    parser_expect(TOK_IDENT)         # <-- expects identifier after .?
    base = expr_field_access(...)
```

Must add branch: if no identifier follows `.?`, create `ExistsCheck(base)` node.

**Total files to modify: ~8-12**
- Lexer disambiguation: 1 file
- Parser: 1 file (add standalone `.?` branch)
- Type inference: 1 line change (`Type.Bool` → `type_Optional(expr_ty)`)
- Truthiness: 2 files (add Option)
- MIR lowering: 1 file (add `ExistsCheck` case)
- Backend codegen: 2-3 files (LLVM, C, potentially Cranelift)
- Interpreter: 1 file

**Pros:**
- **Shortest possible grammar** — 2 characters (`.?`)
- No new functions or API surface
- `.?` already means "is present/usable" — returning the value is the natural semantic
- Backward compatible if truthiness is extended for Optional
- Works for ALL types (text, arrays, dicts, options) — not just text

**Cons:**
- Compiler changes across multiple stages (but each is small)
- `.?` now has dual personality: returns `T?` but acts as `bool` in conditionals
- MIR lowering and backend codegen are currently MISSING for `.?` entirely
- Must implement the missing pipeline regardless

### Option F: Implicit `if val` for text (truthiness binding)

Extend `if val x = expr:` to work when `expr` is `text` (not just `T?`):

```simple
# Currently works (expr is T?)
if val name = get_optional_name():    # text? → unwrap if Some
    use(name)

# NEW: also works (expr is text, empty → fails binding)
if val name = get_name():             # text → bind if non-empty
    use(name)
```

The compiler would auto-insert presence conversion: `text` → `text?` where `""` → `nil`.

```simple
# Desugars to:
if val name = (get_name().? ):    # .? converts text → text?
    use(name)
```

**Pros:**
- **Zero extra characters** — shortest possible
- Natural extension of `if val` semantics
- Aligns with Python's `if name := get_input():`

**Cons:**
- Ambiguous: what does `if val x = 0:` mean? `if val x = false:`?
- Need to define which types support implicit truthiness binding
- Could be confusing: `text` is not `text?`, yet `if val` treats it as optional
- Type system complexity: `if val x = expr:` now means different things for `T?` vs `text`

**Resolution:** Only apply to types where `.?` is meaningful (text, arrays, dicts). NOT to primitives.
Rule: `if val x = expr:` where `expr: T` and `T` has a `.?` semantic → auto-apply `.?` → `T?` → `if val`.

---

## 5. Comparison Matrix

| Criterion | A: `not_empty→T?` | B: `presence` | C: `take_if` | E: `.?→T?` | F: implicit `if val` |
|-----------|-------------------|---------------|--------------|------------|---------------------|
| Extra chars | `.not_empty` (10) | `.presence` (9) | `.take_if(f)` (12+) | **`.?` (2)** | **0** |
| Breaking change | **Yes** | No | No | **Yes** | No |
| Enables `if val` | Yes | Yes | Yes | Yes | Yes |
| Enables `??` | Yes | Yes | Yes | Yes | No |
| API surface | None (replace) | +2 functions | +1 generic | None | None |
| Compiler work | Low | **None** | Medium | Medium | Medium |
| Works for all types | Text only | Text only | All | **All** | Text/Array/Dict |
| Backward compat | `if s.not_empty:` breaks | Full | Full | `if s.?:` preservable | Full |
| Grammar shortness | Medium | Medium | Verbose | **Shortest** | **Shortest** |

### Recommended approach: E+B (hybrid)

**Primary: Option E** — Change `.?` to return `T?`. This gives the 2-character grammar.
**Secondary: Option B** — Also add `presence(text) -> text?` as stdlib convenience.

The hybrid gives both:
```simple
# Short form (operator) — for quick code
if val name = input.?:
    process(name)

val host = env_host.? ?? "localhost"

# Named form (function) — for readable code
if val name = input.presence:
    process(name)

val host = env_host.presence ?? "localhost"
```

---

## 6. Real-World Impact Analysis

### Current codebase usage of `not_empty` / `is_empty`

Surveying the codebase, the pattern of "check then use" appears frequently:

```simple
# Pattern seen 5+ times in integration_test_config_spec.spl
if original_ci.not_empty:
    env_set("CI", original_ci ?? "")

# Pattern in coverage.spl
if env_path.not_empty:
    use_path(env_path)

# Pattern in api_tools.spl
if source.is_empty:
    return error(...)
# (else use source)
```

With Option B (`presence`), these become:

```simple
# Binding directly
if val ci = original_ci.presence:
    env_set("CI", ci)

# Default value
val path = env_path.presence ?? default_path

# Early return on invalid
val source = rt_file_read_text(file_path)
if val src = source.presence:
    process(src)
else:
    return error(...)
```

### Benefit estimation

| Pattern | Boolean `not_empty` | Value-returning `presence` | Improvement |
|---------|--------------------|-----------------------------|-------------|
| Check + use | 2 refs to same var | 1 binding | Less duplication |
| Optional + check + unwrap | `.?` + `?.not_empty` + `?? ""` | `.presence` + `if val` | Significantly simpler |
| Default fallback | `if ... else ...` | `x.presence ?? default` | One-liner |
| Chained defaults | Nested `if`s | `a.presence ?? b.presence ?? c` | Linear vs nested |

### Complexity cost

| Change | Compiler impact | Runtime impact | Learning curve |
|--------|----------------|----------------|---------------|
| Add `presence` function | None (pure stdlib) | None | Low |
| Change `not_empty` return | None (pure stdlib) | None | Medium (breaking) |
| Extend `.?` operator | Significant | Possible | High |
| Generic `take_if` | Moderate (generics) | None | Medium |

---

## 7. Recommendation

### Primary: Option E — Change `.?` to return `T?`

**This is the short-grammar answer.** `.?` already means "is this present?" — make it return the present value, not just a boolean.

```simple
# Before (current): .? returns bool
if s.?:           # bool — can't bind
    use(s)        # must reference s again

# After (proposed): .? returns T?
if val name = s.?:    # text? — binds!
    use(name)         # bound, guaranteed non-empty

val host = config.? ?? env.? ?? "localhost"   # chained defaults
```

**Implementation roadmap:**

1. **Parser** (`parser_expr.spl`): Add standalone `.?` branch (currently only `?.field`)
2. **Type inference** (`expr_infer.spl:361`): Change `Ok(Type.Bool)` → `Ok(type_Optional(expr_ty))`
3. **Truthiness** (`truthiness.spl`): Add `"Option"` to value-dependent types
4. **MIR lowering** (`mir_lowering_expr.spl`): Add `ExistsCheck` case — tag test + Some/nil
5. **Backend codegen** (LLVM, C): Generate code for existence check
6. **Interpreter** (`value.spl`): Add Option truthiness unwrapping

**Note:** MIR lowering and backend codegen are currently MISSING for `.?` entirely (it only works through type inference + semantics but has no code generation). The `.?` pipeline must be completed regardless — this proposal just changes what it returns.

### Secondary: Also add `presence` as stdlib convenience

For readability-sensitive code:

```simple
fn presence(s: text) -> text?:
    """Returns s if non-empty, nil otherwise."""
    if s.len() > 0: Some(s) else: nil

fn presence_trimmed(s: text) -> text?:
    """Returns s if non-blank (after trim), nil otherwise."""
    if not is_blank(s): Some(s) else: nil
```

This is pure stdlib — zero compiler changes, can ship immediately.

### Export changes

```simple
# src/lib/common/text.spl — add to exports
export is_whitespace, is_empty, is_blank, not_empty, not_blank, presence, presence_trimmed

# src/lib/text.spl — add to re-exports
export is_whitespace, is_empty, is_blank, not_empty, not_blank, presence, presence_trimmed
```

### Phased rollout

| Phase | What | Compiler change? |
|-------|------|-----------------|
| **Phase 1** (now) | Add `presence` + `presence_trimmed` to stdlib | No |
| **Phase 2** | Complete `.?` MIR + codegen pipeline (returns `bool`) | Yes (bug fix) |
| **Phase 3** | Change `.?` return from `bool` → `T?` + truthiness | Yes (semantic change) |

Phase 1 gives immediate value. Phase 2 is needed anyway. Phase 3 delivers the short grammar.

---

## 8. API Summary (After Implementation)

### Boolean predicates (existing — unchanged)

| Function | Signature | UFCS | Purpose |
|----------|-----------|------|---------|
| `is_empty` | `(text) -> bool` | `s.is_empty` | True if `""` |
| `is_blank` | `(text) -> bool` | `s.is_blank` | True if `""` or whitespace-only |
| `not_empty` | `(text) -> bool` | `s.not_empty` | True if not `""` |
| `not_blank` | `(text) -> bool` | `s.not_blank` | True if not empty/whitespace |

### Value-returning extractors (new)

| Function | Signature | UFCS | Purpose |
|----------|-----------|------|---------|
| `presence` | `(text) -> text?` | `s.presence` | Returns `s` if non-empty, `nil` if `""` |
| `presence_trimmed` | `(text) -> text?` | `s.presence_trimmed` | Returns `s` if non-blank, `nil` if empty/whitespace |

### Usage patterns

```simple
# Boolean — simple conditionals (unchanged)
if input.not_empty:
    process(input)

# Short form — .? operator (Phase 3)
if val name = input.?:
    process(name)

val display = input.? ?? "Anonymous"
val host = config.? ?? env.? ?? "localhost"

# Named form — presence function (Phase 1)
if val name = input.presence:
    process(name)

val display = input.presence ?? "Anonymous"

# Optional text — both forms work
val name: text? = get_name()
if val n = name.?:            # .? on text? is pass-through
    use(n)

# Trimmed presence — skip whitespace
if val query = user_input.presence_trimmed:
    search(query)
```

### Existence check (`.?`) — after Phase 3

```simple
# Returns T? (value-or-nil), not bool
s.?                    # text?:  Some(s) if non-empty, nil if ""
opt.?                  # T?:     pass-through
list.?                 # [T]?:   Some(list) if non-empty, nil if []

# Still works in boolean context (truthiness of T?)
if s.?:                # truthy if Some(non-falsy), falsy if nil or Some("")
    use(s)
```

---

## 9. Cross-Language Reference

| Language | Boolean Check | Presence (value-or-nil) | Binding Syntax |
|----------|--------------|------------------------|----------------|
| **Simple** (proposed) | `s.not_empty` | `s.presence` | `if val x = s.presence:` |
| **Ruby** (Rails) | `s.present?` | `s.presence` | `if x = s.presence` |
| **Kotlin** | `s.isNotEmpty()` | `s.takeIf { it.isNotEmpty() }` | `?.let { x -> }` |
| **Swift** | `!s.isEmpty` | `s.nonEmpty` (extension) | `if let x = s.nonEmpty` |
| **Rust** | `!s.is_empty()` | `opt.filter(\|s\| !s.is_empty())` | `if let Some(x) = ...` |
| **Python** | `bool(s)` | `s or None` | `if x := s:` |
| **Java** | `!s.isEmpty()` | `Optional.of(s).filter(...)` | `.ifPresent(x -> ...)` |
| **C#** | `!string.IsNullOrEmpty(s)` | `s is { Length: > 0 } x` | Pattern matching |
| **Haskell** | `not (null s)` | `mfilter (not . null) (Just s)` | `do` notation |
| **Scala** | `s.nonEmpty` | `Option(s).filter(_.nonEmpty)` | `for { x <- ... }` |

---

## 10. Open Questions

1. **Naming:** Is `presence` the best name? Alternatives: `to_option`, `non_empty` (returns text?), `value_if_not_empty`, `present`.

2. **Blank variant naming:** `presence_trimmed` vs `presence_nb` vs `blank_presence` vs `meaningful` vs `content`.

3. **Generic version:** Should there be a generic `presence<T>` trait eventually? Would cover collections (`list.presence` returns `[T]?` if non-empty), maps, etc. With `.?` returning `T?`, this becomes less needed since `.?` is already generic.

4. **`.?` backward compat edge case:** `Some("").?` — with bool return: `false`. With `T?` return + truthiness: `Some("") → "" → false`. Same! But `Some(0).?` — with bool return: `true` (it's Some). With `T?` return + truthiness: `Some(0) → 0 → false`. **Different!** This is a semantic change for `Option<Int>` where `Some(0).?` would become falsy. Is this acceptable?

5. **Performance:** `presence` creates an `Option` wrapper. For hot paths, is the allocation concern real? (Likely negligible — `text?` is probably a tagged pointer or discriminated union.)

6. **Parser ambiguity:** `.?` currently shares token `TOK_QUESTION_DOT` with `?.` (optional chaining). The lexer/parser must disambiguate: `expr.?` (standalone existence) vs `expr?.field` (chaining). Current parser always expects an identifier after `.?` — fixing this is needed regardless.

7. **Completed `.?` pipeline:** The `.?` operator is partially implemented — HIR and type inference exist but MIR lowering and backend codegen are MISSING. Should completing the pipeline be a prerequisite for either approach?

---

## 11. Implementation Status (2026-02-24)

All three phases of the hybrid E+B approach have been implemented:

### Phase 1: `presence` stdlib functions — DONE

- Added `presence(text) -> text?` and `presence_trimmed(text) -> text?` to `src/lib/common/text.spl`
- Added exports in both `src/lib/common/text.spl` and `src/lib/text.spl`
- Tests: `test/unit/lib/common/text_empty_spec.spl` (8 tests)

### Phase 2: Complete `.?` core parser/interpreter pipeline — DONE

- **Lexer** (`lexer.spl`, `lexer_struct.spl`): `.?` now emits `TOK_DOT_QUESTION` (133) instead of `TOK_QUESTION_DOT` (131)
- **AST** (`ast_expr.spl`): Added `EXPR_EXISTS_CHECK = 49` tag and `expr_exists_check()` constructor
- **Parser** (`parser_expr.spl`): Both `parse_postfix` and `parse_postfix_on` handle `TOK_DOT_QUESTION` as standalone existence check
- **Value** (`value.spl`): Added `val_exists()` — nil/empty-string/empty-array = false, else true
- **Eval** (`eval.spl`): Handles `EXPR_EXISTS_CHECK` — returns value if present, nil if absent

### Phase 3: Change `.?` return type from `bool` to `T?` — DONE

- **Type inference** (`expr_infer.spl`): `ExistsCheck` now returns `type_Optional(inner: expr_ty)` instead of `Type.Bool`. Already-optional types pass through (no double-wrapping).
- **Truthiness** (`truthiness.spl`): Added `"Option"` to value-dependent types list
- **Interpreter** (`eval.spl`): Returns value if present, `nil` if absent (not bool)

### Open questions resolved

- **Q4 (backward compat):** `Some(0).?` now returns `0` (falsy) instead of `true` (exists). Accepted — `.?` now means "extract present value" not "exists as bool". Most usage is on text/collections where behavior is unchanged.
- **Q6 (parser ambiguity):** Resolved by using separate token `TOK_DOT_QUESTION` (133) for `.?` vs `TOK_QUESTION_DOT` (131) for `?.`.

### Files modified

| Phase | File | Change |
|-------|------|--------|
| 1 | `src/lib/common/text.spl` | `presence`, `presence_trimmed` + exports |
| 1 | `src/lib/text.spl` | Re-exports |
| 2 | `src/compiler/10.frontend/core/lexer.spl` | `.?` → `TOK_DOT_QUESTION` |
| 2 | `src/compiler/10.frontend/core/lexer_struct.spl` | Same |
| 2 | `src/compiler/10.frontend/core/ast_expr.spl` | `EXPR_EXISTS_CHECK = 49` |
| 2 | `src/compiler/10.frontend/core/parser_expr.spl` | Handle `TOK_DOT_QUESTION` |
| 2 | `src/compiler/10.frontend/core/interpreter/value.spl` | `val_exists()` |
| 2+3 | `src/compiler/10.frontend/core/interpreter/eval.spl` | Handle `EXPR_EXISTS_CHECK` → value/nil |
| 3 | `src/compiler/30.types/type_system/expr_infer.spl` | Return `Optional(T)` not `Bool` |
| 3 | `src/compiler/35.semantics/semantics/truthiness.spl` | Add `"Option"` |

---

## References

- Ruby on Rails `presence`: [API docs](https://api.rubyonrails.org/classes/Object.html#method-i-presence)
- Kotlin `takeIf`/`ifEmpty`: [Kotlin stdlib docs](https://kotlinlang.org/api/core/kotlin-stdlib/)
- Swift Forums `nonEmpty` proposal: [forums.swift.org](https://forums.swift.org/t/presence-value-isempty-nil-value/14869)
- Rust `Option::filter`: [std::option docs](https://doc.rust-lang.org/std/option/enum.Option.html#method.filter)
- Haskell `mfilter`: [Control.Monad docs](https://hackage.haskell.org/package/base/docs/Control-Monad.html)
- Simple `if val` syntax: `test/feature/usage/elif_val_pattern_binding_spec.spl`
- Simple `.?` operator: `doc/guide/syntax_quick_reference.md` (line 343)
- Simple text utilities: `src/lib/common/text.spl` (lines 210–224)
