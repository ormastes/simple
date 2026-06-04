# Tag System Refactoring Research

**Date:** 2026-03-29
**Status:** Research Complete — Decision Required
**Scope:** `@` decorators vs `#[...]` attributes — merge, split, or clarify

---

## 1. Current State Analysis

Simple currently has **two distinct tag systems** that have grown to overlap:

### 1.1 `@` Decorators (Python/Java-style)

**Token:** `TOK_AT` (171)
**AST Node:** `Decorator { name: Expr, args: Option<Vec<Argument>> }` — supports **named arguments**
**Parser:** Rust bootstrap `parse_decorator()`, Simple self-hosted attribute parsing

**Categories:**

| Category | Tags | Count |
|----------|------|-------|
| **Effects** (type-system) | `@async`, `@pure`, `@io`, `@net`, `@fs`, `@unsafe`, `@verify`, `@trusted`, `@ghost`, `@auto_lean` | 10 |
| **Layout/Memory** | `@repr("C")`, `@packed`, `@align(N)`, `@volatile`, `@volatile_read`, `@volatile_write`, `@nonvolatile`, `@address(0x...)` | 8 |
| **Function Control** | `@entry`, `@naked`, `@noreturn`, `@boot`, `@interrupt`, `@section("X")`, `@alloc`, `@no_alloc` | 8 |
| **Export/FFI** | `@export("C", name: "sym")`, `@extern("browser", "fn")`, `@callconv(...)` | 3 |
| **GPU/SIMD** | `@gpu_kernel`, `@simd`, `@bounds(...)` | 3 |
| **Task Scheduling** | `@task(instances=N, group="name", frame=N)` | 1 (complex) |
| **Conditional** | `@when(cond)`, `@cfg(key)`, `@elif`, `@else`, `@end` | 5 |
| **Introspection** | `@annotation(...)`, `@traits(...)`, `@file`, `@line`, `@function` | 5 |
| **Meta** | `@deprecated("msg")`, `@must_use`, `@macro`, `@bits(N)` | 4 |
| **Link** | `@link_section("name")`, `@addr_space("region")` | 2 |

**Total: ~49 unique `@` tags**

### 1.2 `#[...]` Attributes (Rust-style)

**Token:** `TOK_HASH_LBRACKET` (172)
**AST Node:** `Attribute { name: String, args: Option<Vec<Expr>> }` — **positional arguments only**
**Parser:** `AttributeParser` in `parser_extensions.spl`

**Categories:**

| Category | Tags | Count |
|----------|------|-------|
| **Test/Spec** | `#[timeout(ms)]`, `#[tag("slow")]`, `#[skip("reason")]`, `#[only]`, `#[slow]`, `#[ignore]` | 6 |
| **Test Modes** | `#[modes(...)]`, `#[skip_modes(...)]`, `#[only_modes(...)]`, `#[mode_failure_strategy(...)]` | 4 |
| **Lint Control** | `#[allow(lint)]`, `#[warn(lint)]`, `#[deny(lint)]` | 3 |
| **Module** | `#[no_gc]`, `#[bypass]`, `#[no_prelude]`, `#[no_auto_defer]`, `#[concurrency_mode(...)]` | 5 |
| **Compiler** | `#[inline]`, `#[derive(...)]`, `#[repr(...)]`, `#[default]`, `#[no_mangle]`, `#[cfg(...)]` | 6 |
| **GPU** | `#[gpu]` | 1 |

**Total: ~25 unique `#[]` tags**

### 1.3 Overlap (Duplicated Tags)

These tags exist in **BOTH** systems:

| Tag | `@` form | `#[]` form | Notes |
|-----|----------|------------|-------|
| `repr` | `@repr("C")` | `#[repr(...)]` | Same semantics |
| `inline` | `@inline` | `#[inline]` | Same semantics |
| `derive` | `@derive(...)` | `#[derive(...)]` | Same semantics |
| `unsafe` | `@unsafe` | `#[unsafe]` | `@` is effect, `#[]` is block marker |
| `gpu` | `@gpu_kernel` | `#[gpu]` | Similar intent |
| `cfg` | `@cfg(key)` | `#[cfg(...)]` | Conditional compilation |

### 1.4 HIR Merge Behavior

At the HIR level, the compiler **already merges** both systems:

```rust
// compiler_rust/compiler/src/hir/lower/function.rs:296-305
let mut attributes: Vec<String> = f.attributes.iter()
    .map(|attr| attr.name.clone()).collect();
for dec in &f.decorators {
    if Effect::from_decorator_name(name).is_none() {
        attributes.push(name.clone());
    }
}
```

This means for AOP matching and downstream passes, `@foo` and `#[foo]` are **already indistinguishable**. The separation only exists at the surface syntax and AST level.

---

## 2. Cross-Language Comparison

### 2.1 Languages with ONE Unified System

| Language | Syntax | Result |
|----------|--------|--------|
| **Rust** | `#[...]` / `#![...]` | Clean, consistent. Inner vs outer attrs via `!`. Widely praised. |
| **Java** | `@Annotation` | Unified. Retention policy (SOURCE/CLASS/RUNTIME) distinguishes compile vs runtime. |
| **Kotlin** | `@Annotation` + use-site targets (`@get:`, `@field:`) | Elegant disambiguation without separate syntax. |
| **Swift** | `@attribute` | One system covers everything from `@available` to `@objc`. |
| **Python** | `@decorator` | One syntax. Decorators are just functions — maximum flexibility. |

**Verdict:** Languages with unified systems cause less confusion and have simpler grammars.

### 2.2 Languages with MULTIPLE Systems

| Language | Systems | Result |
|----------|---------|--------|
| **C/C++** | `__attribute__(())`, `[[...]]`, `#pragma`, `__declspec` | Universally criticized. Fragmented, confusing. |
| **Go** | struct tags (backtick), build tags (`//go:build`), magic comments (`//go:generate`) | Criticized for stringly-typed struct tags. |
| **C#** | `[Attribute]` + `#region` + `#pragma` | `#pragma` is tolerated only for historical reasons. |

**Verdict:** Multi-system approaches accumulate technical debt and confuse users.

### 2.3 Key Lessons

1. **Unified syntax wins.** Every language that started with two systems regrets it (C++, Go).
2. **Distinguish via categories, not syntax.** Kotlin's `@get:JvmName("x")` use-site targets and Java's retention policies show you can distinguish purpose without separate syntaxes.
3. **Named arguments matter.** C#'s `[Obsolete("msg", error: true)]` is superior to positional-only.
4. **Conditional compilation should be part of the tag system**, not a preprocessor (Rust `#[cfg]` > C `#ifdef`).

---

## 3. Root Cause of the Duplication

### 3.1 Original Intent (Reconstructed)

Based on the AST structure differences:

- **`@` decorators** were designed for **semantic annotations** that affect the type system, code generation, and calling conventions. They support named arguments because directives like `@export("C", name: "foo")` need them.
- **`#[...]` attributes** were designed for **metadata** that doesn't change code semantics — test configuration, lint suppression, module settings.

### 3.2 How It Drifted

Over time, both systems expanded beyond their original scope:

1. `@repr("C")` is a **compiler directive** (layout) — should have been `#[]` by the original rule
2. `#[inline]` is a **code generation hint** — could be argued as `@` territory
3. `#[derive(...)]` **generates code** — clearly `@` behavior
4. `@deprecated("msg")` is **metadata** — clearly `#[]` behavior
5. `@cfg(key)` is **conditional compilation** — doesn't fit neatly in either

The result: users cannot predict which system a given tag belongs to.

---

## 4. Refactoring Options

### Option A: Merge to `@` Only (Recommended)

**Syntax:** `@name` and `@name(arg1, key: val)`

**Rationale:**
- `@` is more readable and requires less typing than `#[...]`
- `@` already supports named arguments (critical for `@export`, `@task`)
- Most languages (Java, Kotlin, Swift, Python) use `@`-style syntax
- The HIR already merges both — surface syntax should match
- `#[` requires bracket matching, adding parser complexity

**Migration:**
```
#[timeout(5000)]     →  @timeout(5000)
#[tag("slow")]       →  @tag("slow")
#[allow(lint_name)]  →  @allow(lint_name)
#[no_gc]             →  @no_gc
#[skip_modes(smf)]   →  @skip_modes(smf)
```

**Distinguish via convention (not syntax):**

| Convention | Tags | Target |
|------------|------|--------|
| **Effect prefix** | `@async`, `@pure`, `@io`, `@net`, `@fs`, `@unsafe` | Functions only |
| **Layout prefix** | `@repr`, `@packed`, `@align`, `@volatile` | Types/fields |
| **Test prefix** | `@timeout`, `@tag`, `@skip`, `@slow`, `@only` | Test blocks |
| **Lint prefix** | `@allow`, `@warn`, `@deny` | Any item |
| **Compiler prefix** | `@inline`, `@entry`, `@naked`, `@export`, `@cfg` | Functions/modules |

**Pros:**
- One syntax to learn
- Simpler grammar, lexer, parser
- Matches majority of modern languages
- Eliminates overlap confusion
- Named arguments available everywhere

**Cons:**
- Large migration (all `#[]` usages must change)
- Lose visual distinction between "metadata" and "directives"

---

### Option B: Merge to `#[...]` Only

**Syntax:** `#[name]` and `#[name(arg1, key: val)]`

**Rationale:** Matches Rust exactly, which Simple already borrows heavily from.

**Migration:**
```
@entry              →  #[entry]
@repr("C")          →  #[repr("C")]
@export("C")        →  #[export("C")]
@async              →  #[async]      ← awkward for effects
```

**Pros:**
- Rust users feel at home
- Inner attributes (`#![...]`) possible for module-level

**Cons:**
- Effects read badly: `#[async] #[pure] fn foo()` vs `@async @pure fn foo()`
- More typing, more bracket noise
- Named arguments need to be added to `#[]` parser
- `@` is more natural for "decorating" functions

---

### Option C: Keep Both with Explicit Rules (Current + Cleanup)

**Rule:** `@` for **semantics** (code gen, type system), `#[]` for **metadata** (test config, lint, docs)

**Cleanup required:**
```
# Move to @  (semantic directives wrongly in #[])
#[inline]     →  @inline       (code gen hint)
#[derive]     →  @derive       (code generation)
#[repr]       →  @repr         (layout - already exists as @)
#[no_mangle]  →  @no_mangle    (linker directive)
#[cfg]        →  @cfg          (conditional - already exists as @)
#[default]    →  @default      (trait specialization)

# Move to #[] (metadata wrongly in @)
@deprecated   →  #[deprecated] (metadata, not code gen)
@must_use     →  #[must_use]   (lint/warning metadata)
@macro        →  #[macro]      (declaration metadata)
```

**Pros:**
- Minimal migration
- Visual distinction preserved
- Effects stay clean (`@async`, `@pure`)

**Cons:**
- Users still need to memorize which system for each tag
- Two parsing paths, two AST types to maintain
- Overlap will re-emerge over time (proven by history)
- Goes against industry trend toward unification

---

### Option D: `@` for Everything + `#` for Doc Comments Only

**Syntax:**
- `@name(args)` — all attributes/decorators
- `# text` — doc comments (already used this way)
- Remove `#[...]` entirely

**Rationale:** Clean separation: `#` = documentation, `@` = code metadata

**Pros:**
- Maximally simple grammar
- `#` has a clear, singular purpose
- No ambiguity about which system to use

**Cons:**
- Same as Option A (migration cost)

---

## 5. Recommendation

### **Option A (Merge to `@`) is recommended**, with Option D as the ideal end-state.

**Reasoning:**

1. **The HIR already unifies them** — the dual syntax is a surface-level fiction
2. **Effects are Simple's killer feature** — `@async @pure fn foo()` reads beautifully; `#[async] #[pure] fn foo()` does not
3. **Named arguments** are critical and already work for `@`
4. **6 tags overlap today** — this number will only grow without action
5. **Every modern language** (Java, Kotlin, Swift, Python) that chose `@` has been satisfied with it
6. **Every language** (C/C++, Go) with multiple systems regrets it

### Migration Strategy

**Phase 1: Deprecation (non-breaking)**
- Parser accepts both `@tag(...)` and `#[tag(...)]` for ALL attributes
- Emit deprecation warning for `#[...]` usage
- Add `--fix-tags` auto-migration to `bin/simple fix`

**Phase 2: Migration**
- Run `--fix-tags` across the codebase
- Update all documentation and examples
- Update test runner to use `@timeout`, `@tag`, `@skip`

**Phase 3: Removal**
- Remove `TOK_HASH_LBRACKET` from lexer
- Remove `AttributeParser` from parser_extensions.spl
- Remove `Attribute` struct (merge into `Decorator`)
- Simplify HIR lowering (no merge step needed)

### Category System (Post-Merge)

Instead of two syntaxes, use **documented categories** with linting:

```simple
# Effect annotations (affect type system)
@async @pure @io @net @fs @unsafe @verify @trusted @ghost

# Layout annotations (affect memory layout)
@repr("C") @packed @align(16) @volatile @address(0x40020000)

# Compiler directives (affect code generation)
@entry @naked @noreturn @boot @interrupt @export("C") @inline @no_mangle

# Test metadata (test runner configuration)
@timeout(5000) @tag("slow") @skip("reason") @only @slow

# Lint control (diagnostic configuration)
@allow(lint_name) @warn(lint_name) @deny(lint_name)

# Conditional compilation
@cfg(target_os: "linux") @when(feature: "gpu")

# Module configuration
@no_gc @no_prelude @bypass @concurrency_mode(lock_base)
```

The linter can enforce that `@entry` only appears on functions, `@repr` only on types, `@timeout` only in spec blocks, etc. — **target validation replaces syntax splitting**.

---

## 6. Key Files to Modify (if proceeding)

| Component | File | Change |
|-----------|------|--------|
| Lexer tokens | `src/compiler/10.frontend/core/tokens.spl` | Deprecate `TOK_HASH_LBRACKET` |
| Lexer scanner | `src/compiler/10.frontend/core/lexer_scanners.spl` | Emit warning for `#[` |
| Parser | `src/compiler/10.frontend/parser_extensions.spl` | Route `#[]` to decorator parser |
| AST types | `src/compiler/10.frontend/parser_types.spl` | Unify Attribute into Decorator |
| Rust AST | `src/compiler_rust/parser/src/ast/nodes/core.rs` | Merge Attribute → Decorator |
| Rust parser | `src/compiler_rust/parser/src/parser_impl/attributes.rs` | Unify parsing |
| HIR lowering | `src/compiler/20.hir/hir_lowering/items.spl` | Simplify (no merge) |
| Rust HIR | `src/compiler_rust/compiler/src/hir/lower/function.rs` | Remove merge step |
| Attributes | `src/compiler/00.common/attributes.spl` | Update to use Decorator |
| TreeSitter | `src/compiler/10.frontend/treesitter/outline.spl` | Remove `is_hash_bracket` |
| Test runner | Test framework files | `#[timeout]` → `@timeout` |
| Lint config | `src/compiler_rust/lib/std/src/tooling/lint_config.spl` | `#[allow]` → `@allow` |
| All .spl files | ~250 occurrences of `#[` | Automated migration |

---

## 7. Open Questions for Decision

1. **Inner attributes?** Rust's `#![...]` applies to the enclosing item. Do we need `@!name` or similar?
2. **User-defined annotations?** Should `@custom(...)` be extensible (like Java custom annotations)?
3. **Retention?** Should some annotations survive to runtime (reflection) vs compile-time only?
4. **Stacking order?** Does `@async @pure fn foo()` have defined ordering semantics?
5. **Timeline?** Phase 1 in next release, or do all phases at once?

---

## Appendix: Cross-Language Reference

Full comparison available at: `doc/01_research/domain/attribute_annotation_tag_system_comparison.md`
