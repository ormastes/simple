# Migration Pattern Cookbook - Rust to Simple

**Purpose:** Practical patterns for migrating Rust code to Simple
**Audience:** Developers performing migrations
**Status:** Based on 4 successful migrations (arg_parsing, sandbox, test_args, lint_config)

---

## Quick Reference

| Pattern | Difficulty | Code Change | Use When | Example File |
|---------|-----------|-------------|----------|--------------|
| **Boolean Flags** | ⭐ Easy | -28% | CLI parsing | arg_parsing |
| **Mutable Struct** | ⭐ Easy | -4% | Config building | test_args |
| **String Processing** | ⭐ Easy | -20% | Text parsing | arg_parsing |
| **Immutable Builder** | ⭐⭐⭐⭐⭐ Hard | +171% | **AVOID** | sandbox |

---

## Pattern 1: Boolean Flag Parsing ⭐ EASIEST

**Difficulty:** Easy
**Code change:** -20% to -30%
**Best for:** CLI argument parsing, feature flags

### Rust Pattern
```rust
pub fn parse_flags(args: &[String]) -> Flags {
    Flags {
        verbose: args.iter().any(|a| a == "--verbose"),
        debug: args.iter().any(|a| a == "--debug"),
        quiet: args.iter().any(|a| a == "--quiet"),
    }
}
```

### Simple Pattern
```simple
fn parse_flags(args: List<text>) -> Flags:
    Flags(
        verbose: args.any(\a: a == "--verbose"),
        debug: args.any(\a: a == "--debug"),
        quiet: args.any(\a: a == "--quiet")
    )
```

### Key Translations
- `args.iter().any(|a| ...)` → `args.any(\a: ...)`
- `||` → `or`
- `&&` → `and`
- No semicolons needed
- Implicit return

### Tips
✅ **DO:**
- Use `.any()` for existence checks
- Combine conditions with `or`/`and`
- Use single-line for simple conditions

❌ **DON'T:**
- Try multi-line `or` chains (not supported)
- Use match for simple equality checks

### Example Migration
**Before (Rust 10 lines):**
```rust
let flags = Flags {
    gc_log: args.iter().any(|a| a == "--gc-log"),
    gc_off: args.iter().any(|a| a == "--gc=off" || a == "--gc=OFF"),
    use_notui: args.iter().any(|a| a == "--notui"),
};
```

**After (Simple 7 lines):**
```simple
val flags = Flags(
    gc_log: args.any(\a: a == "--gc-log"),
    gc_off: args.any(\a: a == "--gc=off" or a == "--gc=OFF"),
    use_notui: args.any(\a: a == "--notui")
)
```

**Savings:** 30%

---

## Pattern 2: Mutable Struct Configuration ⭐ RECOMMENDED

**Difficulty:** Easy
**Code change:** 0% to +20% (but core logic -5%)
**Best for:** Option parsing, configuration building, accumulator patterns

### Rust Pattern
```rust
pub fn parse_options(args: &[String]) -> Options {
    let mut opts = Options::default();
    for arg in args {
        match arg.as_str() {
            "--verbose" => opts.verbose = true,
            "--output" => { /* set output */ }
            _ => {}
        }
    }
    opts
}
```

### Simple Pattern (IDIOMATIC!)
```simple
fn parse_options(args: List<text>) -> Options:
    var opts = Options.default()
    var i = 0
    while i < args.len():
        val arg = args[i]
        if arg == "--verbose":
            opts.verbose = true
        elif arg == "--output":
            # set output
        i = i + 1
    opts
```

### Why This Works Well

**Advantages over Rust:**
1. Direct field mutation (same as Rust)
2. No builder boilerplate needed
3. Type inference reduces verbosity
4. Implicit return is cleaner

**Comparison:**
- Rust: `let mut opts` → `opts.field = value`
- Simple: `var opts` → `opts.field = value`
- **Same pattern, same ergonomics!**

### Tips
✅ **DO:**
- Use `var` for mutable config
- Mutate fields directly
- Return at end (implicit)
- Use `if/elif` for flag matching

❌ **DON'T:**
- Try to use builder pattern (see Pattern 4)
- Use match for assignments (doesn't work well)

### Example Migration
**test_args.rs** migrated successfully with this pattern:
- 25 fields in struct
- 30+ flags parsed
- Core logic 4% **shorter** than Rust
- Overall +16% only due to type definitions being inlined

---

## Pattern 3: String Processing ⭐ EXCELLENT

**Difficulty:** Easy
**Code change:** -15% to -30%
**Best for:** Parsing, text transformation, escape utils

### Common Operations

| Rust | Simple | Notes |
|------|--------|-------|
| `s.trim()` | `s.trim()` | Same |
| `s.split(',')` | `s.split(",")` | Same |
| `s.ends_with('G')` | `s.ends_with("G")` | Use string, not char |
| `&s[..n]` | `s.slice(0, n)` | Explicit slice method |
| `s.parse::<u64>()` | `s.parse_u64()` | Dedicated method |
| `s.to_lowercase()` | `s.to_lowercase()` | Same |

### Memory Size Parsing Example

**Rust:**
```rust
pub fn parse_memory(s: &str) -> Result<u64, String> {
    let s = s.trim();
    let (num_str, mult) = if s.ends_with('G') {
        (&s[..s.len()-1], 1024*1024*1024)
    } else if s.ends_with('M') {
        (&s[..s.len()-1], 1024*1024)
    } else {
        (s, 1)
    };
    num_str.parse().map(|n| n * mult)
        .map_err(|e| format!("invalid: {}", e))
}
```

**Simple:**
```simple
fn parse_memory(s: text) -> Result<u64, text>:
    val trimmed = s.trim()
    var num_str = trimmed
    var mult: u64 = 1
    
    if trimmed.ends_with("G"):
        num_str = trimmed.slice(0, trimmed.len() - 1)
        mult = 1024 * 1024 * 1024
    elif trimmed.ends_with("M"):
        num_str = trimmed.slice(0, trimmed.len() - 1)
        mult = 1024 * 1024
    
    match num_str.parse_u64():
        Ok(n) => Ok(n * mult)
        Err(_) => Err("invalid memory size")
```

**Analysis:** Slightly more verbose due to explicit mutation, but very readable.

### Tips
✅ **DO:**
- Use string methods directly
- Chain operations: `s.trim().split(",")`
- Use `.map()` for transformations

❌ **DON'T:**
- Try to use char literals (use single-char strings)
- Assume slicing syntax matches Rust (use `.slice()`)

---

## Pattern 4: Immutable Builder ⚠️ AVOID

**Difficulty:** Very Hard
**Code change:** +100% to +200%
**Best for:** **NOTHING - WAIT FOR LANGUAGE FIX**

### Why It Fails

**Rust builder:**
```rust
impl Config {
    pub fn with_timeout(self, secs: u64) -> Self {
        Self { timeout: secs, ..self }  // 1 line!
    }
}
```

**Simple (current):**
```simple
# Must copy ALL fields manually
fn with_timeout(secs: u64) -> Config:
    Config(
        timeout: secs,
        host: host,              # Copy
        port: port,              # Copy
        retries: retries,        # Copy
        debug: debug,            # Copy
        # ... 20 more fields
    )  # 25 lines!
```

**Problem:** No struct update syntax in Simple yet.

### Workaround: Use Mutable Pattern Instead

**Don't do this:**
```simple
# Immutable builder (bad)
val config = Config.new()
    .with_timeout(60)
    .with_retries(3)
    .with_debug(true)
# Each method: 25 lines × 3 methods = 75 lines of boilerplate!
```

**Do this instead:**
```simple
# Mutable config (good)
var config = Config.default()
config.timeout = 60
config.retries = 3
config.debug = true
# Total: 4 lines, same result!
```

### When Builder Pattern is Necessary

If you **must** use builder pattern (e.g., for API compatibility):
- ⏸️ **WAIT** for struct update syntax
- 🔥 **P0 feature request** filed
- Estimated impact: 50-70% code reduction when added

---

## Pattern 5: List/Iterator Operations ⭐ EXCELLENT

**Difficulty:** Easy
**Code change:** -10% to -20%
**Best for:** Data transformations, filtering, mapping

### Common Operations

| Rust | Simple | Notes |
|------|--------|-------|
| `.iter().map(\|x\| ...)` | `.map(\x: ...)` | No `.iter()` needed |
| `.iter().filter(\|x\| ...)` | `.filter(\x: ...)` | Same |
| `.iter().any(\|x\| ...)` | `.any(\x: ...)` | Same |
| `.iter().find(\|x\| ...)` | `.find(\x: ...)` | Same |
| `.collect()` | `.collect()` | Same |
| `.len()` | `.len()` | Same |

### Example: Comma-Separated Parsing

**Rust:**
```rust
let domains: Vec<String> = args[i]
    .split(',')
    .map(|s| s.trim().to_string())
    .collect();
```

**Simple:**
```simple
val domains = args[i]
    .split(",")
    .map(\s: s.trim())
    .collect()
```

**Savings:** ~20% (no `.iter()`, no `.to_string()`)

---

## Pattern 6: Option/Result Handling

**Difficulty:** Medium
**Code change:** +10% to +20% (slightly more verbose)

### Result → Option

**Rust:**
```rust
options.seed = args[i].parse().ok();
```

**Simple (workaround):**
```simple
val maybe_seed = args[i].parse_u64()
if maybe_seed.is_ok():
    options.seed = Some(maybe_seed.unwrap())
```

**Note:** Waiting for `.ok()` method (P2 feature)

### Match Expressions

**Rust:**
```rust
match parse_value(&args[i]) {
    Ok(v) => config.value = v,
    Err(e) => eprintln!("error: {}", e),
}
```

**Simple:**
```simple
match parse_value(args[i]):
    Ok(v) =>
        config.value = v
    Err(e) =>
        print "error: {e}"
```

**Note:** Indentation matters, assignments work in match arms

---

## Pattern 7: Enum Definitions

**Difficulty:** Easy
**Code change:** -50% to -70%

### Rust
```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    All,
    Unit,
    Integration,
    System,
}
```

### Simple
```simple
enum Level:
    All
    Unit
    Integration
    System
```

**Savings:** 60% (no derives needed, cleaner syntax)

---

## Pattern 8: Struct Defaults

**Difficulty:** Medium
**Code change:** +100% to +200% (verbose)

### Rust (with derive)
```rust
#[derive(Default)]
pub struct Options {
    pub verbose: bool,
    pub debug: bool,
    // ... 20 more fields
}
```

### Simple (manual)
```simple
impl Options:
    static fn default() -> Options:
        Options(
            verbose: false,
            debug: false,
            # ... 20 more fields
        )
```

**Note:** Waiting for `#[derive(Default)]` (P1 feature)

---

## Anti-Patterns to Avoid

### ❌ Anti-Pattern 1: Multi-line Or Chains

**Don't:**
```simple
if arg == "foo" or
   arg == "bar":  # Parse error!
```

**Do:**
```simple
val is_match = arg == "foo" or arg == "bar"
if is_match:
```

### ❌ Anti-Pattern 2: Match in Assignment Context

**Don't:**
```simple
match value:
    Ok(v) => result = v  # May not work in all contexts
```

**Do:**
```simple
if value.is_ok():
    result = value.unwrap()
```

### ❌ Anti-Pattern 3: Builder Pattern

See Pattern 4 - just don't do it yet.

---

## Migration Workflow

### Step 1: Analyze Pattern (5 min)
1. Read Rust code
2. Identify pattern from this cookbook
3. Check difficulty rating
4. If "AVOID", stop and use workaround

### Step 2: Create Simple File (15-30 min)
1. Copy structure (enums, structs)
2. Translate functions using patterns
3. Check syntax with `simple check`

### Step 3: Create Tests (15-30 min)
1. Port Rust tests or create new ones
2. Use SSpec BDD format
3. Run with `simple test`

### Step 4: Document (10-15 min)
1. Note any novel translations
2. Update this cookbook if new pattern found
3. Create migration report

**Total time per file:** 45-90 minutes

---

## Decision Tree

```
Does it use a builder pattern?
├─ YES → ⚠️ DEFER (wait for P0 fix)
└─ NO  → ✅ Continue

Does it need mutable state?
├─ YES → ⭐ Use Pattern 2 (Mutable Struct)
└─ NO  → Continue

Is it mostly boolean flags?
├─ YES → ⭐ Use Pattern 1 (Boolean Flags)
└─ NO  → Continue

Is it string processing?
├─ YES → ⭐ Use Pattern 3 (String Processing)
└─ NO  → Continue

Is it list transformations?
├─ YES → ⭐ Use Pattern 5 (List Operations)
└─ NO  → ⚠️ Assess case-by-case
```

---

## Troubleshooting

### Problem: Parse Errors

**Check:**
1. Multi-line or chains? (not supported)
2. Missing colons after `if`/`while`/`fn`?
3. Reserved word used as variable? (`class`, `type`, etc.)

### Problem: Import Not Working

**Workaround:**
- Tooling modules don't support imports yet in tests
- Create standalone validation tests instead

### Problem: Match Not Working

**Workaround:**
- Use `if value.is_ok():` instead
- Extract to intermediate variable

---

## Success Metrics

**Good migration:**
- ✅ Compiles on first try or after minor fixes
- ✅ -20% to +20% code change
- ✅ Core logic readable and maintainable
- ✅ Tests pass

**Great migration:**
- ✅ Code reduction (-20% or more)
- ✅ More readable than Rust
- ✅ Demonstrates Simple's strengths

**Blocked migration:**
- ❌ +100% code expansion
- ❌ Builder pattern required
- ⏸️ Defer until language fix

---

## Quick Start Template

```simple
# Module description
# Migrated from: path/to/rust/file.rs

# Enums (if needed)
enum MyEnum:
    Variant1
    Variant2

# Structs
struct MyStruct:
    field1: type1
    field2: type2

impl MyStruct:
    # Use mutable pattern for config
    static fn default() -> MyStruct:
        MyStruct(field1: default1, field2: default2)

# Main function
fn my_function(args: List<text>) -> Result<MyType, text>:
    var result = MyType.default()
    
    # Use if/elif for flag matching
    var i = 0
    while i < args.len():
        val arg = args[i]
        if arg == "--flag1":
            result.field1 = value1
        elif arg == "--flag2":
            result.field2 = value2
        i = i + 1
    
    Ok(result)
```

---

## Appendix: Pattern Matrix

| Pattern | arg_parsing | sandbox | test_args | Recommended |
|---------|------------|---------|-----------|-------------|
| Boolean flags | ✅ Primary | ✅ Used | ✅ Used | ⭐⭐⭐⭐⭐ |
| Mutable struct | - | - | ✅ Primary | ⭐⭐⭐⭐⭐ |
| String processing | ✅ Used | ✅ Primary | - | ⭐⭐⭐⭐⭐ |
| Immutable builder | - | ❌ Primary | - | ❌ AVOID |
| List operations | ✅ Used | ✅ Used | ✅ Used | ⭐⭐⭐⭐ |
| Option/Result | ✅ Used | ✅ Used | ✅ Used | ⭐⭐⭐ |
| Enums | - | - | ✅ Used | ⭐⭐⭐⭐⭐ |

---

**Status:** LIVING DOCUMENT
**Last Updated:** 2026-01-20
**Next Review:** After next 3 migrations

**Contributions:** If you discover a new pattern, add it here!
