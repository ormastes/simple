# SDN Self-Hosting and Missing Language Features

**Version:** 2025-12
**Status:** Research

This document covers:
1. **SDN Self-Hosting** - Replacing TOML with SDN for Simple's own configuration
2. **Missing Language Features** - Features in specs but not yet in feature.md

---

## Part 1: SDN Self-Hosting

### Current State

Simple currently uses **TOML** (`simple.toml`) for package configuration:

```toml
# Current: simple.toml
[package]
name = "myproject"
version = "0.1.0"
main = "src/main.spl"

[dependencies]
http = "1.0"
json = { version = "2.0", features = ["serde"] }

[dev-dependencies]
spec = "1.0"
```

### Proposed: SDN Format

Replace `simple.toml` with `simple.sdn`:

```sdn
# Proposed: simple.sdn
package:
    name: myproject
    version: 0.1.0
    main: src/main.spl
    authors = [Alice, Bob]
    keywords = [web, api, server]

dependencies:
    http: 1.0
    json:
        version: 2.0
        features = [serde]

dev_dependencies:
    spec: 1.0

features |name, deps|
    full, [http, json, logging]
    minimal, [http]

registry:
    default: https://github.com/simple-lang/registry
```

### Benefits of SDN Self-Hosting

| Aspect | TOML | SDN |
|--------|------|-----|
| Native format | No (external) | Yes (Simple's own) |
| Token efficiency | Medium | High (table syntax) |
| Parser complexity | Separate crate | Reuse `src/sdn/` |
| Learning curve | Extra syntax | Same as data in code |
| Embedding in Simple | Manual serde | Native `data` blocks |
| LLM friendliness | Moderate | Better (less punctuation) |

### Migration Path

#### Phase 1: Dual Support (#1051-1053)

| Feature ID | Feature | Description |
|------------|---------|-------------|
| #1051 | `simple.sdn` parsing | Add SDN manifest parser alongside TOML |
| #1052 | Manifest format detection | Auto-detect `.toml` vs `.sdn` |
| #1053 | `simple pkg migrate` command | Convert `simple.toml` → `simple.sdn` |

#### Phase 2: SDN Default (#1054-1056)

| Feature ID | Feature | Description |
|------------|---------|-------------|
| #1054 | `simple init` generates `.sdn` | Default to SDN for new projects |
| #1055 | Deprecation warning for TOML | Warn when using `simple.toml` |
| #1056 | Lock file as SDN | `simple.lock` → `simple-lock.sdn` |

#### Phase 3: Full SDN (#1057-1060)

| Feature ID | Feature | Description |
|------------|---------|-------------|
| #1057 | Remove TOML dependency | Drop `toml` crate from Cargo.toml |
| #1058 | SDN for all config files | Coverage config, test config, etc. |
| #1059 | SDN for AOP/DI config | Unified predicate config in SDN |
| #1060 | SDN CLI improvements | `sdn validate`, `sdn migrate` |

### SDN Manifest Schema

```sdn
# simple.sdn schema
package:
    name: str           # Required: package name
    version: str        # Default: 0.1.0
    authors = [str]     # Optional: list of authors
    description: str    # Optional: package description
    license: str        # Optional: SPDX license
    repository: str     # Optional: source repository
    keywords = [str]    # Optional: search keywords
    main: str           # Default: src/main.spl

dependencies:
    # Short form
    <name>: <version>

    # Long form
    <name>:
        version: str
        git: str
        branch: str
        tag: str
        rev: str
        path: str
        optional: bool
        features = [str]

dev_dependencies:
    # Same as dependencies

features |name, deps|
    <feature_name>, [<dep1>, <dep2>, ...]

registry:
    default: str        # Default: https://github.com/simple-lang/registry

# Optional: profiles for build configuration
profiles:
    release:
        optimize: true
        debug_info: false
    test:
        coverage: true
```

---

## Part 2: Missing Language Features

Features documented in specs but not tracked in `feature.md`.

### Metaprogramming Features (#1061-1080)

From `doc/spec/metaprogramming.md`:

#### Macros (#1061-1065)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1061 | `macro` keyword | 📋 | Macros |
| #1062 | `gen_code` block | 📋 | Defining Macros |
| #1063 | Hygienic macro expansion | 📋 | Safety and Limits |
| #1064 | AST manipulation in macros | 📋 | Macro Capabilities |
| #1065 | Macro-as-decorator (`@name`) | 📋 | Invocation |

**Example:**
```simple
macro define_counter(name: Ident):
    gen_code:
        mut static {name}: i64 = 0
        fn {name}_increment():
            {name} = {name} + 1
            return {name}
```

#### DSL Features (#1066-1068)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1066 | `context obj:` block | 📋 | Context Blocks |
| #1067 | `method_missing` handler | 📋 | Method Missing |
| #1068 | Fluent interface support | 📋 | DSL Support Summary |

**Example:**
```simple
let html = HTMLBuilder()
context html:
    tag("h1", "Welcome")
    p "This is a DSL example."
    div:
        span "Nice!"
```

#### Built-in Decorators (#1069-1072)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1069 | `@cached` decorator | 📋 | Decorators |
| #1070 | `@logged` decorator | 📋 | Decorators |
| #1071 | `@deprecated(message)` | 📋 | Decorators |
| #1072 | `@timeout(seconds)` | 📋 | Decorators |

#### Attributes (#1073-1077)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1073 | `#[inline]` hint | 📋 | Attributes |
| #1074 | `#[derive(...)]` auto-impl | 📋 | Attributes |
| #1075 | `#[cfg(...)]` conditional | 📋 | Attributes |
| #1076 | `#[allow(...)]` / `#[deny(...)]` | 📋 | Lint Control |
| #1077 | `#[test]` marker | 📋 | Attributes |

#### Comprehensions (#1078-1079)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1078 | List comprehension `[x for x in ...]` | 📋 | List Comprehension |
| #1079 | Dict comprehension `{k: v for ...}` | 📋 | Dict Comprehension |

#### Slicing/Indexing (#1080-1082)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1080 | Negative indexing `arr[-1]` | 📋 | Negative Indexing |
| #1081 | Slicing `arr[2:5]`, `arr[::2]` | 📋 | Slicing |
| #1082 | Spread operators `[*a, *b]`, `{**d1, **d2}` | 📋 | Spread Operators |

### Pattern Matching Enhancements (#1083-1090)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1083 | Match guards `case x if x > 0:` | 📋 | Match Guards |
| #1084 | Or patterns `case "a" \| "b":` | 📋 | Or Patterns |
| #1085 | Range patterns `case 1..10:` | 📋 | Range Patterns |
| #1086 | `if let Some(x) = ...` | 📋 | If Let |
| #1087 | `while let Some(x) = ...` | 📋 | While Let |
| #1088 | Chained comparisons `0 < x < 10` | 📋 | Chained Comparisons |
| #1089 | Exhaustiveness checking | 📋 | language_enhancement.md |
| #1090 | Unreachable arm detection | 📋 | language_enhancement.md |

### Context Managers & Closures (#1091-1093)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1091 | `with open(...) as f:` | 📋 | Context Managers |
| #1092 | `ContextManager` trait | 📋 | Implementing Context Managers |
| #1093 | `move \:` closures | 📋 | Move Closures |

### Error Handling (#1094-1095)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1094 | `?` operator for Result | 📋 | The `?` Operator |
| #1095 | `?` operator for Option | 📋 | The `?` Operator |

### Memory Model (#1096-1100)

From `doc/spec/language_enhancement.md`:

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1096 | `mut T` capability (exclusive writer) | 📋 | Reference kinds |
| #1097 | `iso T` capability (isolated transferable) | 📋 | Reference kinds |
| #1098 | Capability conversions (`iso` → `mut` → `T`) | 📋 | Conversions |
| #1099 | Happens-before memory model | 📋 | Memory model |
| #1100 | Data-race-free (DRF) guarantee | 📋 | DRF guarantee |

### Interior Mutability (#1101-1103)

| Feature ID | Feature | Status | Spec Section |
|------------|---------|--------|--------------|
| #1101 | `Atomic[T]` wrapper | 📋 | Interior mutability |
| #1102 | `Mutex[T]` wrapper | 📋 | Interior mutability |
| #1103 | `RwLock[T]` wrapper | 📋 | Interior mutability |

---

## Summary

### New Feature Ranges

| Range | Category | Count |
|-------|----------|-------|
| #1051-1060 | SDN Self-Hosting | 10 |
| #1061-1082 | Metaprogramming | 22 |
| #1083-1090 | Pattern Matching | 8 |
| #1091-1095 | Context/Error | 5 |
| #1096-1103 | Memory Model | 8 |
| **Total** | | **53** |

### Implementation Priority

1. **High Priority** (foundational)
   - SDN self-hosting (#1051-1060) - dogfooding
   - `?` operator (#1094-1095) - error handling
   - Match guards/or-patterns (#1083-1084) - already common

2. **Medium Priority** (productivity)
   - Comprehensions (#1078-1079)
   - Slicing/indexing (#1080-1082)
   - Context managers (#1091-1092)

3. **Lower Priority** (advanced)
   - Full macro system (#1061-1065)
   - Memory model formalization (#1096-1103)
   - DSL features (#1066-1068)

### Related Documents

- [SDN Specification](../spec/sdn.md)
- [Metaprogramming](../spec/metaprogramming.md)
- [Language Enhancement](../spec/language_enhancement.md)
- [Features](../features/feature.md)
