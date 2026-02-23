# Module Visibility System Design

**Status:** Implementation Ready
**Date:** 2026-02-05 (Updated)
**Author:** Claude

---

## Executive Summary

**Simplified Design:**
- **Keywords:** `pub` and `pri` (short forms, Rust-style)
- **Auto-public:** Types matching filename are public by default
- **Global variables:** Top-level `val`/`var` allowed (private by default)
- **Migration:** Warnings first, errors later

---

## 1. Problem Statement

### 1.1 Current Limitations

Simple currently has no visibility control mechanism:

1. **No top-level `val`**: Cannot declare module-level constants
   ```simple
   # ERROR: Unexpected token: expected identifier, found Val
   val MAX_SIZE: i32 = 1024
   ```

2. **Everything is implicitly public**: All types and functions are exported
   ```simple
   # All of these are visible to importers - no way to hide internals
   class PublicAPI: ...
   class InternalHelper: ...    # Should be private
   fn internal_impl(): ...      # Should be private
   ```

3. **Workarounds are verbose**: Must use function accessors for constants
   ```simple
   fn get_max_size() -> i32: 1024   # Workaround, but clutters API
   ```

### 1.2 Goals

1. Enable top-level `val` declarations (module-private by default)
2. Provide clear, simple visibility rules
3. Encourage good module organization (one main type per file)
4. Maintain backward compatibility (warning period before errors)

---

## 2. Proposed Design

### 2.1 Core Rule: Filename-Based Auto-Public

**A type is automatically public if and only if its name matches the filename.**

| File | Declaration | Visibility |
|------|-------------|------------|
| `test_case.spl` | `class TestCase` | Auto-public |
| `test_case.spl` | `class Helper` | Private |
| `test_case.spl` | `fn test_case_create()` | Private |
| `test_case.spl` | `val CONSTANT` | Private |

### 2.2 Visibility Keywords

**Simplified:** Use `pub` and `pri` (short, Rust-style)

```simple
# Explicit visibility modifiers
pub class ExplicitlyPublic: ...
pri class ExplicitlyPrivate: ...   # Optional, same as default

# No modifier = private (except filename-matching types)
class ImplicitlyPrivate: ...

# Top-level globals now allowed
val PRIVATE_CONST: i32 = 42        # Module-private constant
pub val PUBLIC_CONST: i32 = 100    # Exported constant
```

### 2.3 Name Matching Rules

Filename to type name conversion:

| Filename | Matches Type |
|----------|--------------|
| `test_case.spl` | `TestCase` (snake_case → PascalCase) |
| `string_interner.spl` | `StringInterner` |
| `http_client.spl` | `HttpClient` |
| `io.spl` | `Io` or `IO` |
| `mod.spl` | (special: module re-exports only) |

**Matching algorithm:**
```
filename_to_type(name):
    1. Remove .spl extension
    2. Split by underscore
    3. Capitalize first letter of each part
    4. Join without separator

    "test_case" → ["test", "case"] → ["Test", "Case"] → "TestCase"
```

### 2.4 Visibility by Declaration Type

| Declaration | Default Visibility | Can Override |
|-------------|-------------------|--------------|
| `class` (name matches file) | **Public** | Yes (`private class`) |
| `class` (name differs) | Private | Yes (`public class`) |
| `struct` | Same as class | Yes |
| `enum` | Same as class | Yes |
| `fn` | Private | Yes (`public fn`) |
| `val` | Private | Yes (`public val`) |
| `var` | Private | Yes (`public var`) |
| `type` alias | Private | Yes (`public type`) |

### 2.5 Top-Level `val` Support

With this design, top-level `val` becomes possible:

```simple
# file: constants.spl

# Private module constants (default)
val TEST_STATUS_PENDING: i32 = 0
val TEST_STATUS_PASSED: i32 = 2
val TEST_STATUS_FAILED: i32 = 3

# Explicitly public constant
public val MAX_TEST_COUNT: i32 = 10000

# Auto-public type (matches filename)
class Constants:
    # Empty class just to have a public anchor, or...
    pass

# Alternative: use enum for public constants
public enum TestStatus:
    Pending = 0
    Passed = 2
    Failed = 3
```

---

## 3. Detailed Rules

### 3.1 Class and Struct

```simple
# file: test_case.spl

# Auto-public: name matches filename
class TestCase:
    id: i32
    name: text

# Private: name doesn't match
class TestCaseBuilder:
    case: TestCase

# Explicit public override
public class TestCaseError:
    message: text

# Explicit private (redundant but allowed)
private class InternalState:
    data: [i32]
```

### 3.2 Functions

```simple
# file: test_case.spl

# Private by default
fn validate_name(name: text) -> bool:
    name.len() > 0

# Explicit public
public fn create_test_case(name: text) -> TestCase:
    TestCase(id: 0, name: name)

# Factory functions - often want these public
public fn TestCase_create(id: i32, name: text) -> TestCase:
    TestCase(id: id, name: name)
```

### 3.3 Impl Blocks

Impl blocks inherit visibility context from their target type:

```simple
# file: test_case.spl

class TestCase:       # Auto-public
    id: i32

impl TestCase:
    # Methods on public type are public by default
    fn get_id() -> i32:
        self.id

    # Can mark individual methods private
    private fn internal_validate():
        ...

class Helper:         # Private
    data: i32

impl Helper:
    # Methods on private type are private
    fn process():     # Private (type is private)
        ...
```

### 3.4 Module Files (mod.spl)

Special handling for `mod.spl` files:

```simple
# file: core/mod.spl

# mod.spl is for re-exports only
# No auto-public type (no type named "Mod")

# Re-export public items from submodules
public use core.types.TestCase
public use core.constants.TEST_STATUS_PASSED

# Or re-export everything
public use core.types.*
```

### 3.5 Nested Types

Nested types follow their parent's visibility:

```simple
# file: parser.spl

class Parser:           # Auto-public
    class Token:        # Public (nested in public type)
        kind: i32

    private class State:  # Private (explicit)
        pos: i32
```

---

## 4. Warnings and Errors

### 4.1 Phase 1: Warnings (Current Implementation)

**Backward Compatible:** All access allowed, but warn on non-public access

```
WARNING[W0401]: Accessing private type 'Helper' from outside module
  --> src/app/other.spl:5:10
   |
 5 | use test_case.Helper
   |     ^^^^^^^^^^^^^^^^ 'Helper' is not exported from 'test_case.spl'
   |
   = note: Type 'Helper' doesn't match filename and lacks 'pub' modifier
   = help: Add 'pub class Helper' in test_case.spl to export it
   = note: This will become an error in a future release
```

**Key Points:**
- ✅ Code still compiles and runs
- ⚠️ Warnings show what will break later
- 🔧 Users have time to add `pub` keywords

### 4.2 Phase 2: Enforcement (Future)

After migration period:
- Warnings become errors
- Private access is blocked

```
ERROR[E0403]: Type 'Helper' is private
  --> src/app/other.spl:5:10
   |
 5 | val h: Helper = ...
   |        ^^^^^^ private type
   |
   = note: 'Helper' is defined in 'test_case.spl' but not exported
   = help: Add 'pub class Helper' in test_case.spl to export it
```

### 4.3 Warning Codes

| Code | Description |
|------|-------------|
| W0401 | Implicitly public type (name doesn't match file) |
| W0402 | Implicitly public function |
| W0403 | Implicitly public constant |
| W0404 | Redundant visibility modifier |
| E0403 | Accessing private item from outside module |
| E0404 | Cannot make filename-matching type private |

---

## 5. Examples

### 5.1 Before and After

**Before (current workaround):**
```simple
# file: core/constants.spl

# Can't do this:
# val TEST_STATUS_PASSED: i32 = 2   # ERROR

# Must use functions:
fn get_test_status_passed() -> i32: 2
fn get_test_status_failed() -> i32: 3
fn get_proto_magic() -> i32: 0xAB
```

**After (with new visibility):**
```simple
# file: core/constants.spl

# Module-private constants (default)
val TEST_STATUS_PENDING: i32 = 0
val TEST_STATUS_RUNNING: i32 = 1
val TEST_STATUS_PASSED: i32 = 2
val TEST_STATUS_FAILED: i32 = 3

# Public constants (explicit)
public val PROTO_MAGIC: i32 = 0xAB
public val PROTO_VERSION: i32 = 0x01

# Auto-public type for grouped constants
class Constants:
    static fn status_passed() -> i32: TEST_STATUS_PASSED
    static fn proto_magic() -> i32: PROTO_MAGIC
```

### 5.2 Complete Module Example

```simple
# file: test_case.spl

# ===== Private Constants =====
val DEFAULT_TIMEOUT_MS: i64 = 5000
val MAX_NAME_LENGTH: i32 = 256

# ===== Public Constants =====
public val TEST_VERSION: i32 = 1

# ===== Auto-Public Type (matches filename) =====
class TestCase:
    id: i32
    name: text
    status: i32
    duration_ms: i64

impl TestCase:
    fn is_passed() -> bool:
        self.status == 2

    fn is_failed() -> bool:
        self.status == 3

# ===== Private Helper Type =====
class TestCaseValidator:
    fn validate(tc: TestCase) -> bool:
        tc.name.len() > 0 and tc.name.len() < MAX_NAME_LENGTH

# ===== Public Factory Function =====
public fn TestCase_create(id: i32, name: text) -> TestCase:
    TestCase(id: id, name: name, status: 0, duration_ms: 0)

# ===== Private Helper Function =====
fn generate_id() -> i32:
    # Internal implementation
    0
```

### 5.3 Importing

```simple
# file: test_runner.spl

# Import public items
use core.test_case.TestCase           # OK - auto-public
use core.test_case.TestCase_create    # OK - explicit public
use core.test_case.TEST_VERSION       # OK - explicit public

# These would fail:
# use core.test_case.TestCaseValidator  # ERROR - private type
# use core.test_case.DEFAULT_TIMEOUT_MS # ERROR - private constant
# use core.test_case.generate_id        # ERROR - private function
```

---

## 6. Implementation Plan

### 6.1 Compiler Changes

| Phase | Task | Effort |
|-------|------|--------|
| 1 | Parse `public`/`private` keywords | 4h |
| 2 | Track visibility in HIR | 8h |
| 3 | Filename-to-type matching logic | 4h |
| 4 | Visibility checking in type checker | 8h |
| 5 | Warning generation (W0401-W0404) | 4h |
| 6 | Enable top-level `val` parsing | 4h |
| 7 | Error generation (E0403-E0404) | 4h |
| **Total** | | **36h** |

### 6.2 Rollout Strategy

| Phase | Behavior |
|-------|----------|
| **Current** | Parse `pub`/`pri`, track visibility, emit W0401 warnings (access still allowed) |
| **Next** | Top-level `val`/`var` enabled, continue warnings |
| **Later** | Additional warning refinements, migration tools |
| **Future** | **Breaking:** Private access blocked (W0401 becomes E0403) |

### 6.3 Migration Tool

```bash
# Analyze codebase for visibility issues
simple lint --check-visibility src/

# Auto-add explicit modifiers
simple fix --add-visibility src/

# Preview changes
simple fix --add-visibility --dry-run src/
```

---

## 7. Alternatives Considered

### 7.1 Export Lists (Rejected)

```simple
# Explicit export list at top of file
export TestCase, TestCase_create, TEST_VERSION

class TestCase: ...
```

**Rejected because:** Duplicates information, easy to get out of sync.

### 7.2 Capitalization-Based (Rejected)

```simple
# Go-style: capitalized = public
class TestCase: ...    # Public
class helper: ...      # Private (lowercase)
```

**Rejected because:** Conflicts with Simple's naming conventions.

### 7.3 All Private by Default (Modified)

Original proposal was all private by default, but filename-matching auto-public:
- Encourages good organization
- Reduces boilerplate for common case
- Still allows explicit `public` for exceptions

---

## 8. FAQ

**Q: Can I have multiple public types in one file?**
A: Yes, use explicit `public` keyword.

**Q: What if filename doesn't follow snake_case?**
A: Matching is case-insensitive after conversion. `TestCase.spl` matches `TestCase`.

**Q: Can I make the filename-matching type private?**
A: Warning in v0.x, error in v1.0. If you want it private, rename the file.

**Q: How does this affect existing code?**
A: Warnings only initially. Use `simple fix --add-visibility` to migrate.

**Q: What about `impl` for external types?**
A: Impl blocks for types defined elsewhere follow normal rules (methods are public if explicitly marked).

---

## 9. References

- Rust visibility: https://doc.rust-lang.org/reference/visibility-and-privacy.html
- Go exported identifiers: https://go.dev/ref/spec#Exported_identifiers
- Kotlin visibility: https://kotlinlang.org/docs/visibility-modifiers.html
