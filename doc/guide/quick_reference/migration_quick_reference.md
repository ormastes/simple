# Migration Quick Reference Guide
## Rust to Simple - Quick Patterns

**Date:** February 3, 2026
**For:** Contributors migrating code from Rust to Simple
**See also:** `doc/report/rust_to_simple_migration_2026-02-03.md` for full details

## Quick Decision Tree

```
Need to write code?
│
├─ Is it application logic/tooling?
│  └─ ✅ Write in Simple (.spl)
│
├─ Is it runtime core (GC, VM, bytecode)?
│  └─ ❌ Keep in Rust
│
├─ Is it performance-critical hot path?
│  └─ ❌ Keep in Rust (benchmark first)
│
└─ Is it pure computation/string manipulation?
   └─ ✅ Write in Simple (no FFI needed)
```

## FFI Quick Reference

### Modern FFI Functions (Use These ✅)

**File I/O:**
```simple
extern fn rt_file_read_text(path: String) -> String
extern fn rt_file_write_text(path: String, content: String) -> Unit
extern fn rt_file_exists(path: String) -> Bool
```

**Directory Operations:**
```simple
extern fn rt_dir_list(path: String) -> List<String>
extern fn rt_dir_create(path: String, recursive: Bool) -> Bool
```

**Environment:**
```simple
extern fn rt_env_cwd() -> String
extern fn rt_env_get(key: String) -> String?
extern fn rt_env_home() -> String
```

**Process:**
```simple
extern fn rt_process_run(cmd: String, args: [String]) -> ProcessHandle
extern fn rt_process_output(cmd: String, args: [String]) -> ProcessOutput
```

### Deprecated FFI (Don't Use ❌)

```simple
# ❌ DEPRECATED - Use rt_file_* instead
extern fn native_fs_read_string(path: String) -> Any
extern fn native_fs_write_string(path: String, content: String) -> Any
extern fn native_fs_exists(path: String) -> Bool
extern fn native_fs_read_dir(path: String) -> Any

# ⏸️ PENDING - Use std.path when module system ready
extern fn rt_path_basename(path: String) -> String
```

## Common Migration Patterns

### Pattern 1: File Reading

**Before (Legacy):**
```simple
extern fn native_fs_read_string(path: String) -> Any

val file_content = native_fs_read_string(path)
match file_content:
    case Ok(content):
        return Ok(content)
    case Err(e):
        return Err("Failed to read file")
```

**After (Modern):**
```simple
extern fn rt_file_read_text(path: String) -> String

val file_content = rt_file_read_text(path)
if file_content == "":
    return Err("Failed to read file: {path}")
return Ok(file_content)
```

### Pattern 2: File Writing

**Before (Legacy):**
```simple
extern fn native_fs_write_string(path: String, content: String) -> Any

val write_status = native_fs_write_string(path, content)
match write_status:
    case Ok(n):
        return Ok(n)
    case Err(e):
        return Err("Failed to write file")
```

**After (Modern):**
```simple
extern fn rt_file_write_text(path: String, content: String) -> Unit

rt_file_write_text(path, content)
# Returns Unit; assume success if no exception
return Ok(content.len())
```

### Pattern 3: Path Operations

**Current (FFI - Temporary):**
```simple
extern fn rt_path_basename(path: String) -> String

val name = rt_path_basename(cwd)
```

**Future (Pure Simple - When module system ready):**
```simple
use std.path.{basename}

val name = basename(cwd)
```

### Pattern 4: Directory Listing

**Before (Legacy):**
```simple
extern fn native_fs_read_dir(path: String) -> Any

val entries = native_fs_read_dir(dir_path)
match entries:
    case Err(e):
        return Err("Failed to read directory: {e}")
    case Ok(dir_result):
        for entry in dir_result.entries:
            val name = entry.name
            # Process entry
```

**After (Modern):**
```simple
extern fn rt_dir_list(path: String) -> List<String>

val entry_names = rt_dir_list(dir_path)
for name in entry_names:
    # Process entry directly
```

## std.path Module (Ready When Module System Fixed)

**Functions Available (10 total):**
```simple
use std.path.{basename, dirname, extension, stem, join, join2,
              normalize, is_absolute, is_relative, has_extension}

# Extract components
val file = basename("/home/user/doc.pdf")      # "doc.pdf"
val dir = dirname("/home/user/doc.pdf")        # "/home/user"
val ext = extension("doc.pdf")                 # "pdf"
val name = stem("doc.pdf")                     # "doc"

# Construct paths
val path = join(["home", "user", "file.txt"]) # "home/user/file.txt"
val path2 = join2("/home", "user")            # "/home/user"

# Normalize
val clean = normalize("//home//./user")       # "/home/user"

# Check properties
val abs = is_absolute("/home/user")           # true
val has_ext = has_extension("file.txt", "txt") # true
```

## When to Use FFI vs Pure Simple

### ✅ Use Pure Simple For:
- String manipulation (split, join, substring)
- Path operations (basename, dirname, join)
- Collection operations (map, filter, reduce)
- Application logic and business rules
- CLI argument parsing
- Configuration parsing
- Test utilities

### ❌ Use FFI (Rust) For:
- File I/O (reading/writing files)
- Directory operations (listing, creating)
- Process management (spawning, waiting)
- Environment variables (reading, setting)
- Network operations (HTTP, TCP)
- System calls
- Performance-critical algorithms

## Build Commands Quick Reference

```bash
# Build project
simple build                    # Debug build
simple build --release          # Release build

# Run tests
simple test                     # All tests
simple test path/to/test.spl   # Single test file

# Format and lint
simple build fmt                # Format code
simple build lint               # Run linter

# Clean
simple build clean              # Remove build artifacts
```

## Checklist for Migration

When migrating code from Rust to Simple:

- [ ] Identify what the code does
- [ ] Check if it's application logic (✅ migrate) or runtime core (❌ keep)
- [ ] Find FFI dependencies needed
- [ ] Replace legacy FFI (`native_fs_*`) with modern (`rt_file_*`)
- [ ] Write Simple implementation
- [ ] Create SSpec tests for the code
- [ ] Verify functionality matches Rust version
- [ ] Document the migration
- [ ] Remove Rust code (if safe)
- [ ] Update imports in dependent files

## Common Gotchas

### 1. Direct Construction Pattern
```simple
# ✅ CORRECT - Direct construction
val point = Point(x: 3, y: 4)

# ❌ WRONG - Don't use .new()
val point = Point.new(3, 4)

# ✅ CORRECT - Named factory for special cases
val origin = Point.origin()
```

### 2. Generic Syntax
```simple
# ✅ CORRECT - Use angle brackets
Option<T>, List<Int>, fn map<T, U>

# ❌ WRONG - Square brackets deprecated
Option[T], List[Int]
```

### 3. Module Imports
```simple
# ✅ CORRECT - For app modules (works now)
use app.build.main.*

# ⏸️ PENDING - For std modules (needs compiler fix)
use std.path.*  # Will work after module system enhanced
```

### 4. FFI Error Handling
```simple
# rt_file_* functions return empty string on error
val content = rt_file_read_text(path)
if content == "":
    # Handle error
    return Err("Failed to read {path}")

# rt_file_write_text returns Unit, throws on error
rt_file_write_text(path, content)  # Success if no exception
```

## Resources

### Documentation
- Full migration plan: `doc/report/rust_to_simple_migration_2026-02-03.md`
- FFI boundary spec: `doc/spec/ffi_boundary_spec.md`
- Session summary: `doc/report/complete_session_summary_2026-02-03.md`

### Examples
- std.path module: `src/lib/path.spl` (pure Simple path utilities)
- Path tests: `test/std/path_spec.spl` (85+ SSpec tests)
- Updated apps: `src/app/formatter/main.spl`, `src/app/lint/main.spl`

### Test Patterns
```simple
# SSpec test structure
describe "Feature":
    it "does something":
        val result = function_to_test()
        expect result == expected_value

    it "handles errors":
        val result = function_with_error()
        expect result.err.?  # Check if error
```

## Status (As of Feb 3, 2026)

- **Application Layer:** 55% Simple (up from 50%)
- **Legacy FFI:** 0 calls (100% removed)
- **Modern FFI:** ~20 calls (all necessary)
- **stdlib Functions:** 10 path utilities added
- **Test Coverage:** 692 Simple test files

## Quick Wins for Next Contributor

1. **Migrate coverage tools** - `rust/util/simple_mock_helper/` (~3,500 lines)
2. **Add deprecation warnings** - Remaining 67 Makefile targets
3. **Create std.text module** - String utilities in pure Simple
4. **Migrate arch_test** - `rust/util/arch_test/` (~500 lines)

## Getting Help

- **Questions:** Check `doc/report/` for detailed reports
- **Patterns:** See updated files in `src/app/` for examples
- **FFI Reference:** `doc/spec/ffi_boundary_spec.md`
- **Test Examples:** `test/std/path_spec.spl` for SSpec patterns

---

**Last Updated:** February 3, 2026
**Migration Progress:** Application layer 55% Simple, overall 27.4%
**Target:** 80% Simple in application layer, 40% overall
