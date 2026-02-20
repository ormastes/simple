# SDoctest Enforcement for Public APIs - Quick Reference

## The Rules

**Grouped items** (under a comment header) → At least **ONE** SDoctest for the group
**Non-grouped items** → **EACH** item needs its own SDoctest

## How to Document Public APIs in __init__.spl

### Format 1: Grouped Items (Recommended)

```simple
# File operations
#   - file_read
#   - file_write
#   - file_exists
```

**SDoctest requirement**: Write at least ONE example using ANY of these functions:

````markdown
# Example in README.md or doc/guide/*.md

```simple
use std.io.{file_read}

val content = file_read("example.txt")
print content
```
````

### Format 2: Non-grouped Items

```simple
# Public API:
#   - describe
#   - it
#   - expect
```

**SDoctest requirement**: Each function needs its own example.

### Format 3: Use Statements (Auto-detected as groups)

```simple
use std.spec.{describe, it, expect}
use std.spec.{before, after, before_each, after_each}
```

**SDoctest requirement**: One example per `use` line (each forms a group).

## Checking Coverage

### Programmatic Check

```simple
use doc_coverage.analysis.init_parser.{parse_init_file}
use doc_coverage.analysis.group_sdoctest.{check_group_sdoctest}
use doc_coverage.analysis.sdoctest_coverage.{load_sdoctest_blocks}

# 1. Parse __init__.spl
val result = parse_init_file("src/lib/io/__init__.spl")
val groups = result.0
val individual_items = result.1

# 2. Load all sdoctest blocks from docs
val blocks_data = load_sdoctest_blocks()
val sdoctest_blocks = blocks_data.1  # (names, codes)

# 3. Check group coverage
for group in groups:
    val has_coverage = check_group_sdoctest(group, sdoctest_blocks)
    if not has_coverage:
        print "❌ Group '{group.group_name}' missing SDoctest coverage"
        print "   Items: {group.items}"

# 4. Check individual item coverage
for item in individual_items:
    val has_coverage = _is_in_sdoctests(item.name, sdoctest_blocks)
    if not has_coverage:
        print "❌ Function '{item.name}' missing SDoctest"
```

### CLI Check (Future)

```bash
# Once integrated with CLI:
bin/simple doc-coverage --check-public-api
bin/simple build --enforce-public-sdoctest
```

## Best Practices

### 1. Group Related Functions

✅ **Good** (Grouped - needs 1 test total):
```simple
# String operations
#   - str_upper
#   - str_lower
#   - str_trim
```

❌ **Bad** (Ungrouped - needs 3 tests):
```simple
# Public API:
#   - str_upper
#   - str_lower
#   - str_trim
```

### 2. Write Minimal, Focused Examples

```markdown
## String Operations

Basic string manipulation:

```simple
use std.text.{str_upper, str_lower}

val text = "Hello World"
print str_upper(text)  # "HELLO WORLD"
print str_lower(text)  # "hello world"
```
```

This ONE example covers both `str_upper` and `str_lower` in the group.

### 3. Place Examples in Logical Locations

- **README.md** - High-level API overview
- **doc/guide/**.md - Detailed usage guides
- **Inline docstrings** - Function-specific examples (future)

### 4. Use `:tag` Modifiers for Categorization

````markdown
```simple:tag=stdlib:string
use std.text.{split, join}
val parts = split("a,b,c", ",")
val result = join(parts, "|")  # "a|b|c"
```
````

## Common Patterns

### Pattern 1: Testing Framework API

```simple
# BDD Test Organization
#   - describe
#   - context
#   - it
```

**One test covers all**:
````markdown
```simple
use std.spec.{describe, context, it}

describe "Calculator":
    context "addition":
        it "adds numbers":
            # test code
```
````

### Pattern 2: I/O Operations

```simple
# File Operations
#   - file_read
#   - file_write
#   - file_exists
#
# Directory Operations
#   - dir_create
#   - dir_list
```

**Two examples needed** (one per group):
````markdown
File example:
```simple
use app.io.{file_write, file_read}
file_write("test.txt", "content")
val data = file_read("test.txt")
```

Directory example:
```simple
use app.io.{dir_create, dir_list}
dir_create("mydir")
val files = dir_list("mydir")
```
````

### Pattern 3: Math Utilities (ungrouped)

```simple
# Public API:
#   - sqrt
#   - pow
#   - abs
```

**Three examples needed** (one per function).

## Files to Edit

### 1. Update __init__.spl
```
src/lib/mymodule/__init__.spl
```

### 2. Add SDoctest Examples
```
README.md                    # For main APIs
doc/guide/mymodule.md        # For detailed guides
```

### 3. Run Tests
```bash
bin/simple test test/unit/app/doc_coverage/init_parser_spec.spl
```

## Integration Checklist

- [ ] Parse all `__init__.spl` files in `src/`
- [ ] Load SDoctest blocks from all docs
- [ ] Match groups to coverage
- [ ] Match individual items to coverage
- [ ] Generate warnings for missing coverage
- [ ] Add to `bin/simple stats` output
- [ ] Add `--enforce-public-sdoctest` CLI flag
- [ ] Update threshold system
- [ ] Add to CI/CD pipeline

## See Also

- `PUBLIC_API_SDOCTEST_IMPLEMENTATION.md` - Technical implementation details
- `doc/guide/documentation_coverage.md` - Overall doc coverage system
- `src/app/doc_coverage/` - Source code
