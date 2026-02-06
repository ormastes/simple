# Script Migration Guide

**Guide for migrating Python/Bash scripts to Simple**

---

## Policy

**All scripts must be written in Simple (.spl), except for 3 bootstrap scripts:**

1. `script/build-bootstrap.sh` - GitHub Actions first build
2. `script/build-full.sh` - Release package builder
3. `script/install.sh` - End-user installer

These run before Simple runtime exists, so they must remain as Bash.

---

## Migration Process

### 1. Identify Script Category

Determine where the migrated script should live:

| Original Location | New Location | Example |
|-------------------|--------------|---------|
| `script/build/*.sh` | `src/app/build/*.spl` | `link-bins.sh` → `link_bins.spl` |
| `script/verify/*.sh` | `src/app/verify/*.spl` | `verify_features.sh` → `features.spl` |
| `script/*.py` | `src/app/<category>/*.spl` | `fix_ffi_calls.py` → `audit/ffi_analyzer.spl` |
| `script/profiling/*.sh` | `src/app/profiling/*.spl` | `profile-interpreter.sh` → `profile.spl` |

### 2. Create Script Structure

All executable scripts must have:

```simple
#!/usr/bin/env simple
# Brief description
# Migrated from: script/original/path.sh

use app.io
use app.utils.colors (success, error, warning, info)

export main, primary_function

fn main():
    # Entry point for CLI usage
    val result = primary_function()
    if not result:
        exit(1)

fn primary_function() -> bool:
    """Main logic - can be imported by other modules"""
    # Implementation here
    true
```

### 3. Common Patterns

#### File Operations

**Bash:**
```bash
if [ -f "$file" ]; then
    cat "$file"
fi
```

**Simple:**
```simple
if file_exists(file):
    file_read(file)
```

#### Process Execution

**Bash:**
```bash
output=$(command arg1 arg2)
exit_code=$?
```

**Simple:**
```simple
val (stdout, stderr, code) = process_run("command", ["arg1", "arg2"])
```

#### Shell Commands

**Bash:**
```bash
grep pattern file | awk '{print $2}'
```

**Simple:**
```simple
# Option 1: Use shell() for complex pipes
val result = shell("grep pattern file | awk '{print $2}'")
val output = result.stdout

# Option 2: Parse in Simple
val lines = file_read("file").split("\n")
val matched = lines.filter(\line: line.contains("pattern"))
```

#### Loops and Iteration

**Bash:**
```bash
for file in *.txt; do
    echo "Processing $file"
done
```

**Simple:**
```simple
val files = dir_list(".").filter(\f: f.ends_with(".txt"))
for file in files:
    print "Processing {file}"
```

#### Exit Codes

**Bash:**
```bash
if ! command; then
    echo "Error!"
    exit 1
fi
```

**Simple:**
```simple
val (_, _, code) = process_run("command", [])
if code != 0:
    print error("Error!")
    exit(1)
```

---

## Available SFFI Functions

All file/process operations available in `src/app/io/mod.spl`:

### File Operations
```simple
file_exists(path: text) -> bool
file_read(path: text) -> text
file_write(path: text, content: text) -> bool
file_append(path: text, content: text) -> bool
file_copy(src: text, dst: text) -> bool
file_delete(path: text) -> bool
file_size(path: text) -> i64
```

### Directory Operations
```simple
dir_create(path: text, recursive: bool) -> bool
dir_list(path: text) -> [text]
dir_remove(path: text, recursive: bool) -> bool
is_dir(path: text) -> bool
```

### Process Execution
```simple
process_run(cmd: text, args: [text]) -> (text, text, i64)
process_run_timeout(cmd: text, args: [text], timeout_ms: i64) -> (text, text, i32)
shell(command: text) -> ProcessResult
```

### Environment
```simple
cwd() -> text
home() -> text
env_get(key: text) -> text
getpid() -> i64
hostname() -> text
cpu_count() -> i64
```

### Time
```simple
time_now_unix_micros() -> i64
current_time_unix() -> i64
timestamp_year() -> i64
timestamp_month() -> i64
timestamp_day() -> i64
timestamp_hour() -> i64
timestamp_minute() -> i64
timestamp_second() -> i64
```

---

## Utility Modules

### colors.spl

ANSI terminal colors for output:

```simple
use app.utils.colors (success, error, warning, info)

print success("✅ Operation completed")
print error("❌ Operation failed")
print warning("⚠️  Warning message")
print info("ℹ️  Information")
```

Individual colors:
```simple
use app.utils.colors (red, green, blue, reset)

print "{red()}Error:{reset()} Something went wrong"
print "{green()}Success!{reset()}"
```

---

## Testing Strategy

### 1. Create SSpec Test File

Create `test/app/<category>/<script>_spec.spl`:

```simple
use sspec (describe, it, assert, assert_eq)
use app.build.link_bins (link_bins)
use app.io

describe "link_bins":
    it "creates directory if missing":
        # Test logic
        assert true

    it "handles errors gracefully":
        # Test error handling
        assert true
```

### 2. Integration Testing

Test with real files in temporary directory:

```simple
fn test_with_temp_dir():
    val temp_dir = "/tmp/test_{getpid()}"
    dir_create(temp_dir, recursive: true)

    # Run test
    # ...

    # Cleanup
    dir_remove(temp_dir, recursive: true)
```

### 3. Regression Testing

Compare output with original script:

```bash
# Run both versions side-by-side
./script/build/original.sh > /tmp/bash_output.txt
./src/app/build/migrated.spl > /tmp/simple_output.txt
diff /tmp/bash_output.txt /tmp/simple_output.txt
```

---

## Examples

### Example 1: Simple File Operation

**Before (Bash):**
```bash
#!/bin/bash
if [ ! -d "bin" ]; then
    mkdir -p bin
fi
cp src/file.txt bin/
```

**After (Simple):**
```simple
#!/usr/bin/env simple
use app.io

fn main():
    if not is_dir("bin"):
        dir_create("bin", recursive: true)
    file_copy("src/file.txt", "bin/file.txt")
```

### Example 2: Process Execution

**Before (Bash):**
```bash
#!/bin/bash
output=$(cargo build --release 2>&1)
if [ $? -ne 0 ]; then
    echo "Build failed: $output"
    exit 1
fi
```

**After (Simple):**
```simple
#!/usr/bin/env simple
use app.io
use app.utils.colors (error)

fn main():
    val (stdout, stderr, code) = process_run("cargo",
        ["build", "--release"])

    if code != 0:
        print error("Build failed: {stderr}")
        exit(1)
```

### Example 3: Log Processing

**Before (Python):**
```python
#!/usr/bin/env python3
import re

with open("log.txt") as f:
    for line in f:
        if re.match(r"\[ERROR\]", line):
            print(line.strip())
```

**After (Simple):**
```simple
#!/usr/bin/env simple
use app.io

fn main():
    val content = file_read("log.txt")
    val lines = content.split("\n")

    for line in lines:
        if line.starts_with("[ERROR]"):
            print line.trim()
```

---

## Common Pitfalls

### 1. Shell Escaping

**Problem:** String interpolation doesn't escape shell characters

**Solution:** Use process_run() instead of shell() for user input:

```simple
# ❌ UNSAFE - subject to shell injection
val user_file = get_user_input()
shell("cat '{user_file}'")

# ✅ SAFE - no shell interpretation
process_run("cat", [user_file])
```

### 2. Exit Codes

**Problem:** Shell scripts use $? for exit codes, Simple uses return values

**Solution:** Check third element of tuple:

```simple
val (stdout, stderr, code) = process_run("command", [])
if code != 0:
    # Handle error
```

### 3. Path Handling

**Problem:** Relative paths in scripts can break

**Solution:** Use absolute paths or cwd():

```simple
val script_dir = cwd()
val project_root = "{script_dir}/../.."
```

---

## Checklist

Before considering a migration complete:

- [ ] Script runs without errors
- [ ] All functionality preserved
- [ ] Exit codes match original
- [ ] Output format matches (or improved)
- [ ] Error handling implemented
- [ ] Colors added for better UX
- [ ] SSpec tests written
- [ ] Shebang added (`#!/usr/bin/env simple`)
- [ ] File made executable (`chmod +x`)
- [ ] Original script kept temporarily for comparison
- [ ] Documentation updated

---

## See Also

- **CLAUDE.md** - Project coding standards
- **doc/report/script_migration_2026-02-06.md** - Migration status
- **src/app/io/mod.spl** - Available SFFI functions
- **src/app/utils/colors.spl** - Color utility module
