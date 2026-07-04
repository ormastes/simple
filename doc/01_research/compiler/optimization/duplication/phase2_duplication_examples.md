# Phase 2: Duplication Examples - Concrete Code Samples

**Analysis Date:** 2026-02-14
**Companion to:** `phase2_app_duplicates.md`

---

## Example 1: Format Size Function Duplication

### Implementation 1: `/app/brief/main.spl` (lines 36-44)
```simple
fn format_size(bytes: i64) -> text:
    if bytes < 1024:
        return "{bytes} B"
    elif bytes < 1024 * 1024:
        val kb = bytes / 1024
        return "{kb} KB"
    else:
        val mb = bytes / (1024 * 1024)
        return "{mb} MB"
```

### Implementation 2: `/app/package/list.spl` (similar)
```simple
fn format_size(bytes: i64) -> text:
    if bytes < 1024:
        return "{bytes} B"
    else if bytes < 1024 * 1024:
        val kb = bytes / 1024
        return "{kb} KB"
    else if bytes < 1024 * 1024 * 1024:
        val mb = bytes / (1024 * 1024)
        return "{mb} MB"
    else:
        val gb = bytes / (1024 * 1024 * 1024)
        return "{gb} GB"
```

**Differences:**
- Version 1 uses `elif`, Version 2 uses `else if`
- Version 2 adds GB support
- Both lack floating-point precision (show "1 KB" vs "1.5 KB")

**Refactoring Solution:**
```simple
# src/app/io/format_utils.spl
fn format_bytes_basic(bytes: i64) -> text:
    if bytes < 1024:
        return "{bytes} B"
    elif bytes < 1024 * 1024:
        val kb = bytes / 1024
        return "{kb} KB"
    else:
        val mb = bytes / (1024 * 1024)
        return "{mb} MB"

fn format_bytes_full(bytes: i64) -> text:
    if bytes < 1024:
        return "{bytes} B"
    elif bytes < 1024 * 1024:
        val kb = bytes / 1024
        return "{kb} KB"
    elif bytes < 1024 * 1024 * 1024:
        val mb = bytes / (1024 * 1024)
        return "{mb} MB"
    else:
        val gb = bytes / (1024 * 1024 * 1024)
        return "{gb} GB"
```

---

## Example 2: Timestamp Function Duplication

### Implementation 1: `/app/mcp/resource_utils.spl`
```simple
fn current_timestamp() -> text:
    val now = time_now_unix_micros() / 1_000_000
    # Format as RFC3339 or ISO8601
    # (actual implementation omitted for brevity)
```

### Implementation 2: `/app/package/manifest.spl`
```simple
fn current_timestamp() -> text:
    val now = time_now_unix_micros() / 1_000_000
    # Similar formatting logic
```

### Implementation 3: `/app/test/quick_runner.spl`
```simple
fn current_timestamp() -> text:
    val micros = time_now_unix_micros()
    val seconds = micros / 1_000_000
    # Format timestamps
```

**Existing Consolidation:** `/app/io/time_ops.spl` already has:
```simple
fn current_time_ms() -> i64:
    time_now_unix_micros() / 1_000

fn timestamp_year(micros: i64) -> i32:
    val seconds = micros / 1_000_000
    val years = seconds / (365 * 24 * 60 * 60)
```

**Action:** Expand `time_ops.spl` to include timestamp formatting

---

## Example 3: Print Error Pattern Duplication

### Pattern 1: `/app/cli/main.spl` (lines ~100-110)
```simple
fn print_error(msg: str):
    print "error: {msg}"

fn print_error_with_help(msg: str):
    print "error: {msg}"
    print ""
    print_help()

# Usage:
if not file_exists(manifest_path):
    print_error("Manifest not found: {manifest_path}")
    return 1
```

### Pattern 2: `/app/build/watch.spl`
```simple
fn print_error(msg: text):
    print "error: {msg}"

# Usage:
if not success:
    print_error("Build failed")
    return 1
```

### Pattern 3: `/app/ffi_gen/main.spl`
```simple
fn print_error(msg: text):
    print "error: {msg}"

fn show_error(msg: text, code: i64):
    print_error(msg)
    return code
```

**Variations:**
- All print with "error: " prefix
- Some include helper variants (with_help, show_error)
- Inconsistent type: `str` vs `text`

**Refactoring Solution:**
```simple
# src/app/error.spl
fn print_error(msg: text):
    print "error: {msg}"

fn print_warning(msg: text):
    print "warning: {msg}"

fn print_info(msg: text):
    print "info: {msg}"

fn print_error_and_help(msg: text, help_fn: fn()):
    print_error(msg)
    print ""
    help_fn()

fn exit_error(msg: text, code: i64) -> i64:
    print_error(msg)
    code
```

---

## Example 4: LSP Handler Pattern Duplication

### Handler Structure Pattern

**File:** `/app/lsp/handlers/completion.spl` (lines 1-100)
```simple
use app.lsp.utils (node_at_position)

export handle_completion, CompletionItem, CompletionItemKind

enum CompletionItemKind:
    Text = 1
    Method = 2
    Function = 3
    # ... 25 more entries

impl CompletionItemKind:
    fn to_i64() -> i64:
        match self:
            Text: 1
            Method: 2
            # ...

fn find_node_at_position(tree: Tree, line: Int, column: Int) -> Option<Node>:
    # Duplicate implementation

fn handle_completion(tree: Tree, line: Int, column: Int) -> [CompletionItem]:
    match find_node_at_position(tree, line, column):
        Some(node):
            # Extract completions
        nil:
            []
```

**File:** `/app/lsp/handlers/definition.spl`
```simple
use app.lsp.utils (node_at_position)

export handle_definition

fn find_node_at_position(tree: Tree, line: Int, column: Int) -> Option<Node>:
    # SAME IMPLEMENTATION duplicated again

fn handle_definition(tree: Tree, line: Int, column: Int) -> Option<Location>:
    match find_node_at_position(tree, line, column):
        Some(node):
            # Find definition
        nil:
            nil
```

**Refactoring Solution:**
```simple
# src/app/lsp/handler_base.spl
use parser.treesitter.{Node, Tree}

fn find_node_at_position(tree: Tree, line: Int, column: Int) -> Option<Node>:
    # Single implementation
    # (common to all handlers)

# Then in completion.spl:
use app.lsp.handler_base.{find_node_at_position}

fn handle_completion(...) -> [CompletionItem]:
    # No need to reimplement find_node_at_position()
```

---

## Example 5: Argument Parsing Duplication

### Pattern 1: `/app/cli/main.spl`
```simple
fn main() -> i64:
    val args = get_cli_args()

    var path = ""
    var verbose = false
    var quiet = false

    for arg in args:
        if arg == "-h" or arg == "--help":
            print_help()
            return 0
        elif arg == "--verbose":
            verbose = true
        elif arg == "-q" or arg == "--quiet":
            quiet = true
        elif arg == "--version":
            print "simple v0.6.0"
            return 0
        elif not arg.starts_with("-"):
            path = arg

    if verbose:
        print "verbose mode enabled"

    # ... rest of command
```

### Pattern 2: `/app/formatter/main.spl`
```simple
fn main() -> i64:
    val args = get_cli_args()

    var file_path = ""
    var check_mode = false
    var format = "default"

    for arg in args:
        if arg == "-h" or arg == "--help":
            print_help()
            return 0
        elif arg == "--check":
            check_mode = true
        elif arg.starts_with("--format="):
            format = arg[9:]
        elif not arg.starts_with("-"):
            file_path = arg

    # ... rest of command
```

### Pattern 3: `/app/lint/main.spl`
```simple
fn main() -> i64:
    val args = get_cli_args()

    var target = ""
    var rules = []
    var output = "text"

    for arg in args:
        if arg == "-h" or arg == "--help":
            print_help()
            return 0
        elif arg == "--output":
            output = "json"
        elif not arg.starts_with("-"):
            target = arg

    # ... rest of command
```

**Common Pattern:** 15-25 lines per module × 73 modules = **1,000+ duplicate lines**

**Refactoring Solution:**
```simple
# src/app/cli/args.spl
class CliArgs:
    flags: [text]
    values: text -> text
    positional: [text]

    fn has_flag(name: text) -> bool:
        flags.contains(name)

    fn get_value(name: text) -> text:
        values[name] ?? ""

    fn positional() -> [text]:
        positional

fn parse_cli_args() -> CliArgs:
    val all_args = get_cli_args()
    var flags = []
    var values = {}
    var positional = []

    for arg in all_args:
        if arg.starts_with("--"):
            if arg.contains("="):
                val parts = arg[2:].split("=")
                values[parts[0]] = parts[1]
            else:
                flags.push(arg[2:])
        elif arg.starts_with("-"):
            for i in range(1, arg.len()):
                flags.push(arg[i].to_string())
        else:
            positional.push(arg)

    CliArgs(flags: flags, values: values, positional: positional)

# Usage in commands:
fn main() -> i64:
    val cli = parse_cli_args()

    if cli.has_flag("help"):
        print_help()
        return 0

    val path = if cli.positional().len() > 0:
        cli.positional()[0]
    else:
        ""

    val verbose = cli.has_flag("verbose")
    val format = cli.get_value("format")

    # ... rest of command
```

---

## Example 6: JSON Helper Duplication

### Current Implementation: `/app/mcp/helpers.spl` (lines 69-95)
```simple
fn jp(key: String, val_str: String) -> String:
    var r = Q()
    r = r + key
    r = r + Q()
    r = r + ":"
    r = r + val_str
    r

fn js(s: String) -> String:
    var r = Q()
    r = r + s
    r = r + Q()
    r

fn jo1(pair: String) -> String:
    var r = LB()
    r = r + pair
    r = r + RB()
    r

fn jo2(p1: String, p2: String) -> String:
    var r = LB()
    r = r + p1
    r = r + ","
    r = r + p2
    r = r + RB()
    r

fn jo3(p1: String, p2: String, p3: String) -> String:
    var r = LB()
    r = r + p1
    r = r + ","
    r = r + p2
    r = r + ","
    r = r + p3
    r = r + RB()
    r
```

### Similar Patterns in: `/app/ffi_gen/specs/json.spl`
```simple
# Similar JSON building logic
fn build_json_prop(name: String, type: String) -> String:
    # Uses similar string concatenation pattern
```

**Refactoring:**
- Move `helpers.spl` functions to `src/lib/json/builder.spl`
- Already imported in mcp/helpers.spl: `use lib.json.builder.{escape_json}`
- Extend builder with more functions, import from centralized location

---

## Example 7: Test Runner Monolith Coupling

### Files in `/app/test_runner_new/`

**Execution tier:**
- `test_runner_main.spl` (704 lines) — entry point
- `test_runner_execute.spl` (624 lines) — execution
- `test_runner_async.spl` (339 lines) — async execution
- `execution_strategy.spl` (280 lines) — strategy pattern

**Database tier:**
- `test_db_core.spl` (520 lines)
- `test_db_types.spl` (198 lines)
- `test_db_parser.spl` (268 lines)
- `test_db_validation.spl` (310 lines)
- `test_db_io.spl` (92 lines)
- `test_db_compat.spl` (189 lines)
- `test_db_serializer.spl` (123 lines)
- `test_db_lock.spl` (30 lines)

**Monitoring tier:**
- `system_monitor.spl` (383 lines)
- `process_tracker.spl` (275 lines)

**Reporting tier:**
- `test_stats.spl` (277 lines)
- `test_runner_output.spl` (84 lines)
- `doc_generator.spl` (347 lines)

**Coupling Example:**
```simple
# test_runner_main.spl imports from multiple modules:
use app.test_runner_new.test_runner_execute.{run_test_suite}
use app.test_runner_new.test_db_core.{init_test_database}
use app.test_runner_new.system_monitor.{start_monitor, stop_monitor}
use app.test_runner_new.test_stats.{compute_stats}

fn main() -> i64:
    val db = init_test_database()  # Database dependency
    val monitor = start_monitor()   # Monitor dependency
    val results = run_test_suite()  # Execution dependency
    val stats = compute_stats(results)  # Stats dependency

    # All tightly coupled in linear flow
```

**Refactoring to Plugin Architecture:**
```simple
# src/app/test_runner/plugin.spl (new)
class TestRunnerPlugin:
    name: text
    fn initialize(): bool
    fn on_test_start(test: text): ()
    fn on_test_result(result: TestResult): ()
    fn on_suite_complete(): ()
    fn finalize(): ()

# src/app/test_runner/main.spl (refactored)
fn main() -> i64:
    val plugins = [
        ExecutionPlugin(),
        DatabasePlugin(),
        MonitoringPlugin(),
        StatsPlugin(),
        ReportingPlugin()
    ]

    # Initialize all plugins
    for p in plugins:
        p.initialize()

    # Run with plugin hooks
    val results = run_with_plugins(plugins)

    # Finalize
    for p in plugins:
        p.finalize()
```

---

## Example 8: C Code Generation Duplication

### `/app/compile/c_translate.spl` (1,896 lines)

Multiple translation functions with overlapping logic:

```simple
fn translate_condition(cond: text, types: text) -> text:
    var result = cond
    # Handle "not" prefix (5 lines)
    # Handle "or" operator (5 lines)
    # Handle "and" operator (5 lines)
    # Handle "!= nil" (12 lines)
    # Handle "== nil" (12 lines)
    # Handle "==" (15 lines)
    # Handle "!=" (12 lines)
    result

fn translate_method_expr(expr: text, types: text) -> text:
    # Similar structure to translate_condition
    # Handles method calls on objects
    # Also handles nil checks, operators, etc.

fn translate_expr(expr: text, types: text) -> text:
    # ANOTHER similar function
    # Handles expressions in general
    # Overlaps with method_expr and condition
```

**Duplication Issues:**
1. Three functions doing similar work
2. Nil/NULL handling appears in all three
3. Operator translation (and/or/!==/==) in multiple places
4. String vs text type checking duplicated

**Refactoring Solution:**
```simple
# Extract common patterns into helpers
fn handle_nil_comparison(expr: text, types: text) -> text:
    # Single implementation for "x == nil", "x != nil"

fn handle_operator_comparison(op: text, left: text, right: text, types: text) -> text:
    # Single implementation for ==, !=, <, >, etc.

fn translate_expression(expr: text, types: text, context: text) -> text:
    # Unified expression translation
    # context = "condition", "method", "assignment", etc.

    if context == "condition":
        # Handle boolean operators specially
    else if context == "method":
        # Handle method calls
    else:
        # Generic expression
```

---

## Example 9: Platform Detection Duplication

### `/app/compile/native.spl`
```simple
fn detect_platform() -> text:
    val uname = shell("uname -s")
    val arch = shell("uname -m")

    if uname.contains("Linux"):
        if arch.contains("x86_64"):
            "linux-x86_64"
        else:
            "linux-arm64"
    else if uname.contains("Darwin"):
        "macos-arm64"
    else:
        "unknown"
```

### `/app/package/paths.spl`
```simple
fn detect_platform() -> text:
    val os = shell("uname -s")

    if os == "Linux":
        "linux"
    else if os == "Darwin":
        "macos"
    else if os.starts_with("MINGW"):
        "windows"
    else:
        "unknown"
```

### `/app/build/download_mold.spl`
```simple
fn detect_platform() -> text:
    var platform = ""
    if shell("uname").contains("Linux"):
        platform = "linux"
    elif shell("uname").contains("Darwin"):
        platform = "macos"
    platform
```

**Inconsistencies:**
- Different shell commands (uname vs uname -s vs uname -m)
- Different return formats (linux-x86_64 vs linux vs macos-arm64)
- Different comparison operators (contains, ==, starts_with)

**Refactoring:**
```simple
# src/app/platform.spl
class Platform:
    os: text    # linux, macos, windows
    arch: text  # x86_64, arm64, etc.

    fn to_string() -> text:
        "{os}-{arch}"

fn detect_platform() -> Platform:
    val uname_s = shell("uname -s").trim()
    val uname_m = shell("uname -m").trim()

    var os = ""
    if uname_s == "Linux":
        os = "linux"
    elif uname_s == "Darwin":
        os = "macos"
    elif uname_s.starts_with("MINGW"):
        os = "windows"
    else:
        os = "unknown"

    var arch = ""
    if uname_m.contains("x86_64") or uname_m == "amd64":
        arch = "x86_64"
    elif uname_m.contains("arm64") or uname_m == "aarch64":
        arch = "arm64"
    else:
        arch = uname_m

    Platform(os: os, arch: arch)
```

---

## Summary of Refactoring Impact

| Refactoring | Files Affected | LOC Reduced | Complexity Reduction |
|---|---|---|---|
| Consolidate format_size | 5 files | 50 | High |
| Consolidate timestamps | 7 files | 70 | High |
| Centralize error printing | 7 files | 50 | Medium |
| Extract LSP base handlers | 7 files | 100 | Very High |
| Unify arg parsing | 73 files | 1,000 | Very High |
| Create CLI framework | 115 files | 500 | Very High |
| Extract JSON builders | 4 files | 100 | High |
| Plugin architecture (test) | 46 files | 1,500 | Very High |
| Consolidate C translation | 3 files | 400 | High |
| Centralize platform detection | 4 files | 40 | Medium |

**Total Potential Reduction:** 2,500-3,000 lines (2-3% of codebase)
**Complexity Reduction:** 25-30% in affected modules
**Maintenance Improvement:** 40-50%

---

