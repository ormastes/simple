# CLI Keyword Guide

The `cli` keyword provides declarative command-line argument parsing as a first-class language feature. It replaces manual argument-loop parsing with a concise block that generates a typed struct, automatic `--help`/`-h` and `--version`/`-v` handling, file detection, and subcommand routing.

---

## 1. Quick Start

```simple
cli Args:
    """A minimal example tool"""
    -v verbose = false   """Enable verbose output"""
    -o output = ""       """Output file path"""
    name = ""            """Name to greet"""

fn main():
    val args = Args.parse()
    if args.verbose:
        print "verbose mode on"
    print "Hello, {args.name}!"
```

Run it:

```bash
simple greet.spl --verbose --name Alice
# verbose mode on
# Hello, Alice!

simple greet.spl -h
# A minimal example tool
#
# Options:
#   -v, --verbose    Enable verbose output
#   -o, --output     Output file path
#       --name       Name to greet
```

---

## 2. Core Concepts

### Options with Defaults

Every field inside a `cli` block declares a command-line option. The **default value** is required and determines both the initial value and the inferred type.

```simple
cli Args:
    """My Application"""
    -v verbose = false    """Enable verbose output"""
    -o output = ""        """Output file path"""
    timeout = 0           """Timeout in seconds"""
    threshold = 0.5       """Score threshold"""
```

### Short Names

A short name is an optional single-character prefix before the field name, written as `-X`:

```simple
-v verbose = false    # --verbose or -v
-o output = ""        # --output or -o
timeout = 0           # --timeout only (no short form)
```

Short names support combined flags: `-vo out.txt` is equivalent to `--verbose --output out.txt`.

### Docstrings

Each field's trailing `"""..."""` becomes the help text shown in `--help` output. The block-level docstring at the top becomes the program description.

```simple
cli Args:
    """Process data files"""           # program description
    -f format = "json"  """Output format (json, csv, xml)"""
```

### Type Inference from Defaults

The type of each field is inferred from its default value:

| Default | Inferred Type | CLI Behavior |
|---------|--------------|--------------|
| `false` | `bool` | Flag (no value needed): `--verbose` sets to `true` |
| `true` | `bool` | Negated flag: `--no-verbose` sets to `false` |
| `""` | `text` | Requires a value: `--output file.txt` or `--output=file.txt` |
| `"default"` | `text` | Same as above, with a non-empty default |
| `0` | `i64` | Requires an integer value: `--timeout 30` |
| `0.0` | `f64` | Requires a float value: `--threshold 0.5` |

Boolean fields are parsed as **flags** (presence toggles the value). All other types are parsed as **options** that consume the next argument or use `=` syntax.

---

## 3. Subcommands

### Named Subcommands with Options

Use `sub name:` to define subcommands with their own options:

```simple
cli Args:
    """Simple Language Compiler"""
    -v verbose = false   """Enable verbose output"""

    sub run:
        """Run a source file"""
        -d debug = false     """Debug mode"""
        -w watch = false     """Watch for changes"""

    sub test:
        """Run test suite"""
        -l list_only = false """List tests without running"""
        -f filter = ""       """Filter test names"""
        --only-slow only_slow = false  """Run only slow tests"""
```

Access the active subcommand via `Args.command`:

```simple
fn main():
    val args = Args.parse()
    match args.command:
        case "run":
            if args.run.debug:
                print "debug mode"
            run_file(args.file_path)
        case "test":
            run_tests(args.test.filter, args.test.list_only)
```

### Pass-Through Subcommands

Subcommands that need no custom options can be listed together:

```simple
cli Args:
    """Build tool"""
    sub build, clean, lint
```

Pass-through subcommands collect all remaining arguments in `args.rest`.

### Default Subcommand

The `default: .name` directive specifies which subcommand runs when none is given:

```simple
cli Args:
    """My Application"""
    default: .run

    sub run:
        """Run the application"""
    sub test:
        """Run tests"""
```

When the user runs `simple myapp.spl` without a subcommand, it behaves as if `run` was specified.

---

## 4. File Detection

### The `file:` Directive

The `file:` directive tells the parser to detect file arguments by extension:

```simple
cli Args:
    """Simple compiler"""
    file: ".spl"
```

When a positional argument ends with `.spl`, it is captured as `args.file_path` (a `text` field). Other positional arguments go to `args.rest`. This means the user can write:

```bash
simple run src/main.spl --verbose
```

and `args.file_path` will be `"src/main.spl"` regardless of where it appears in the argument list.

Multiple extensions can be specified:

```simple
file: ".spl", ".smf", ".shs"
```

### The `prefetch:` Directive

When `prefetch: true` is set, the CLI framework issues a page cache warming read for detected files during argument parsing. This overlaps I/O with the remaining startup work so that by the time your program opens the file, it is likely already in memory.

```simple
cli Args:
    """Fast file processor"""
    file: ".spl"
    prefetch: true
```

This is a pure performance hint. It has no effect on correctness and can be omitted for tools where startup latency is not a concern.

---

## 5. Common Patterns

### Global Options + Subcommand Options

Global options are accessible on `args` directly, while subcommand options live under `args.<subcommand>`:

```simple
cli Args:
    """Simple CLI"""
    -v verbose = false       """Verbose output"""
    --backend backend = "auto"  """JIT backend"""

    sub compile:
        """Compile source"""
        -o output = ""       """Output path"""
        --target target = "" """Target architecture"""

    sub test:
        """Run tests"""
        -l list_only = false """List tests only"""
        --only-slow only_slow = false """Run only slow tests"""

fn main():
    val args = Args.parse()

    # Global options
    if args.verbose:
        print "Verbose mode enabled"

    match args.command:
        case "compile":
            compile(args.file_path, args.compile.output, args.compile.target)
        case "test":
            test(args.test.list_only, args.test.only_slow)
```

### Rest Args

Arguments not consumed by defined options or file detection are collected in `args.rest` as `[text]`:

```simple
cli Args:
    """Wrapper tool"""
    -v verbose = false  """Verbose"""
    file: ".spl"

fn main():
    val args = Args.parse()
    # Forward remaining args to another tool
    for arg in args.rest:
        print "extra: {arg}"
```

### Embedding in mod.spl

For multi-file applications, define the `cli` block in `mod.spl` so all submodules can import the generated `Args` struct:

```simple
# src/app/myapp/mod.spl
cli Args:
    """My Application v1.0"""
    -v verbose = false   """Verbose output"""
    file: ".spl"
    prefetch: true

    sub run:
        """Run application"""
    sub test:
        """Run tests"""
    sub build, clean

export Args
```

Then in submodules:

```simple
# src/app/myapp/runner.spl
use app.myapp.mod.{Args}

fn handle_run(args: Args):
    if args.verbose:
        print "Running..."
```

---

## 6. API Reference

### Generated Struct Fields

The `cli` block generates a struct with these fields:

| Field | Type | Description |
|-------|------|-------------|
| `args.<option>` | Inferred from default | Each declared option becomes a field |
| `args.command` | `text` | Name of the active subcommand (`""` if none) |
| `args.file_path` | `text` | Detected file path (if `file:` directive is set) |
| `args.rest` | `[text]` | Remaining unmatched arguments |
| `args.<subcommand>.<option>` | Inferred from default | Subcommand-specific options |

### Generated Functions

| Function | Signature | Description |
|----------|-----------|-------------|
| `Args.parse()` | `fn() -> Args` | Parse `cli_get_args()`, exit on error |
| `Args.parse_from(argv)` | `fn([text]) -> Args` | Parse from explicit argument list |
| `Args.help_text()` | `fn() -> text` | Return formatted help string |

### Implicit Flags

These are handled automatically and do not need to be declared:

| Flag | Short | Behavior |
|------|-------|----------|
| `--help` | `-h` | Print help text and exit with code 0 |
| `--version` | `-V` | Print version from `simple.sdn` or `SIMPLE_VERSION` env var, exit with code 0 |

---

## 7. Advanced Usage

### O(1) Lookup

The generated parser uses a hash map for option lookup, giving O(1) per-argument dispatch regardless of how many options are defined. This contrasts with the manual pattern of linear `if/elif` chains that scale linearly with the number of flags.

### simple.sdn Integration

The `cli` block reads project metadata from `simple.sdn` when present:

```sdn
name: "myapp"
version: "1.2.0"
description: "My application"
```

- `--version`/`-V` prints the version from `simple.sdn`
- The program name in `--help` output defaults to the `name` field
- The description falls back to `simple.sdn` if the `cli` block docstring is omitted

---

## 8. Migration

### Before: Manual `parse_global_flags` (~120 lines)

This is the pattern used in `src/app/cli/main.spl` before the `cli` keyword:

```simple
struct GlobalFlags:
    gc_log: bool
    gc_off: bool
    use_notui: bool
    max_recursion_depth: i64
    timeout_secs: i64
    execution_limit: i64
    backend: text
    force_interpret: bool
    no_jit: bool
    jit_threshold: i64

fn parse_global_flags(args: [text]) -> GlobalFlags:
    var gc_log = false
    var gc_off = false
    var use_notui = false
    var max_recursion_depth = 0
    var timeout_secs = 0
    var execution_limit = 0
    var backend = "auto"
    var force_interpret = false
    var no_jit = false
    var jit_threshold = 10

    var i = 0
    while i < args.len():
        val arg = args[i]
        if arg == "--gc-log":
            gc_log = true
        elif arg == "--gc-off":
            gc_off = true
        elif arg == "--notui":
            use_notui = true
        elif arg == "--interpret":
            force_interpret = true
        elif arg == "--no-jit":
            no_jit = true
        elif arg.starts_with("--jit-threshold="):
            val val_str = arg[16:]
            jit_threshold = val_str.to_int()
        elif arg == "--jit-threshold" and i + 1 < args.len():
            i = i + 1
            jit_threshold = args[i].to_int()
        elif arg.starts_with("--backend="):
            backend = arg[10:]
        elif arg == "--backend" and i + 1 < args.len():
            i = i + 1
            backend = args[i]
        elif arg.starts_with("--max-recursion-depth="):
            val val_str = arg[21:]
            max_recursion_depth = val_str.to_int()
        elif arg == "--max-recursion-depth" and i + 1 < args.len():
            i = i + 1
            max_recursion_depth = args[i].to_int()
        elif arg.starts_with("--timeout="):
            val val_str = arg[10:]
            timeout_secs = val_str.to_int()
        elif arg == "--timeout" and i + 1 < args.len():
            i = i + 1
            timeout_secs = args[i].to_int()
        elif arg.starts_with("--execution-limit="):
            val val_str = arg[18:]
            execution_limit = val_str.to_int()
        elif arg == "--execution-limit" and i + 1 < args.len():
            i = i + 1
            execution_limit = args[i].to_int()
        i = i + 1

    GlobalFlags(gc_log: gc_log, gc_off: gc_off, use_notui: use_notui,
        max_recursion_depth: max_recursion_depth, timeout_secs: timeout_secs,
        execution_limit: execution_limit,
        backend: backend, force_interpret: force_interpret,
        no_jit: no_jit, jit_threshold: jit_threshold)
```

Problems:
- Every option requires 2-4 lines (equality check, starts_with check, value extraction, index bump)
- The struct definition duplicates the variable declarations
- `--help` must be handled separately
- No automatic help text generation
- Easy to introduce off-by-one bugs in substring offsets (`arg[16:]`, `arg[21:]`, etc.)

### After: `cli` keyword (~40 lines)

```simple
cli Args:
    """Simple Language Compiler"""
    --gc-log gc_log = false             """Enable GC logging"""
    --gc-off gc_off = false             """Disable garbage collection"""
    --notui use_notui = false           """Disable TUI output"""
    --interpret force_interpret = false  """Force interpreter mode"""
    --no-jit no_jit = false             """Disable JIT compilation"""
    --jit-threshold jit_threshold = 10  """JIT compilation threshold"""
    --backend backend = "auto"          """JIT backend (auto, cranelift, llvm)"""
    --max-recursion-depth max_recursion_depth = 0  """Max recursion depth"""
    --timeout timeout_secs = 0          """Timeout in seconds"""
    --execution-limit execution_limit = 0  """Execution step limit"""

    file: ".spl"
    prefetch: true

    default: .run

    sub run:
        """Run a source file"""
    sub test:
        """Run test suite"""
        -l list_only = false  """List tests only"""
        --only-slow only_slow = false  """Run only slow tests"""
    sub compile:
        """Compile source"""
        -o output = ""  """Output file"""
        --target target = ""  """Target architecture"""
    sub build, watch, lint, fmt, fix, check
    sub mcp, lsp, verify, diff, stats

fn main():
    val args = Args.parse()
    match args.command:
        case "run":
            run_file(args.file_path)
        case "test":
            run_tests(args.test.list_only, args.test.only_slow)
        case "compile":
            compile(args.file_path, args.compile.output)
        case _:
            run_file(args.file_path)
```

Benefits:
- 3x fewer lines
- No manual index arithmetic or substring offsets
- Struct is generated automatically -- single source of truth
- `--help`/`-h` and `--version`/`-V` are free
- Docstrings flow directly into help output
- Type-safe: `args.timeout_secs` is `i64`, not `text`

---

## 9. Best Practices

1. **Always write docstrings.** Every option should have a `"""..."""` description. This is the single source of truth for both code documentation and `--help` output.

2. **Use explicit short names for common options.** Users expect `-v` for verbose, `-o` for output, `-f` for filter. Declare them explicitly rather than relying on auto-assignment.

3. **Prefer `cli` for all new applications.** The `cli` keyword replaces both the manual `while`-loop pattern and the library-based `cli_spec()`/`parse_cli_args()` approach. It is more concise and produces better error messages.

4. **Use `file:` for tools that process source files.** It enables positional file arguments without a `--file` flag, matching the natural `simple run src/main.spl` usage pattern.

5. **Enable `prefetch: true` for file-processing tools.** There is no downside and it improves startup latency when the file is not yet in the page cache.

6. **Group related subcommands.** Use `sub build, clean, lint` for simple pass-through subcommands and reserve `sub name:` blocks for subcommands that need their own options.

7. **Set `default:` for the primary action.** If your tool has an obvious default subcommand (like `run`), declare it so users can omit the subcommand name.

8. **Keep global options minimal.** Options that only apply to one subcommand should be declared inside that subcommand's block, not at the top level.
