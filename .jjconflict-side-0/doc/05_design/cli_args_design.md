# `cli` Keyword Design — Declarative CLI Argument Parsing

**Status:** Proposal
**Date:** 2026-03-03
**Scope:** Lexer, Parser, Interpreter, C Backend, Runtime

---

## 1. Problem Statement

### 1.1 Manual Parsing Proliferation

The main CLI entry point (`src/app/cli/main.spl`) dedicates approximately 120 lines to hand-written argument parsing:

- **`GlobalFlags` struct** (lines 205-218) — 13 fields, manually defined.
- **`parse_global_flags`** (lines 220-337) — 118-line while-loop with 20+ `elif` branches, handling `--key=value`, `--key value`, and bare flags, plus env-var fallback logic and SDN config reading.
- **`filter_internal_flags`** (lines 359-371) — a second pass that removes consumed global flags before forwarding to subcommands, requiring careful synchronization with `parse_global_flags` whenever a flag is added or removed.

Every new global flag requires coordinated edits in three places: the struct, the parser, and the filter.

### 1.2 Widespread Duplication Across Applications

A grep for manual `starts_with("--")` parsing across `src/app/` reveals **47 files** containing hand-rolled argument processing loops. Representative examples:

| File | What It Parses |
|------|---------------|
| `src/app/cli/main.spl` | GlobalFlags + 40+ subcommand dispatch |
| `src/app/io/cli_compile.spl` | `--backend=`, `--target=`, `--linker=`, `--format=`, `-o` |
| `src/app/compile/native.spl` | `--backend=`, linker detection |
| `src/app/cli/test_entry.spl` | `--list`, `--only-slow`, `--filter=`, `--tag=`, `--fail-fast` |
| `src/app/cli/lint_entry.spl` | `--fix`, path arguments |
| `src/app/build/` (via `src/compiler/80.driver/build/cli_entry.spl`) | subcommands: test, clean, lint, fmt, check, coverage, duplication, bootstrap |
| `src/app/coverage/main.spl` | `--verbose`, `--format=`, `--output=` |
| `src/app/search/main.spl` | `--type=`, `--path=` |
| `src/app/diagram/main.spl` | `--format=`, `--output=` |

Each file independently implements the `while i < args.len()` / `starts_with("--")` / `arg[N:]` pattern, with inconsistent error handling, no help generation, and no short-flag support.

### 1.3 Three Unused Libraries

The `src/lib/nogc_sync_mut/cli/` directory contains **three** separate argument-parsing implementations:

1. **`cli_parser.spl`** (439 lines) — `CliSpec` builder with `cli_spec_flag`, `cli_spec_option`, `cli_spec_positional`, `parse_cli_args`, `generate_help`. Full featured but verbose: defining 5 options requires ~30 lines of builder calls.

2. **`simple_parser_api.spl`** (355 lines) — `SimpleParser` struct with `flag()`, `option()`, `subcommand()` builder methods, `parse()` returning `Result<ParsedResult, text>`. Supports combined short flags (`-abc`). More ergonomic but still requires ~20 lines for 5 options.

3. **`parser.spl`** (100 lines) — Tuple-based parser (`create_parser`, `add_flag`, `add_option`). Fragile: accesses tuple fields by index (`parser[0]`, `parser[2]`).

Despite having three libraries available, **only `cli_util.spl`** (which provides `get_cli_args`, `has_flag`, `get_flag_value`) is actually imported by app code (43 files). Only `dashboard/main.spl` imports `cli_parser.spl`. Zero files use `simple_parser_api.spl` or `parser.spl` for real argument parsing. The libraries are too verbose to compete with the simplicity of a manual `if arg.starts_with("--verbose")` pattern.

### 1.4 The Core Insight

The fundamental problem is not missing library support — it is that **library-based CLI parsing will always be more verbose than the manual pattern it replaces**. A 5-option struct requires ~30 lines of builder calls versus ~15 lines of manual if/elif. The only way to be genuinely shorter is to move the declaration into the language syntax, where the compiler generates both the struct and the parser.

---

## 2. Proposed Syntax

### 2.1 Full Example

```simple
cli Args:
    """Simple Language Compiler"""
    -g gc_log = false       """Enable GC logging"""
    backend = "auto"        """JIT backend: auto|cranelift|llvm"""
    timeout = 0             """Execution timeout in seconds"""
    file: ".spl"
    prefetch: true
    default: .repl
    sub test:
        """Run test suite"""
        -l list_only = false  """List tests without running"""
        only_slow = false     """Run only slow tests"""
        filter = ""           """Filter tests by pattern"""
    sub build:
        """Build project"""
        release = false       """Release mode"""
        warn_docs = false     """Check documentation coverage"""
        target = ""           """Target architecture"""
    sub lint, fmt, fix, check
    sub compile:
        """Compile source file"""
        -o output = ""        """Output path"""
        target = ""           """Target architecture"""
        linker = ""           """Linker: mold|lld|ld"""
```

### 2.2 EBNF Grammar

```ebnf
cli_decl       = "cli" IDENT ":" NEWLINE INDENT cli_body DEDENT ;

cli_body       = [ docstring NEWLINE ]
                 { option_def NEWLINE }
                 { meta_def NEWLINE }
                 { sub_decl NEWLINE } ;

option_def     = [ short_flag ] IDENT "=" default_value [ docstring ] ;

short_flag     = "-" LETTER ;

default_value  = BOOL_LIT          (* false, true *)
               | STRING_LIT        (* "text" *)
               | INT_LIT           (* 0, 42 *)
               | FLOAT_LIT         (* 0.0, 3.14 *)
               | "[" type "]"      (* [text], [i64] *)
               ;

meta_def       = "file" ":" STRING_LIT       (* accepted file extension *)
               | "prefetch" ":" BOOL_LIT      (* OS-level prefetch of argv[1] *)
               | "default" ":" "." IDENT      (* default subcommand when no args *)
               ;

sub_decl       = "sub" IDENT { "," IDENT } [ ":" NEWLINE INDENT sub_body DEDENT ] ;

sub_body       = [ docstring NEWLINE ]
                 { option_def NEWLINE } ;

docstring      = '"""' TEXT '"""' ;
```

### 2.3 Syntax Rules

- **`cli Name:`** — declares a named CLI specification. `Name` becomes a struct type.
- **`option = default`** — option name, type inferred from default value. Long flag is `--option-name` (underscores become hyphens).
- **`-x option = default`** — explicit short flag `-x`.
- **`"""text"""`** — docstring for help generation. Top-level docstring is the program description. Per-option docstrings appear in help output.
- **`sub name:`** — subcommand with its own options. Subcommands inherit global options.
- **`sub a, b, c`** — bare subcommands (no additional options).
- **`file: ".spl"`** — declares accepted file extension for positional file arguments.
- **`prefetch: true`** — enables OS-level file prefetch on `argv[1]` (readahead/madvise).
- **`default: .repl`** — names the default action when invoked with no arguments.

---

## 3. Data Model

### 3.1 AST Representation

A new declaration kind `DECL_CLI = 13` uses the existing arena pools:

```
decl_tag[idx]            = 13  (DECL_CLI)
decl_name[idx]           = "Args"
decl_imports[idx][0]     = "Simple Language Compiler"   # top-level docstring
decl_field_names[idx]    = [                            # option metadata
    "gc_log|b|false|g|Enable GC logging",
    "backend|s|auto||JIT backend: auto|cranelift|llvm",
    "timeout|i|0||Execution timeout in seconds",
]
decl_field_types[idx]    = []                           # unused, types inferred from defaults
decl_field_defaults[idx] = []                           # unused, defaults encoded in field_names
decl_body_stmts[idx]     = [sub_idx_test, sub_idx_build, ...]  # subcommand decl indices
decl_type_params[idx]    = ["file:.spl", "prefetch:true", "default:.repl"]  # meta directives
```

### 3.2 Option Metadata Encoding

Each entry in `decl_field_names[]` is a pipe-delimited string:

```
"name|type_char|default|short|doc"
```

| Field | Description |
|-------|------------|
| `name` | Option identifier (e.g., `gc_log`) |
| `type_char` | `b` = bool, `s` = text, `i` = i64, `f` = f64, `a` = array |
| `default` | Default value as string |
| `short` | Single-letter short flag, or empty |
| `doc` | Docstring text, or empty |

This encoding avoids adding new arena arrays and fits within the existing `[[text]]` pool type.

### 3.3 Subcommand Encoding

Each subcommand is stored as a separate DECL_CLI node referenced from the parent's `decl_body_stmts[]`:

```
decl_tag[sub_idx]         = 13  (DECL_CLI)
decl_name[sub_idx]        = "test"
decl_imports[sub_idx][0]  = "Run test suite"
decl_field_names[sub_idx] = [
    "list_only|b|false|l|List tests without running",
    "only_slow|b|false||Run only slow tests",
]
```

Bare subcommands (`sub lint, fmt, fix, check`) are stored as DECL_CLI nodes with empty `decl_field_names[]`.

---

## 4. Type Inference Rules

The default value literal determines the option's runtime type:

| Default Value | Inferred Type | C Type | Example |
|--------------|---------------|--------|---------|
| `false` / `true` | `bool` | `int` | `gc_log = false` |
| `"text"` / `""` | `text` | `const char*` | `backend = "auto"` |
| `0` / `42` | `i64` | `int64_t` | `timeout = 0` |
| `0.0` / `3.14` | `f64` | `double` | `threshold = 0.5` |
| `[text]` | `[text]` | `SimpleArray*` | `tags = [text]` |
| `[i64]` | `[i64]` | `SimpleArray*` | `ports = [i64]` |

Bool options act as flags (presence toggles to `true`). Text/i64/f64 options consume the next argument as their value (supporting both `--key=value` and `--key value` forms).

---

## 5. Short Name Strategy

### 5.1 Resolution Order

1. **Explicit shorts win.** `-g gc_log` assigns `g` to `gc_log` unconditionally.
2. **Auto-assign first letter.** For options without explicit shorts, try the first character of the name. `backend` tries `b`.
3. **Skip on conflict.** If the first letter is already taken, the option gets no short flag. No fallback to second letter — keep it predictable.
4. **Reserved letters.** `-h` (help) and `-v` (version) are always reserved. Explicit `-h` or `-v` in a `cli` block is a compile error (E-CLI-005).

### 5.2 Example Resolution

Given:
```simple
-g gc_log = false
backend = "auto"
-b big_mode = false
timeout = 0
```

| Option | Explicit | Auto | Result |
|--------|----------|------|--------|
| `gc_log` | `-g` | - | `-g` |
| `backend` | - | `b` | conflict with `big_mode` -> **no short** |
| `big_mode` | `-b` | - | `-b` |
| `timeout` | - | `t` | `-t` |

---

## 6. O(1) Codegen Strategy

### 6.1 The Problem

Naive argument parsing iterates over all known options for each input argument: O(N*M) where N = argc and M = number of options. For CLIs with 20+ options, this adds measurable overhead on every invocation.

### 6.2 The Solution: Length-Dispatch

The C backend generates a nested switch on string length, then first character, then `memcmp`:

```c
// Generated from: cli Args: ... backend = "auto" ... timeout = 0 ...
static int parse_arg(const char* arg, int len, Args* out) {
    switch (len) {
        case 9:  // "--backend"
            if (arg[2] == 'b' && memcmp(arg, "--backend", 9) == 0) {
                // next arg is value
                return ARG_NEEDS_VALUE | ARG_IDX_BACKEND;
            }
            break;
        case 9:  // "--timeout"
            if (arg[2] == 't' && memcmp(arg, "--timeout", 9) == 0) {
                return ARG_NEEDS_VALUE | ARG_IDX_TIMEOUT;
            }
            break;
        case 8:  // "--gc-log"
            if (arg[2] == 'g' && memcmp(arg, "--gc-log", 8) == 0) {
                out->gc_log = 1;
                return ARG_CONSUMED;
            }
            break;
    }
    return ARG_UNKNOWN;
}
```

When multiple options share the same length, they are disambiguated by first-character switch within the length case:

```c
case 9:
    switch (arg[2]) {
        case 'b': if (memcmp(arg+3, "ackend", 6)==0) { ... } break;
        case 't': if (memcmp(arg+3, "imeout", 6)==0) { ... } break;
    }
    break;
```

### 6.3 `--key=value` Handling

For `=`-separated values, scan for `=` first, compute key length, then dispatch on key length:

```c
const char* eq = memchr(arg, '=', arg_len);
if (eq) {
    int key_len = eq - arg;
    const char* value = eq + 1;
    switch (key_len) {
        case 9: // "--backend"
            if (memcmp(arg, "--backend", 9) == 0) {
                out->backend = value;
                return ARG_CONSUMED;
            }
            break;
    }
}
```

### 6.4 Complexity

- **Per-argument:** O(1) — constant-time switch + single `memcmp`.
- **Total parsing:** O(argc) — single linear scan of `argv`.
- **No heap allocation** during parsing (all values are pointers into `argv` or static defaults).

---

## 7. Help Generation

### 7.1 Source of Truth

All help text is derived from the `cli` block's docstrings:

- Top-level `"""..."""` becomes the program description.
- Per-option `"""..."""` becomes the option's help line.
- Per-subcommand `"""..."""` becomes the subcommand description.

### 7.2 Generated Help Text

For the example in Section 2.1:

```
Simple Language Compiler

Usage: simple [options] [file.spl] [command]

Options:
  -g, --gc-log              Enable GC logging
      --backend=VALUE       JIT backend: auto|cranelift|llvm (default: auto)
      --timeout=N           Execution timeout in seconds (default: 0)

Commands:
  test       Run test suite
  build      Build project
  lint       Run linter
  fmt        Format code
  fix        Auto-fix issues
  check      Type check

Run 'simple <command> --help' for subcommand options.
```

### 7.3 C Backend: Static String Generation

The C backend emits help text as a static `const char[]` literal, avoiding runtime string concatenation:

```c
static const char HELP_TEXT[] =
    "Simple Language Compiler\n"
    "\n"
    "Usage: simple [options] [file.spl] [command]\n"
    "\n"
    "Options:\n"
    "  -g, --gc-log              Enable GC logging\n"
    "      --backend=VALUE       JIT backend: auto|cranelift|llvm (default: auto)\n"
    "      --timeout=N           Execution timeout in seconds (default: 0)\n"
    "\n"
    "Commands:\n"
    "  test       Run test suite\n"
    "  build      Build project\n"
    ;

void print_help(void) {
    fwrite(HELP_TEXT, 1, sizeof(HELP_TEXT) - 1, stdout);
}
```

### 7.4 Formatting Rules

- Short flag column: 6 characters (`  -g, ` or `      `)
- Long flag column: 24 characters (left-aligned)
- Description follows after the column
- Default values appended as `(default: VALUE)` for non-bool options
- Bool flags show no default (they default to `false` by definition)

---

## 8. Component Impact

### 8.1 Lexer — 1 New Keyword

File: `src/compiler/10.frontend/core/lexer.spl`

Add `TOK_KW_CLI` to the keyword table. The token value follows the existing numbering scheme (next available after `TOK_KW_MIXIN = 203`). `sub` is parsed as a contextual keyword within `cli` blocks only (not a global keyword).

```simple
val TOK_KW_CLI = 208
```

Impact: ~5 lines changed. One entry in the keyword lookup table.

### 8.2 Parser — New `parser_cli.spl`

File: `src/compiler/10.frontend/core/parser_cli.spl` (new)

Parses the `cli` block into DECL_CLI arena nodes. Called from the main parser's `parse_decl()` when `TOK_KW_CLI` is encountered.

Functions:
- `parse_cli_decl() -> i64` — top-level cli block
- `parse_cli_option() -> text` — single option line, returns pipe-encoded metadata
- `parse_cli_sub() -> i64` — subcommand block, returns child DECL_CLI index
- `parse_cli_meta() -> text` — meta directives (file, prefetch, default)

Estimated size: ~150 lines.

### 8.3 Interpreter — New `cli_eval.spl`

File: `src/compiler/95.interp/interpreter/cli_eval.spl` (new)

Evaluates DECL_CLI at runtime by generating a struct and a parsing function. When the interpreter encounters `DECL_CLI`:

1. Register a struct type named `Name` with fields matching the option names and inferred types.
2. Register a function `parse_Name(args: [text]) -> Name` that implements the while-loop parsing pattern.
3. Register a function `Name_help() -> text` that returns the formatted help string.

This means the interpreter expands `cli Args:` into the equivalent hand-written struct + parse function, then evaluates normally.

Estimated size: ~200 lines.

### 8.4 C Backend — New `cli_codegen.spl`

File: `src/compiler/70.backend/backend/cli_codegen.spl` (new)

Generates the O(1) switch-based parser described in Section 6. Emits:

- C struct definition for `Args`
- `parse_args(int argc, char** argv, Args* out)` with length-dispatch
- Static help text literal
- `print_help(void)` function
- Optional: `prefetch_file(const char* path)` wrapper around `posix_fadvise`/`readahead`

Estimated size: ~300 lines.

### 8.5 Runtime — Prefetch and Accessors

File: `src/runtime/runtime.c` (additions)

- `rt_prefetch_file(const char* path)` — calls `posix_fadvise(fd, 0, 0, POSIX_FADV_WILLNEED)` on Linux, `fcntl(fd, F_RDAHEAD, 1)` on macOS. Called at program start if `prefetch: true` is set and `argv[1]` matches the `file:` extension.
- `rt_parsed_args()` — returns a pointer to the parsed args struct (set during `main()` init).

Estimated size: ~30 lines.

---

## 9. Error Codes

| Code | Severity | Description |
|------|----------|------------|
| E-CLI-001 | Error | Duplicate option name within same `cli` or `sub` block |
| E-CLI-002 | Error | Duplicate subcommand name |
| E-CLI-003 | Error | Invalid default value type (must be literal) |
| E-CLI-004 | Error | Short flag must be a single ASCII letter |
| E-CLI-005 | Error | Short flag `-h` or `-v` is reserved (conflicts with built-in `--help`/`--version`) |
| E-CLI-006 | Error | Duplicate short flag assignment (two options claim the same letter) |
| E-CLI-007 | Warning | Option name shadows a parent `cli` block option in a `sub` block (the sub option takes precedence; parent option is inaccessible in that subcommand) |

Error messages follow the existing diagnostic format:

```
error[E-CLI-001]: duplicate option name 'verbose'
  --> src/app/cli/main.spl:15:5
   |
15 |     verbose = false
   |     ^^^^^^^ option 'verbose' already defined on line 8
```

---

## 10. Migration Path

### 10.1 Before: Manual Parsing (~120 lines)

```simple
struct GlobalFlags:
    gc_log: bool
    gc_off: bool
    backend: text
    timeout: i64
    force_interpret: bool

fn parse_global_flags(args: [text]) -> GlobalFlags:
    var gc_log = false
    var gc_off = false
    var backend = "auto"
    var timeout = 0
    var force_interpret = false
    var i = 0
    while i < args.len():
        val arg = args[i]
        if arg == "--gc-log":
            gc_log = true
        elif arg == "--gc-off":
            gc_off = true
        elif arg.starts_with("--backend="):
            backend = arg[10:]
        elif arg == "--backend" and i + 1 < args.len():
            i = i + 1
            backend = args[i]
        elif arg.starts_with("--timeout="):
            timeout = arg[10:].to_int()
        elif arg == "--timeout" and i + 1 < args.len():
            i = i + 1
            timeout = args[i].to_int()
        elif arg == "--interpret":
            force_interpret = true
        i = i + 1
    GlobalFlags(gc_log: gc_log, gc_off: gc_off, backend: backend,
        timeout: timeout, force_interpret: force_interpret)

fn filter_internal_flags(args: [text]) -> [text]:
    var result = []
    var skip_next = false
    for arg in args:
        if skip_next:
            skip_next = false
        elif arg == "--timeout" or arg == "--backend":
            skip_next = true
        elif not arg.starts_with("--gc") and arg != "--interpret":
            if not arg.starts_with("--backend=") and not arg.starts_with("--timeout="):
                result.push(arg)
    result
```

### 10.2 After: `cli` Keyword (~40 lines)

```simple
cli Args:
    """Simple Language Compiler"""
    -g gc_log = false         """Enable GC logging"""
    gc_off = false            """Disable garbage collection"""
    backend = "auto"          """JIT backend: auto|cranelift|llvm"""
    timeout = 0               """Execution timeout in seconds"""
    force_interpret = false    """Force interpreter mode"""
    file: ".spl"
    prefetch: true
    default: .repl
    sub test:
        """Run test suite"""
        -l list_only = false  """List tests without running"""
        only_slow = false     """Run only slow tests"""
        filter = ""           """Filter tests by pattern"""
        fail_fast = false     """Stop on first failure"""
    sub build:
        """Build project"""
        release = false       """Release mode"""
        warn_docs = false     """Check documentation coverage"""
    sub compile:
        """Compile source file"""
        -o output = ""        """Output path"""
        target = ""           """Target architecture"""
        linker = ""           """Linker: mold|lld|ld"""
    sub lint, fmt, fix, check, lex, watch, verify
    sub mcp, lsp, diff, query, info, stats
```

### 10.3 What Is Eliminated

| Component | Before | After |
|-----------|--------|-------|
| Struct definition | Manual, 13 fields | Generated from `cli` block |
| Parser function | 118 lines, 20+ elif branches | Generated O(1) switch |
| Filter function | 13 lines, must sync with parser | Eliminated (compiler knows which flags are global vs subcommand) |
| Help text | 120+ lines of `print` statements in `cli_helpers.spl` | Generated from docstrings |
| Short flags | Not supported | Automatic + explicit |
| `--key=value` support | Manual `starts_with` + substring | Generated |
| Error on unknown flag | Not implemented | Generated |
| Subcommand help | Separate functions per subcommand | Generated `<cmd> --help` |

### 10.4 Migration Strategy

1. **Phase 1:** Add `cli` keyword to lexer/parser/interpreter. All existing code unchanged.
2. **Phase 2:** Write `cli Args:` block in `src/app/cli/main.spl` alongside existing `GlobalFlags`. Both coexist. Validate output matches.
3. **Phase 3:** Remove `GlobalFlags`, `parse_global_flags`, `filter_internal_flags`, and the 120-line help text in `cli_helpers.spl`. Switch `main()` to use `Args.parse(get_cli_args())`.
4. **Phase 4:** Migrate individual `src/app/*/main.spl` files from manual parsing to local `cli` blocks, one at a time.

---

## 11. Key Decisions

### 11.1 Why Keyword, Not Macro or Library

| Approach | Lines for 5 options | Help gen | O(1) parse | Short flags | Type safety |
|----------|---------------------|----------|------------|-------------|-------------|
| Manual while-loop | ~35 | No | No | No | No |
| `cli_parser.spl` library | ~30 | Yes (runtime) | No | Yes | No (string keys) |
| `simple_parser_api.spl` library | ~20 | Yes (runtime) | No | Yes | No (string keys) |
| `cli` keyword | ~8 | Yes (static) | Yes | Yes | Yes (struct fields) |

The keyword approach is the only one that:
- Is shorter than manual code for any number of options.
- Generates a real struct with typed fields (no `parsed.get_option("name")` string lookups).
- Enables compile-time help text generation (no runtime string building).
- Enables O(1) argument dispatch in the C backend.
- Integrates with the existing documentation system (docstrings are already parsed).

A macro could achieve similar syntax but would require a macro expansion system that does not currently exist in Simple. The `mixin()` builtin parses code strings at runtime, which cannot generate C-backend-specific optimizations.

### 11.2 Arena Reuse Pattern

The design intentionally reuses existing arena arrays rather than adding new ones:

- `decl_field_names[]` stores pipe-encoded option metadata (avoiding new `decl_cli_options` array).
- `decl_body_stmts[]` stores subcommand indices (same as struct method body indices).
- `decl_type_params[]` stores meta directives (avoiding new `decl_cli_meta` array).
- `decl_imports[]` stores the top-level docstring (avoiding new `decl_cli_doc` array).

This follows the same pattern used by `DECL_CE` (computation expressions) which encodes CE-specific metadata in existing fields. Zero new arena arrays means zero impact on memory layout for programs that do not use `cli`.

### 11.3 File Layout

```
src/compiler/10.frontend/core/
    lexer.spl                  # +1 keyword (TOK_KW_CLI)
    parser_cli.spl             # NEW: ~150 lines
    parser.spl                 # +3 lines (call parse_cli_decl on TOK_KW_CLI)

src/compiler/95.interp/interpreter/
    cli_eval.spl               # NEW: ~200 lines
    eval.spl                   # +5 lines (DECL_CLI case in eval_decl)

src/compiler/70.backend/backend/
    cli_codegen.spl            # NEW: ~300 lines
    codegen.spl                # +5 lines (DECL_CLI case in emit_decl)

src/compiler/10.frontend/core/ast.spl
                               # +1 line: val DECL_CLI = 13

src/runtime/runtime.c          # +30 lines (prefetch helper)
```

Total new code: ~650 lines across 3 new files.
Total deleted code (after migration): ~250 lines from `main.spl` + ~120 lines from `cli_helpers.spl` help text + scattered manual parsing across `src/app/`.

### 11.4 Interaction with Existing `use std.cli` Libraries

The `cli` keyword does not replace or deprecate the existing libraries. Programs that prefer runtime-configurable argument parsing (e.g., plugin systems that add flags dynamically) should continue using `SimpleParser` or `CliSpec`. The `cli` keyword targets the common case of static, known-at-compile-time argument specifications.

---

## Appendix A: Generated Struct Access Pattern

Given `cli Args:` with options `gc_log`, `backend`, `timeout`, the compiler generates:

```simple
struct Args:
    gc_log: bool
    backend: text
    timeout: i64
    _subcommand: text
    _positionals: [text]

fn Args.parse(args: [text]) -> Args:
    # ... generated parsing logic ...

fn Args.help() -> text:
    # ... generated help text ...

fn Args.subcommand() -> text:
    self._subcommand

fn Args.positionals() -> [text]:
    self._positionals
```

Usage in `main()`:

```simple
fn main() -> i64:
    val args = Args.parse(get_cli_args())
    if args._subcommand == "test":
        return run_tests(args)
    elif args._subcommand == "build":
        return run_build(args)
    # ...
```

## Appendix B: Prefetch Mechanism

When `prefetch: true` and `file: ".spl"` are declared, the generated `main()` preamble includes:

```c
// Before any argument parsing
if (argc >= 2) {
    const char* ext = strrchr(argv[1], '.');
    if (ext && strcmp(ext, ".spl") == 0) {
        int fd = open(argv[1], O_RDONLY);
        if (fd >= 0) {
            posix_fadvise(fd, 0, 0, POSIX_FADV_WILLNEED);
            close(fd);
        }
    }
}
```

This triggers the kernel's readahead mechanism, overlapping disk I/O with argument parsing and initialization. On cold-cache runs with large source files, this can save 2-5ms of latency.
