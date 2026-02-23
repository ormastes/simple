# Simple Shell (SSH) DSL Design

**Date:** 2026-02-01
**Status:** Proposal

## Summary

`.ssh` files (Simple Shell) are Simple code with `std.shell.*` auto-imported, providing a unified shell scripting + build automation DSL that is shorter than bash and replaces both bash scripts and Makefiles.

```simple
#!/usr/bin/env simple-shell

task build:
    !? cargo build --release

task test depends_on: [build]:
    !? cargo test --workspace

task clean phony:
    rm -rf target/
```

## Design Goals

1. **Shorter than bash** for every common operation
2. **Full Simple language** always available (no separate "shell mode")
3. **Unified bash + make** in one file format
4. **Fail-fast by default** (unlike bash's "keep going")
5. **Typed errors** via `Result<T, ShellError>`

## Extension: `.ssh`

**Mnemonic:** Simple Shell

**Conflict with SSH protocol:** Minimal risk. SSH protocol uses no file extension (config in `~/.ssh/` directory). Context distinguishes: `script.ssh` is a file, `ssh user@host` is a command.

Alternative extensions considered: `.shs` (looks like typo), `.simple.sh` (verbose). `.ssh` is short and clear.

## Command Execution

### Running Commands

```simple
# Bare word commands (like bash)
ls -la /tmp
echo "hello"

# Capture output as text
val output = $(git rev-parse HEAD)

# Capture output as array of lines
val files = @(ls *.txt)

# Run and fail-fast on non-zero exit
!? cargo build

# Force command (disambiguate from Simple function)
! ls
```

| Syntax | Returns | Behavior |
|--------|---------|----------|
| `command args` | Unit | Run, ignore exit code |
| `$(command)` | `Result<text, ShellError>` | Capture stdout |
| `@(command)` | `Result<[text], ShellError>` | Capture stdout as lines |
| `!? command` | Unit | Run, exit script on failure |
| `! command` | Unit | Force external command |

### Pipes and Redirects

```simple
# Unix pipe (text stream)
cat file.txt | grep pattern | wc -l

# Typed pipe (Simple values)
ls_typed() |> filter(\f: f.size > 1000) |> map(\f: f.name)

# Redirects
echo "data" > output.txt      # stdout to file
echo "more" >+ output.txt     # append (bash: >>)
command !> error.log           # stderr (bash: 2>)
command >> all.log             # both stdout+stderr (bash: &>)

# Here-string
cat <<< "inline content"

# Background
cargo build &
val pid = $!
```

**Shorter than bash:**

| Operation | Bash | SSH |
|-----------|------|-----|
| Append | `>>` | `>+` |
| Stderr redirect | `2>` | `!>` |
| Both streams | `&>` | `>>` |
| Exit code | `$?` | `$?` |
| Capture output | `` `cmd` `` or `$(cmd)` | `$(cmd)` |
| Capture as array | `IFS=$'\n' arr=($(cmd))` | `@(cmd)` |
| Fail on error | `set -e; cmd` | `!? cmd` |

## Variables and Environment

```simple
# Simple variables
val user = "alice"
var count = 0

# Environment variables
env.PATH += ":/new/path"
val home = env.HOME
export env.MY_VAR = "value"

# String interpolation (already in Simple)
echo "User {user} in {env.HOME}"

# Exit code
val code = $?
```

## Error Handling

Default is **fail-fast** (safer than bash `set -e`):

```simple
# Stops script on first failure
!? cargo build
!? cargo test

# Explicit error handling
match $(dangerous_command):
    Ok(output): print output
    Err(e): print "Failed: {e}"

# Default value on failure
val result = $(fallible_cmd) ?? "default"

# Propagate errors
fn deploy() -> Result<(), ShellError>:
    $(git pull)?
    $(cargo build --release)?
    Ok(())

# Explicitly ignore error
$(might_fail) or_else: ()
```

## Task System (Make Replacement)

### Basic Tasks

```simple
task build:
    """Build the project"""
    !? cargo build --release

task test depends_on: [build]:
    """Run tests after building"""
    !? cargo test --workspace

task clean phony:
    """Remove build artifacts (always runs)"""
    rm -rf target/
```

### Task Parameters

```simple
task deploy(env: text = "staging"):
    """Deploy to environment"""
    val server = match env:
        | "production" -> "prod.example.com"
        | "staging" -> "staging.example.com"
        | _ -> error("Unknown: {env}")
    !? scp target/release/app {server}:/app/
```

### Pattern Rules

```simple
task compile(source: File("*.c")) -> File("*.o"):
    """Compile C files"""
    !? gcc -c {source} -o {source.with_extension("o")}
```

### Parallel Dependencies

```simple
task all depends_on: [build, test, docs] parallel:
    """Run all tasks concurrently"""
    echo "Done"
```

### Task Invocation

```bash
simple build.ssh            # Runs 'default' task
simple build.ssh test       # Runs 'test' task
simple build.ssh deploy env=production
```

## Control Flow

```simple
# Conditional on command success
if !? test -f config.json:
    echo "Config exists"

# Loop over command output
for line in @(ls *.txt):
    echo "Processing {line}"

# Match on exit codes
match $(command):
    Ok(_): print "Success"
    Err(e) if e.exit_code == 1: print "Not found"
    Err(e): print "Error: {e}"
```

## Standard Library (`std.shell`)

Auto-imported in `.ssh` files:

```simple
# Types
struct ShellError:
    exit_code: i64
    stderr: text
    command: text

# File checks (replaces bash test)
fn exists(path: text) -> bool
fn is_file(path: text) -> bool
fn is_dir(path: text) -> bool
fn is_executable(path: text) -> bool
fn is_newer(file1: text, file2: text) -> bool

# Utilities
fn retry(cmd: fn() -> Result<T, E>, times: i64) -> Result<T, E>
fn timeout(cmd: fn() -> T, seconds: i64) -> Result<T, TimeoutError>

# Path manipulation
fn basename(path: text) -> text
fn dirname(path: text) -> text
fn realpath(path: text) -> text
```

## Migration from Bash

| Bash | SSH |
|------|-----|
| `set -e` | Default behavior |
| `set -x` | `set trace: true` |
| `$@` | `args` |
| `$1` | `args[0]` |
| `[ -f file ]` | `is_file("file")` |
| `cmd && cmd2` | `!? cmd; cmd2` |
| `cmd \|\| cmd2` | `cmd or_else: cmd2` |
| `for i in $(ls)` | `for i in @(ls)` |
| `function name { }` | `fn name():` |

## Migration from Makefile

| Makefile | SSH |
|----------|-----|
| `.PHONY: clean` | `task clean phony:` |
| `build: dep1 dep2` | `task build depends_on: [dep1, dep2]:` |
| `%.o: %.c` | `task compile(src: File("*.c")) -> File("*.o"):` |
| `@echo "msg"` | `echo "msg"` |
| `$(VAR)` | `{VAR}` |

## Full Example: CI Pipeline

```simple
#!/usr/bin/env simple-shell

val VERSION = $(cargo pkgid | cut -d# -f2)?

task default depends_on: [build]:
    ()

task lint:
    !? cargo clippy -- -D warnings
    !? cargo fmt -- --check

task test depends_on: [lint]:
    !? cargo test --workspace
    !? cargo test --doc

task build depends_on: [test]:
    !? cargo build --release

task package depends_on: [build]:
    mkdir -p dist/
    cp target/release/app dist/
    tar -czf "dist/app-{VERSION}.tar.gz" -C dist app
    echo "Package: dist/app-{VERSION}.tar.gz"

task coverage:
    !? cargo llvm-cov --workspace --html
    echo "Report: target/coverage/html/index.html"
```

## Security

- String interpolation in commands escapes shell metacharacters by default
- `unsafe_shell("raw command")` for explicit opt-in to raw execution
- Linter warns on interpolated variables in commands

## Execution Model

- `.ssh` files are interpreted by Simple runtime (same as `.spl`)
- `std.shell.*` auto-imported (no manual `use` needed)
- Shebang: `#!/usr/bin/env simple-shell`
- Task graph: topological sort, parallel execution via `//` operator

## Comparison

| Feature | Bash | Make | Nushell | Just | **SSH** |
|---------|------|------|---------|------|---------|
| Brevity | Medium | Medium | Low | High | **High** |
| Type Safety | None | None | Strong | None | **Strong** |
| Full Language | Limited | No | Yes | No | **Yes** |
| Task Deps | Manual | Built-in | No | Built-in | **Built-in** |
| Parallel | Manual | `-j` | No | No | **Built-in** |
| Error Handling | Weak | Weak | Strong | Weak | **Strong** |

## Implementation Files

- `rust/compiler/src/lexer/` - new operators (`!?`, `>+`, `!>`, `@()`)
- `rust/compiler/src/parser/` - task syntax, command execution
- `rust/runtime/src/shell/` - shell execution engine (new)
- `src/lib/src/shell.spl` - standard library module (new)
- `src/app/cli/main.spl` - CLI integration for `.ssh` files
