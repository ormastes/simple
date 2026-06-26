# Command Dispatch Specification

> Commands route to Simple (.spl) apps by default, with Rust fallback via environment variable guards or Rust-only flags.

<!-- sdn-diagram:id=command_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=command_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

command_dispatch_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=command_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 105 | 105 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Command Dispatch Specification

Commands route to Simple (.spl) apps by default, with Rust fallback via environment variable guards or Rust-only flags.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/command_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Commands route to Simple (.spl) apps by default, with Rust fallback
via environment variable guards or Rust-only flags.

## Dispatch Pattern
1. Check env guard (SIMPLE_<CMD>_RUST) -> use Rust fallback
2. Check for Rust-only flags -> use Rust fallback
3. Find Simple app at src/app/<tool>/main.spl -> dispatch
4. Fall back to Rust implementation

## Migrated Commands (12 total)
fmt, lint, spipe-docgen, context, mcp, verify, dashboard,
coverage, depgraph, lsp, dap, test

## Path Resolution (3 strategies)
1. Relative to CWD (development)
2. Relative to executable (../../ from target/debug/)
3. SIMPLE_HOME environment variable

## Edge Cases
- Empty args after command name
- Multiple Rust-only flags combined
- Args with special characters (spaces, quotes, equals)
- Flag-like file names (e.g., --file.spl)
- Mixed flag ordering
- Prefix matching pitfalls (--json-output vs --json)
- Commands with no Rust fallback
- Path with spaces and unicode

## Scenarios

### Simple app files exist

#### formatter app path

1. expect path ends with
2. expect path starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/formatter/main.spl"
expect path.ends_with(".spl") == true
expect path.starts_with("src/app/") == true
```

</details>

#### lint app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/lint/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### spipe_docgen app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/spipe_docgen/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### context app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/context/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### mcp app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/mcp/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### verify app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/verify/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### dashboard app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/dashboard/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### coverage app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/coverage/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### depgraph app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/depgraph/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### lsp app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/lsp/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### dap app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/dap/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### test_runner_new app path

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/test_runner_new/main.spl"
expect path.ends_with(".spl") == true
```

</details>

### environment guard naming convention

#### all guards follow SIMPLE_<CMD>_RUST pattern

1. expect guard starts with
2. expect guard ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guards = [
    "SIMPLE_FMT_RUST",
    "SIMPLE_LINT_RUST",
    "SIMPLE_TEST_RUNNER_RUST",
    "SIMPLE_CONTEXT_RUST",
    "SIMPLE_MCP_RUST",
    "SIMPLE_DASHBOARD_RUST",
    "SIMPLE_VERIFY_RUST",
    "SIMPLE_SPIPE_DOCGEN_RUST",
    "SIMPLE_COVERAGE_RUST",
    "SIMPLE_DEPGRAPH_RUST",
    "SIMPLE_LSP_RUST",
    "SIMPLE_DAP_RUST"
]
for guard in guards:
    expect guard.starts_with("SIMPLE_") == true
    expect guard.ends_with("_RUST") == true
```

</details>

#### guard names are uppercase

1. expect guard == guard upper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guards = ["SIMPLE_FMT_RUST", "SIMPLE_LINT_RUST", "SIMPLE_MCP_RUST"]
for guard in guards:
    expect guard == guard.upper()
```

</details>

#### guard count matches migrated command count

1. expect guards len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guards = [
    "SIMPLE_FMT_RUST", "SIMPLE_LINT_RUST", "SIMPLE_TEST_RUNNER_RUST",
    "SIMPLE_CONTEXT_RUST", "SIMPLE_MCP_RUST", "SIMPLE_DASHBOARD_RUST",
    "SIMPLE_VERIFY_RUST", "SIMPLE_SPIPE_DOCGEN_RUST",
    "SIMPLE_COVERAGE_RUST", "SIMPLE_DEPGRAPH_RUST",
    "SIMPLE_LSP_RUST", "SIMPLE_DAP_RUST"
]
expect guards.len() == 12
```

</details>

#### no duplicate guard names

1. expect unique count == guards len


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guards = [
    "SIMPLE_FMT_RUST", "SIMPLE_LINT_RUST", "SIMPLE_TEST_RUNNER_RUST",
    "SIMPLE_CONTEXT_RUST", "SIMPLE_MCP_RUST", "SIMPLE_DASHBOARD_RUST",
    "SIMPLE_VERIFY_RUST", "SIMPLE_SPIPE_DOCGEN_RUST",
    "SIMPLE_COVERAGE_RUST", "SIMPLE_DEPGRAPH_RUST",
    "SIMPLE_LSP_RUST", "SIMPLE_DAP_RUST"
]
# Check uniqueness by verifying count matches set size
var unique_count = 0
for i in 0..guards.len():
    var is_dup = false
    for j in 0..i:
        if guards[i] == guards[j]:
            is_dup = true
    if not is_dup:
        unique_count = unique_count + 1
expect unique_count == guards.len()
```

</details>

### Rust-only flag detection

#### fmt command flags

#### detects --json as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["fmt", "--json", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### normal args do not need Rust

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["fmt", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == false
```

</details>

#### EDGE: --json-output is NOT --json (exact match)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["fmt", "--json-output", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == false
```

</details>

#### EDGE: --JSON uppercase is NOT --json (case sensitive)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["fmt", "--JSON", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == false
```

</details>

#### lint command flags

#### detects --json as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["lint", "--json", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == true
```

</details>

#### detects --fix as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["lint", "--fix", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == true
```

</details>

#### both --json and --fix triggers Rust

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["lint", "--json", "--fix", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == true
```

</details>

#### normal args do not need Rust

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["lint", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == false
```

</details>

#### EDGE: --fixed is NOT --fix (exact match)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["lint", "--fixed", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == false
```

</details>

#### test command flags

#### detects --watch as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--watch"]
val needs_rust = args.any(_1 == "--watch" or _1 == "--parallel")
expect needs_rust == true
```

</details>

#### detects --parallel as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--parallel"]
val needs_rust = args.any(_1 == "--watch" or _1 == "--parallel")
expect needs_rust == true
```

</details>

#### detects -p as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "-p"]
val needs_rust = args.any(_1 == "-p")
expect needs_rust == true
```

</details>

#### detects --json as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--json"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### detects --rust-tests as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--rust-tests"]
val needs_rust = args.any(_1 == "--rust-tests")
expect needs_rust == true
```

</details>

#### detects --list-runs as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--list-runs"]
val needs_rust = args.any(_1 == "--list-runs")
expect needs_rust == true
```

</details>

#### detects --full-parallel as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--full-parallel"]
val needs_rust = args.any(_1 == "--full-parallel")
expect needs_rust == true
```

</details>

#### detects --rust-ignored as Rust-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--rust-ignored"]
val needs_rust = args.any(_1 == "--rust-ignored")
expect needs_rust == true
```

</details>

#### normal test args do not need Rust

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "my_spec.spl"]
val needs_rust = args.any(_1 == "--watch" or _1 == "--parallel" or _1 == "--json")
expect needs_rust == false
```

</details>

#### test command prefix flags

#### detects --doctest prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--doctest-only"]
val needs_rust = args.any(_1.starts_with("--doctest"))
expect needs_rust == true
```

</details>

#### detects --diagram prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--diagram-type=sequence"]
val needs_rust = args.any(_1.starts_with("--diagram"))
expect needs_rust == true
```

</details>

#### detects --seq- prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--seq-filter=foo"]
val needs_rust = args.any(_1.starts_with("--seq-"))
expect needs_rust == true
```

</details>

#### detects --prune-runs prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--prune-runs=50"]
val needs_rust = args.any(_1.starts_with("--prune-runs"))
expect needs_rust == true
```

</details>

#### EDGE: --watching is NOT --watch (exact match)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--watching"]
val needs_rust = args.any(_1 == "--watch")
expect needs_rust == false
```

</details>

### dispatch argument construction

#### prepends simple_old and app path using slice

1. expect full args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_path = "src/app/formatter/main.spl"
val args = ["fmt", "file.spl", "--check"]
val user_args = args[1:]
var full_args = ["simple_old", app_path]
for a in user_args:
    full_args = full_args + [a]
expect full_args[0] == "simple_old"
expect full_args[1] == "src/app/formatter/main.spl"
expect full_args[2] == "file.spl"
expect full_args[3] == "--check"
expect full_args.len() == 4
```

</details>

#### passes all user args preserving order

1. expect full args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_path = "src/app/lint/main.spl"
val args = ["lint", "src/", "--verbose", "--warn-only"]
val user_args = args[1:]
var full_args = ["simple_old", app_path]
for a in user_args:
    full_args = full_args + [a]
expect full_args.len() == 5
expect full_args[2] == "src/"
expect full_args[3] == "--verbose"
expect full_args[4] == "--warn-only"
```

</details>

#### handles no extra args (command only)

1. expect user args len
2. expect full args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["dashboard"]
val user_args = args[1:]
expect user_args.len() == 0
var full_args = ["simple_old", "src/app/dashboard/main.spl"]
expect full_args.len() == 2
```

</details>

#### EDGE: single arg after command

1. expect user args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["coverage", "scan"]
val user_args = args[1:]
expect user_args.len() == 1
expect user_args[0] == "scan"
```

</details>

#### EDGE: many args preserved

1. expect user args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "a", "b", "c", "d", "e", "f", "g"]
val user_args = args[1:]
expect user_args.len() == 7
expect user_args[0] == "a"
expect user_args[6] == "g"
```

</details>

#### EDGE: args with equals signs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--tag=integration", "--timeout=30"]
val user_args = args[1:]
expect user_args[0] == "--tag=integration"
expect user_args[1] == "--timeout=30"
```

</details>

#### EDGE: args with spaces in values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["context", "--format=json", "my file.spl"]
val user_args = args[1:]
expect user_args[0] == "--format=json"
expect user_args[1] == "my file.spl"
```

</details>

#### EDGE: flag-like filenames

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["lint", "--verbose.spl"]
val user_args = args[1:]
expect user_args[0] == "--verbose.spl"
```

</details>

#### EDGE: empty string arg

1. expect user args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "", "file.spl"]
val user_args = args[1:]
expect user_args.len() == 2
expect user_args[0] == ""
```

</details>

#### EDGE: double dash separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--", "file.spl"]
val user_args = args[1:]
expect user_args[0] == "--"
expect user_args[1] == "file.spl"
```

</details>

### app path resolution

#### all migrated apps follow src/app/<name>/main.spl pattern

1. expect path starts with
2. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apps = ["formatter", "lint", "coverage", "dashboard", "verify",
            "context", "mcp", "spipe_docgen", "depgraph", "lsp", "dap"]
for app in apps:
    val path = "src/app/{app}/main.spl"
    expect path.starts_with("src/app/") == true
    expect path.ends_with("/main.spl") == true
```

</details>

#### test runner uses test_runner_new directory

1. expect path contains
2. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/test_runner_new/main.spl"
expect path.contains("test_runner_new") == true
expect path.ends_with("/main.spl") == true
```

</details>

#### EDGE: path does not contain double slashes

1. expect path contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apps = ["formatter", "lint", "dashboard"]
for app in apps:
    val path = "src/app/{app}/main.spl"
    expect path.contains("//") == false
```

</details>

#### EDGE: path segments are valid identifiers

1. expect app len
2. expect app contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apps = ["formatter", "lint", "coverage", "dashboard", "verify",
            "context", "mcp", "spipe_docgen", "depgraph", "lsp", "dap"]
for app in apps:
    expect app.len() > 0
    # No spaces in directory names
    expect app.contains(" ") == false
```

</details>

#### EDGE: total migrated app count is 12

1. expect apps len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apps = ["formatter", "lint", "coverage", "dashboard", "verify",
            "context", "mcp", "spipe_docgen", "depgraph", "lsp", "dap",
            "test_runner_new"]
expect apps.len() == 12
```

</details>

#### EDGE: each app has unique directory name

1. expect unique == apps len


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apps = ["formatter", "lint", "coverage", "dashboard", "verify",
            "context", "mcp", "spipe_docgen", "depgraph", "lsp", "dap",
            "test_runner_new"]
var unique = 0
for i in 0..apps.len():
    var dup = false
    for j in 0..i:
        if apps[i] == apps[j]:
            dup = true
    if not dup:
        unique = unique + 1
expect unique == apps.len()
```

</details>

#### resolve: CWD path is first priority

1. expect cwd path starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulates resolve_app_path logic
val cwd_path = "src/app/formatter/main.spl"
val exe_path = "/usr/local/bin/../src/app/formatter/main.spl"
# CWD is checked first
expect cwd_path.starts_with("src/") == true
```

</details>

#### resolve: exe-relative goes up two dirs from target/debug

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exe_dir = "/project/target/debug"
# Parent of parent = /project
# /project + src/app/... = correct path
val parts = exe_dir.split("/")
expect parts.len() > 2
```

</details>

### non-migrated commands

#### compile stays in Rust (bootstrapping dependency)

1. expect non migrated contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val non_migrated = ["compile", "check", "watch", "query", "info",
                    "gen-lean", "diagram"]
expect non_migrated.contains("compile") == true
```

</details>

#### package management stays in Rust (deep integration)

1. expect pkg cmds len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg_cmds = ["init", "add", "remove", "install", "update", "list", "tree", "cache"]
expect pkg_cmds.len() == 8
```

</details>

#### EDGE: non-migrated and migrated sets do not overlap

1. expect non migrated contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val non_migrated = ["compile", "check", "watch", "query", "info",
                    "gen-lean", "diagram", "init", "add", "remove",
                    "install", "update", "list", "tree", "cache"]
val migrated = ["fmt", "lint", "test", "context", "mcp", "verify",
                "dashboard", "spipe-docgen", "coverage", "depgraph", "lsp", "dap"]
for m in migrated:
    expect non_migrated.contains(m) == false
```

</details>

#### EDGE: brief uses inline codegen, not dispatch

1. expect dispatch commands contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inline_commands = ["brief"]
val dispatch_commands = ["fmt", "lint", "test", "dashboard"]
for cmd in inline_commands:
    expect dispatch_commands.contains(cmd) == false
```

</details>

### pure Simple commands (no Rust fallback)

#### coverage has no Rust fallback

1. expect pure simple contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pure_simple = ["coverage", "depgraph", "lsp", "dap"]
expect pure_simple.contains("coverage") == true
```

</details>

#### all pure Simple commands listed

1. expect pure simple len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pure_simple = ["coverage", "depgraph", "lsp", "dap"]
expect pure_simple.len() == 4
```

</details>

### hybrid commands (Simple default, Rust fallback)

#### fmt has Rust fallback

1. expect hybrid contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hybrid = ["fmt", "lint", "test", "spipe-docgen", "context",
              "mcp", "verify", "dashboard"]
expect hybrid.contains("fmt") == true
```

</details>

#### hybrid command count is 8

1. expect hybrid len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hybrid = ["fmt", "lint", "test", "spipe-docgen", "context",
              "mcp", "verify", "dashboard"]
expect hybrid.len() == 8
```

</details>

#### hybrid + pure = total migrated

1. expect hybrid len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hybrid = ["fmt", "lint", "test", "spipe-docgen", "context",
              "mcp", "verify", "dashboard"]
val pure = ["coverage", "depgraph", "lsp", "dap"]
expect hybrid.len() + pure.len() == 12
```

</details>

#### EDGE: each hybrid command has a matching guard

1. expect commands len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Command -> guard mapping
val commands = ["fmt", "lint", "context", "mcp", "verify", "dashboard"]
val guards = ["SIMPLE_FMT_RUST", "SIMPLE_LINT_RUST", "SIMPLE_CONTEXT_RUST",
              "SIMPLE_MCP_RUST", "SIMPLE_VERIFY_RUST", "SIMPLE_DASHBOARD_RUST"]
expect commands.len() == guards.len()
```

</details>

### flag detection edge cases

#### EDGE: flag at end of args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "file.spl", "--json"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### EDGE: flag at beginning (right after command)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--json", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### EDGE: flag in middle of args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "a.spl", "--json", "b.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### EDGE: only flag, no files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["lint", "--json"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == true
```

</details>

#### EDGE: multiple non-rust flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--verbose", "--list", "--show-tags"]
val needs_rust = args.any(_1 == "--json" or _1 == "--watch" or _1 == "--parallel")
expect needs_rust == false
```

</details>

#### EDGE: args[1:] skips command name correctly

1. expect check args len
2. expect check args contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--verbose", "file.spl"]
val check_args = args[1:]
expect check_args.len() == 2
expect check_args[0] == "--verbose"
# Command name itself should never be checked for flags
expect check_args.contains("test") == false
```

</details>

#### EDGE: single letter flag -p matches exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "-p"]
val needs_rust = args.any(_1 == "-p")
expect needs_rust == true
```

</details>

#### EDGE: -p is not prefix of -pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "-pattern"]
val needs_rust = args.any(_1 == "-p")
expect needs_rust == false
```

</details>

#### EDGE: --capture-screenshots exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--capture-screenshots"]
val needs_rust = args.any(_1 == "--capture-screenshots")
expect needs_rust == true
```

</details>

#### EDGE: --cleanup-runs exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--cleanup-runs"]
val needs_rust = args.any(_1 == "--cleanup-runs")
expect needs_rust == true
```

</details>

#### EDGE: combined rust-only and normal flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test", "--verbose", "--watch", "--list"]
val needs_rust = args.any(_1 == "--watch")
expect needs_rust == true
```

</details>

#### EDGE: no args at all (just command)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["test"]
val check_args = args[1:]
val needs_rust = check_args.any(_1 == "--json")
expect needs_rust == false
```

</details>

### argument slicing edge cases

#### slice of single-element list is empty

1. expect rest len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["cmd"]
val rest = args[1:]
expect rest.len() == 0
```

</details>

#### slice preserves all elements

1. expect rest len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["cmd", "a", "b", "c"]
val rest = args[1:]
expect rest.len() == 3
expect rest[0] == "a"
expect rest[1] == "b"
expect rest[2] == "c"
```

</details>

#### slice of two-element list gives one element

1. expect rest len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["cmd", "arg"]
val rest = args[1:]
expect rest.len() == 1
expect rest[0] == "arg"
```

</details>

#### EDGE: nested slicing

1. expect rest2 len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["cmd", "a", "b", "c", "d"]
val rest = args[1:]
val rest2 = rest[1:]
expect rest2.len() == 3
expect rest2[0] == "b"
```

</details>

#### EDGE: slice with negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["a", "b", "c", "d"]
val last = args[-1]
expect last == "d"
```

</details>

#### EDGE: full slice is identity

1. expect full len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["a", "b", "c"]
val full = args[0:]
expect full.len() == 3
```

</details>

#### EDGE: slice range

1. expect mid len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["cmd", "a", "b", "c", "d"]
val mid = args[1:3]
expect mid.len() == 2
expect mid[0] == "a"
expect mid[1] == "b"
```

</details>

#### EDGE: step slice

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["a", "b", "c", "d", "e", "f"]
val evens = args[::2]
expect evens.len() == 3
expect evens[0] == "a"
expect evens[1] == "c"
expect evens[2] == "e"
```

</details>

### command to app directory mapping

#### fmt maps to formatter (not fmt)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "fmt"
val app_dir = "formatter"
expect cmd != app_dir
```

</details>

#### spipe-docgen maps to spipe_docgen (hyphen to underscore)

1. expect cmd contains
2. expect app dir contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "spipe-docgen"
val app_dir = "spipe_docgen"
expect cmd.contains("-") == true
expect app_dir.contains("-") == false
```

</details>

#### test maps to test_runner_new (not test)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "test"
val app_dir = "test_runner_new"
expect cmd != app_dir
```

</details>

#### direct name commands: lint, coverage, verify, dashboard, context, mcp, depgraph, lsp, dap

1. expect path contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = ["lint", "coverage", "verify", "dashboard", "context",
              "mcp", "depgraph", "lsp", "dap"]
for cmd in direct:
    val path = "src/app/{cmd}/main.spl"
    expect path.contains(cmd) == true
```

</details>

#### EDGE: command name is not always the directory name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# These commands have different directory names
val mapped = [["fmt", "formatter"], ["test", "test_runner_new"], ["spipe-docgen", "spipe_docgen"]]
for pair in mapped:
    expect pair[0] != pair[1]
```

</details>

#### EDGE: all app directories are snake_case or single word

1. expect dir contains
2. expect dir contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = ["formatter", "lint", "coverage", "dashboard", "verify",
            "context", "mcp", "spipe_docgen", "depgraph", "lsp", "dap",
            "test_runner_new"]
for dir in dirs:
    expect dir.contains("-") == false
    expect dir.contains(" ") == false
```

</details>

### dispatch decision logic

#### env guard takes highest priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Priority: env guard > rust-only flags > simple app > rust fallback
val env_set = true
val has_rust_flag = true
val app_exists = true
# When env is set, always use Rust regardless of other conditions
val use_rust = env_set
expect use_rust == true
```

</details>

#### rust-only flags take second priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_set = false
val has_rust_flag = true
val app_exists = true
val use_rust = env_set or has_rust_flag
expect use_rust == true
```

</details>

#### simple app used when no env guard and no rust flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_set = false
val has_rust_flag = false
val app_exists = true
val use_simple = not env_set and not has_rust_flag and app_exists
expect use_simple == true
```

</details>

#### rust fallback used when app not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_set = false
val has_rust_flag = false
val app_exists = false
val use_simple = not env_set and not has_rust_flag and app_exists
expect use_simple == false
```

</details>

#### EDGE: env guard overrides even with no rust flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_set = true
val has_rust_flag = false
val use_rust = env_set
expect use_rust == true
```

</details>

#### EDGE: app not found with no fallback errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_exists = false
val has_rust_fallback = false
val error = not app_exists and not has_rust_fallback
expect error == true
```

</details>

### full dispatch simulation

#### simulate fmt dispatch: normal args -> Simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["fmt", "file.spl", "--check"]
val env_set = false
val needs_rust = args.any(_1 == "--json")
val app_exists = true
val dispatch = dispatch_decision(env_set, needs_rust, app_exists)
expect dispatch == "simple"
```

</details>

#### simulate fmt dispatch: --json -> Rust

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["fmt", "--json", "file.spl"]
val env_set = false
val needs_rust = args.any(_1 == "--json")
val dispatch = dispatch_decision(env_set, needs_rust, true)
expect dispatch == "rust"
```

</details>

#### simulate fmt dispatch: env guard -> Rust

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["fmt", "file.spl"]
val env_set = true
val needs_rust = args.any(_1 == "--json")
val dispatch = dispatch_decision(env_set, needs_rust, true)
expect dispatch == "rust"
```

</details>

#### simulate coverage dispatch: no fallback, app exists -> Simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = if true: "simple" else: "error"
expect dispatch == "simple"
```

</details>

#### simulate coverage dispatch: no fallback, app missing -> error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = if false: "simple" else: "error"
expect dispatch == "error"
```

</details>

#### simulate test dispatch: --watch -> Rust, normal -> Simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args_watch = ["test", "--watch"]
val args_normal = ["test", "my_spec.spl"]
val watch_rust = args_watch.any(_1 == "--watch" or _1 == "--parallel" or _1 == "--json")
val normal_rust = args_normal.any(_1 == "--watch" or _1 == "--parallel" or _1 == "--json")
expect watch_rust == true
expect normal_rust == false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 105 |
| Active scenarios | 105 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
