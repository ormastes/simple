# Command Dispatch Specification

> Tests covering Simple app files exist, environment guard naming convention, Rust-only flag detection, dispatch argument construction, app path resolution, non-migrated commands, pure Simple commands (no Rust fallback), hybrid commands (Simple default, Rust fallback), flag detection edge cases, argument slicing edge cases, command to app directory mapping, dispatch decision logic, full dispatch simulation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 111 | 111 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Command Dispatch Specification

## Scenarios

### Simple app files exist

#### formatter app path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formatter app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("formatter app path")
val path = "src/app/formatter/main.spl"
expect path.ends_with(".spl") == true
expect path.starts_with("src/app/") == true
```

</details>

#### lint app path

- lint app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lint app path")
val path = "src/app/lint/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### spipe_docgen app path

- spipe_docgen app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("spipe_docgen app path")
val path = "src/app/spipe_docgen/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### context app path

- context app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("context app path")
val path = "src/app/context/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### mcp app path

- mcp app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("mcp app path")
val path = "src/app/mcp/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### verify app path

- verify app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("verify app path")
val path = "src/app/verify/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### dashboard app path

- dashboard app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("dashboard app path")
val path = "src/app/dashboard/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### coverage app path

- coverage app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("coverage app path")
val path = "src/app/coverage/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### depgraph app path

- depgraph app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("depgraph app path")
val path = "src/app/depgraph/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### lsp app path

- lsp app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lsp app path")
val path = "src/app/lsp/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### dap app path

- dap app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("dap app path")
val path = "src/app/dap/main.spl"
expect path.ends_with(".spl") == true
```

</details>

#### test_runner_new app path

- test_runner_new app path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("test_runner_new app path")
val path = "src/app/test_runner_new/main.spl"
expect path.ends_with(".spl") == true
```

</details>

### environment guard naming convention

#### all guards follow SIMPLE_<CMD>_RUST pattern

- all guards follow SIMPLE_<CMD>_RUST pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("all guards follow SIMPLE_<CMD>_RUST pattern")
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

- guard names are uppercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guard names are uppercase")
val guards = ["SIMPLE_FMT_RUST", "SIMPLE_LINT_RUST", "SIMPLE_MCP_RUST"]
for guard in guards:
    expect guard == guard.upper()
```

</details>

#### guard count matches migrated command count

- guard count matches migrated command count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guard count matches migrated command count")
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

- no duplicate guard names


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("no duplicate guard names")
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

- detects --json as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --json as Rust-only")
val args = ["fmt", "--json", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### normal args do not need Rust

- normal args do not need Rust


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("normal args do not need Rust")
val args = ["fmt", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == false
```

</details>

#### EDGE: --json-output is NOT --json (exact match)

- EDGE: --json-output is NOT --json (exact match)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: --json-output is NOT --json (exact match)")
val args = ["fmt", "--json-output", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == false
```

</details>

#### EDGE: --JSON uppercase is NOT --json (case sensitive)

- EDGE: --JSON uppercase is NOT --json (case sensitive)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: --JSON uppercase is NOT --json (case sensitive)")
val args = ["fmt", "--JSON", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == false
```

</details>

#### lint command flags

#### detects --json as Rust-only

- detects --json as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --json as Rust-only")
val args = ["lint", "--json", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == true
```

</details>

#### detects --fix as Rust-only

- detects --fix as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --fix as Rust-only")
val args = ["lint", "--fix", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == true
```

</details>

#### both --json and --fix triggers Rust

- both --json and --fix triggers Rust


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("both --json and --fix triggers Rust")
val args = ["lint", "--json", "--fix", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == true
```

</details>

#### normal args do not need Rust

- normal args do not need Rust


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("normal args do not need Rust")
val args = ["lint", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == false
```

</details>

#### EDGE: --fixed is NOT --fix (exact match)

- EDGE: --fixed is NOT --fix (exact match)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: --fixed is NOT --fix (exact match)")
val args = ["lint", "--fixed", "file.spl"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == false
```

</details>

#### test command flags

#### detects --watch as Rust-only

- detects --watch as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --watch as Rust-only")
val args = ["test", "--watch"]
val needs_rust = args.any(_1 == "--watch" or _1 == "--parallel")
expect needs_rust == true
```

</details>

#### detects --parallel as Rust-only

- detects --parallel as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --parallel as Rust-only")
val args = ["test", "--parallel"]
val needs_rust = args.any(_1 == "--watch" or _1 == "--parallel")
expect needs_rust == true
```

</details>

#### detects -p as Rust-only

- detects -p as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects -p as Rust-only")
val args = ["test", "-p"]
val needs_rust = args.any(_1 == "-p")
expect needs_rust == true
```

</details>

#### detects --json as Rust-only

- detects --json as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --json as Rust-only")
val args = ["test", "--json"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### detects --rust-tests as Rust-only

- detects --rust-tests as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --rust-tests as Rust-only")
val args = ["test", "--rust-tests"]
val needs_rust = args.any(_1 == "--rust-tests")
expect needs_rust == true
```

</details>

#### detects --list-runs as Rust-only

- detects --list-runs as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --list-runs as Rust-only")
val args = ["test", "--list-runs"]
val needs_rust = args.any(_1 == "--list-runs")
expect needs_rust == true
```

</details>

#### detects --full-parallel as Rust-only

- detects --full-parallel as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --full-parallel as Rust-only")
val args = ["test", "--full-parallel"]
val needs_rust = args.any(_1 == "--full-parallel")
expect needs_rust == true
```

</details>

#### detects --rust-ignored as Rust-only

- detects --rust-ignored as Rust-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --rust-ignored as Rust-only")
val args = ["test", "--rust-ignored"]
val needs_rust = args.any(_1 == "--rust-ignored")
expect needs_rust == true
```

</details>

#### normal test args do not need Rust

- normal test args do not need Rust


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("normal test args do not need Rust")
val args = ["test", "my_spec.spl"]
val needs_rust = args.any(_1 == "--watch" or _1 == "--parallel" or _1 == "--json")
expect needs_rust == false
```

</details>

#### test command prefix flags

#### detects --doctest prefix

- detects --doctest prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --doctest prefix")
val args = ["test", "--doctest-only"]
val needs_rust = args.any(_1.starts_with("--doctest"))
expect needs_rust == true
```

</details>

#### detects --diagram prefix

- detects --diagram prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --diagram prefix")
val args = ["test", "--diagram-type=sequence"]
val needs_rust = args.any(_1.starts_with("--diagram"))
expect needs_rust == true
```

</details>

#### detects --seq- prefix

- detects --seq- prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --seq- prefix")
val args = ["test", "--seq-filter=foo"]
val needs_rust = args.any(_1.starts_with("--seq-"))
expect needs_rust == true
```

</details>

#### detects --prune-runs prefix

- detects --prune-runs prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects --prune-runs prefix")
val args = ["test", "--prune-runs=50"]
val needs_rust = args.any(_1.starts_with("--prune-runs"))
expect needs_rust == true
```

</details>

#### EDGE: --watching is NOT --watch (exact match)

- EDGE: --watching is NOT --watch (exact match)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: --watching is NOT --watch (exact match)")
val args = ["test", "--watching"]
val needs_rust = args.any(_1 == "--watch")
expect needs_rust == false
```

</details>

### dispatch argument construction

#### prepends simple_old and app path using slice

- prepends simple_old and app path using slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("prepends simple_old and app path using slice")
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

- passes all user args preserving order


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("passes all user args preserving order")
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

- handles no extra args (command only)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles no extra args (command only)")
val args = ["dashboard"]
val user_args = args[1:]
expect user_args.len() == 0
var full_args = ["simple_old", "src/app/dashboard/main.spl"]
expect full_args.len() == 2
```

</details>

#### EDGE: single arg after command

- EDGE: single arg after command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: single arg after command")
val args = ["coverage", "scan"]
val user_args = args[1:]
expect user_args.len() == 1
expect user_args[0] == "scan"
```

</details>

#### EDGE: many args preserved

- EDGE: many args preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: many args preserved")
val args = ["test", "a", "b", "c", "d", "e", "f", "g"]
val user_args = args[1:]
expect user_args.len() == 7
expect user_args[0] == "a"
expect user_args[6] == "g"
```

</details>

#### EDGE: args with equals signs

- EDGE: args with equals signs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: args with equals signs")
val args = ["test", "--tag=integration", "--timeout=30"]
val user_args = args[1:]
expect user_args[0] == "--tag=integration"
expect user_args[1] == "--timeout=30"
```

</details>

#### EDGE: args with spaces in values

- EDGE: args with spaces in values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: args with spaces in values")
val args = ["context", "--format=json", "my file.spl"]
val user_args = args[1:]
expect user_args[0] == "--format=json"
expect user_args[1] == "my file.spl"
```

</details>

#### EDGE: flag-like filenames

- EDGE: flag-like filenames


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: flag-like filenames")
val args = ["lint", "--verbose.spl"]
val user_args = args[1:]
expect user_args[0] == "--verbose.spl"
```

</details>

#### EDGE: empty string arg

- EDGE: empty string arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: empty string arg")
val args = ["test", "", "file.spl"]
val user_args = args[1:]
expect user_args.len() == 2
expect user_args[0] == ""
```

</details>

#### EDGE: double dash separator

- EDGE: double dash separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: double dash separator")
val args = ["test", "--", "file.spl"]
val user_args = args[1:]
expect user_args[0] == "--"
expect user_args[1] == "file.spl"
```

</details>

### app path resolution

#### all migrated apps follow src/app/<name>/main.spl pattern

- all migrated apps follow src/app/<name>/main.spl pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("all migrated apps follow src/app/<name>/main.spl pattern")
val apps = ["formatter", "lint", "coverage", "dashboard", "verify",
            "context", "mcp", "spipe_docgen", "depgraph", "lsp", "dap"]
for app in apps:
    val path = "src/app/{app}/main.spl"
    expect path.starts_with("src/app/") == true
    expect path.ends_with("/main.spl") == true
```

</details>

#### test runner uses test_runner_new directory

- test runner uses test_runner_new directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("test runner uses test_runner_new directory")
val path = "src/app/test_runner_new/main.spl"
expect path.contains("test_runner_new") == true
expect path.ends_with("/main.spl") == true
```

</details>

#### EDGE: path does not contain double slashes

- EDGE: path does not contain double slashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: path does not contain double slashes")
val apps = ["formatter", "lint", "dashboard"]
for app in apps:
    val path = "src/app/{app}/main.spl"
    expect path.contains("//") == false
```

</details>

#### EDGE: path segments are valid identifiers

- EDGE: path segments are valid identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: path segments are valid identifiers")
val apps = ["formatter", "lint", "coverage", "dashboard", "verify",
            "context", "mcp", "spipe_docgen", "depgraph", "lsp", "dap"]
for app in apps:
    expect app.len() > 0
    # No spaces in directory names
    expect app.contains(" ") == false
```

</details>

#### EDGE: total migrated app count is 12

- EDGE: total migrated app count is 12


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: total migrated app count is 12")
val apps = ["formatter", "lint", "coverage", "dashboard", "verify",
            "context", "mcp", "spipe_docgen", "depgraph", "lsp", "dap",
            "test_runner_new"]
expect apps.len() == 12
```

</details>

#### EDGE: each app has unique directory name

- EDGE: each app has unique directory name


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: each app has unique directory name")
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

- resolve: CWD path is first priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resolve: CWD path is first priority")
# Simulates resolve_app_path logic
val cwd_path = "src/app/formatter/main.spl"
val exe_path = "/usr/local/bin/../src/app/formatter/main.spl"
# CWD is checked first
expect cwd_path.starts_with("src/") == true
```

</details>

#### resolve: exe-relative goes up two dirs from target/debug

- resolve: exe-relative goes up two dirs from target/debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resolve: exe-relative goes up two dirs from target/debug")
val exe_dir = "/project/target/debug"
# Parent of parent = /project
# /project + src/app/... = correct path
val parts = exe_dir.split("/")
expect parts.len() > 2
```

</details>

### non-migrated commands

#### compile stays in Rust (bootstrapping dependency)

- compile stays in Rust (bootstrapping dependency)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("compile stays in Rust (bootstrapping dependency)")
val non_migrated = ["compile", "check", "watch", "query", "info",
                    "gen-lean", "diagram"]
expect non_migrated.contains("compile") == true
```

</details>

#### package management stays in Rust (deep integration)

- package management stays in Rust (deep integration)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("package management stays in Rust (deep integration)")
val pkg_cmds = ["init", "add", "remove", "install", "update", "list", "tree", "cache"]
expect pkg_cmds.len() == 8
```

</details>

#### EDGE: non-migrated and migrated sets do not overlap

- EDGE: non-migrated and migrated sets do not overlap


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: non-migrated and migrated sets do not overlap")
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

- EDGE: brief uses inline codegen, not dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: brief uses inline codegen, not dispatch")
val inline_commands = ["brief"]
val dispatch_commands = ["fmt", "lint", "test", "dashboard"]
for cmd in inline_commands:
    expect dispatch_commands.contains(cmd) == false
```

</details>

### pure Simple commands (no Rust fallback)

#### coverage has no Rust fallback

- coverage has no Rust fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("coverage has no Rust fallback")
val pure_simple = ["coverage", "depgraph", "lsp", "dap"]
expect pure_simple.contains("coverage") == true
```

</details>

#### all pure Simple commands listed

- all pure Simple commands listed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("all pure Simple commands listed")
val pure_simple = ["coverage", "depgraph", "lsp", "dap"]
expect pure_simple.len() == 4
```

</details>

### hybrid commands (Simple default, Rust fallback)

#### fmt has Rust fallback

- fmt has Rust fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fmt has Rust fallback")
val hybrid = ["fmt", "lint", "test", "spipe-docgen", "context",
              "mcp", "verify", "dashboard"]
expect hybrid.contains("fmt") == true
```

</details>

#### hybrid command count is 8

- hybrid command count is 8


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("hybrid command count is 8")
val hybrid = ["fmt", "lint", "test", "spipe-docgen", "context",
              "mcp", "verify", "dashboard"]
expect hybrid.len() == 8
```

</details>

#### hybrid + pure = total migrated

- hybrid + pure = total migrated


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("hybrid + pure = total migrated")
val hybrid = ["fmt", "lint", "test", "spipe-docgen", "context",
              "mcp", "verify", "dashboard"]
val pure = ["coverage", "depgraph", "lsp", "dap"]
expect hybrid.len() + pure.len() == 12
```

</details>

#### EDGE: each hybrid command has a matching guard

- EDGE: each hybrid command has a matching guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: each hybrid command has a matching guard")
# Command -> guard mapping
val commands = ["fmt", "lint", "context", "mcp", "verify", "dashboard"]
val guards = ["SIMPLE_FMT_RUST", "SIMPLE_LINT_RUST", "SIMPLE_CONTEXT_RUST",
              "SIMPLE_MCP_RUST", "SIMPLE_VERIFY_RUST", "SIMPLE_DASHBOARD_RUST"]
expect commands.len() == guards.len()
```

</details>

### flag detection edge cases

#### EDGE: flag at end of args

- EDGE: flag at end of args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: flag at end of args")
val args = ["test", "file.spl", "--json"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### EDGE: flag at beginning (right after command)

- EDGE: flag at beginning (right after command)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: flag at beginning (right after command)")
val args = ["test", "--json", "file.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### EDGE: flag in middle of args

- EDGE: flag in middle of args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: flag in middle of args")
val args = ["test", "a.spl", "--json", "b.spl"]
val needs_rust = args.any(_1 == "--json")
expect needs_rust == true
```

</details>

#### EDGE: flag in middle of args does not swallow the trailing path

- EDGE: flag in middle of args does not swallow the trailing path


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: flag in middle of args does not swallow the trailing path")
# Flag detection above only proves the flag was SEEN. It says nothing
# about the positional paths on either side of it, so it passes
# identically against a parser that drops b.spl. Drive the shipped
# parser so a dropped path is actually observable.
# See doc/08_tracking/bug/
# test_runner_multi_path_drops_all_but_first_2026-08-01.md.
val opts = parse_test_args(["a.spl", "--json", "b.spl"])
expect opts.paths.len() == 2
expect opts.paths[0] == "a.spl"
expect opts.paths[1] == "b.spl"
expect count_positional_args(["a.spl", "--json", "b.spl"]) == 2
```

</details>

#### EDGE: two positional paths with no flag between them

- EDGE: two positional paths with no flag between them


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: two positional paths with no flag between them")
val opts = parse_test_args(["a.spl", "b.spl"])
expect opts.paths.len() == 2
expect opts.paths[0] == "a.spl"
expect opts.paths[1] == "b.spl"
```

</details>

#### EDGE: reversed path order is preserved, not re-sorted or truncated

- EDGE: reversed path order is preserved, not re-sorted or truncated


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: reversed path order is preserved, not re-sorted or truncated")
val opts = parse_test_args(["b.spl", "a.spl"])
expect opts.paths.len() == 2
expect opts.paths[0] == "b.spl"
expect opts.paths[1] == "a.spl"
```

</details>

#### EDGE: two directory targets are both retained

- EDGE: two directory targets are both retained


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: two directory targets are both retained")
val opts = parse_test_args(["test/unit/", "test/integration/"])
expect opts.paths.len() == 2
expect opts.paths[0] == "test/unit/"
expect opts.paths[1] == "test/integration/"
```

</details>

#### EDGE: single path parses to exactly one target

- EDGE: single path parses to exactly one target


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: single path parses to exactly one target")
# The single-path case must stay byte-identical in behaviour: the
# multi-path fix must not add a phantom second target.
val opts = parse_test_args(["a.spl"])
expect opts.paths.len() == 1
expect opts.paths[0] == "a.spl"
expect opts.path == "a.spl"
expect count_positional_args(["a.spl"]) == 1
```

</details>

#### EDGE: value-taking flag does not count as a positional path

- EDGE: value-taking flag does not count as a positional path


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: value-taking flag does not count as a positional path")
# --timeout consumes its value, so only a.spl is positional. The
# parser and the fail-closed counter must agree, otherwise the runner
# aborts a legitimate run.
val opts = parse_test_args(["--timeout", "30", "a.spl"])
expect opts.paths.len() == 1
expect opts.paths[0] == "a.spl"
expect count_positional_args(["--timeout", "30", "a.spl"]) == 1
```

</details>

#### EDGE: only flag, no files

- EDGE: only flag, no files


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: only flag, no files")
val args = ["lint", "--json"]
val needs_rust = args.any(_1 == "--json" or _1 == "--fix")
expect needs_rust == true
```

</details>

#### EDGE: multiple non-rust flags

- EDGE: multiple non-rust flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: multiple non-rust flags")
val args = ["test", "--verbose", "--list", "--show-tags"]
val needs_rust = args.any(_1 == "--json" or _1 == "--watch" or _1 == "--parallel")
expect needs_rust == false
```

</details>

#### EDGE: args[1:] skips command name correctly

- EDGE: args[1:] skips command name correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: args[1:] skips command name correctly")
val args = ["test", "--verbose", "file.spl"]
val check_args = args[1:]
expect check_args.len() == 2
expect check_args[0] == "--verbose"
# Command name itself should never be checked for flags
expect check_args.contains("test") == false
```

</details>

#### EDGE: single letter flag -p matches exactly

- EDGE: single letter flag -p matches exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: single letter flag -p matches exactly")
val args = ["test", "-p"]
val needs_rust = args.any(_1 == "-p")
expect needs_rust == true
```

</details>

#### EDGE: -p is not prefix of -pattern

- EDGE: -p is not prefix of -pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: -p is not prefix of -pattern")
val args = ["test", "-pattern"]
val needs_rust = args.any(_1 == "-p")
expect needs_rust == false
```

</details>

#### EDGE: --capture-screenshots exact match

- EDGE: --capture-screenshots exact match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: --capture-screenshots exact match")
val args = ["test", "--capture-screenshots"]
val needs_rust = args.any(_1 == "--capture-screenshots")
expect needs_rust == true
```

</details>

#### EDGE: --cleanup-runs exact match

- EDGE: --cleanup-runs exact match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: --cleanup-runs exact match")
val args = ["test", "--cleanup-runs"]
val needs_rust = args.any(_1 == "--cleanup-runs")
expect needs_rust == true
```

</details>

#### EDGE: combined rust-only and normal flags

- EDGE: combined rust-only and normal flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: combined rust-only and normal flags")
val args = ["test", "--verbose", "--watch", "--list"]
val needs_rust = args.any(_1 == "--watch")
expect needs_rust == true
```

</details>

#### EDGE: no args at all (just command)

- EDGE: no args at all (just command)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: no args at all (just command)")
val args = ["test"]
val check_args = args[1:]
val needs_rust = check_args.any(_1 == "--json")
expect needs_rust == false
```

</details>

### argument slicing edge cases

#### slice of single-element list is empty

- slice of single-element list is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("slice of single-element list is empty")
val args = ["cmd"]
val rest = args[1:]
expect rest.len() == 0
```

</details>

#### slice preserves all elements

- slice preserves all elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("slice preserves all elements")
val args = ["cmd", "a", "b", "c"]
val rest = args[1:]
expect rest.len() == 3
expect rest[0] == "a"
expect rest[1] == "b"
expect rest[2] == "c"
```

</details>

#### slice of two-element list gives one element

- slice of two-element list gives one element


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("slice of two-element list gives one element")
val args = ["cmd", "arg"]
val rest = args[1:]
expect rest.len() == 1
expect rest[0] == "arg"
```

</details>

#### EDGE: nested slicing

- EDGE: nested slicing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: nested slicing")
val args = ["cmd", "a", "b", "c", "d"]
val rest = args[1:]
val rest2 = rest[1:]
expect rest2.len() == 3
expect rest2[0] == "b"
```

</details>

#### EDGE: slice with negative index

- EDGE: slice with negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: slice with negative index")
val args = ["a", "b", "c", "d"]
val last = args[-1]
expect last == "d"
```

</details>

#### EDGE: full slice is identity

- EDGE: full slice is identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: full slice is identity")
val args = ["a", "b", "c"]
val full = args[0:]
expect full.len() == 3
```

</details>

#### EDGE: slice range

- EDGE: slice range


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: slice range")
val args = ["cmd", "a", "b", "c", "d"]
val mid = args[1:3]
expect mid.len() == 2
expect mid[0] == "a"
expect mid[1] == "b"
```

</details>

#### EDGE: step slice

- EDGE: step slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: step slice")
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

- fmt maps to formatter (not fmt)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fmt maps to formatter (not fmt)")
val cmd = "fmt"
val app_dir = "formatter"
expect cmd != app_dir
```

</details>

#### spipe-docgen maps to spipe_docgen (hyphen to underscore)

- spipe-docgen maps to spipe_docgen (hyphen to underscore)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("spipe-docgen maps to spipe_docgen (hyphen to underscore)")
val cmd = "spipe-docgen"
val app_dir = "spipe_docgen"
expect cmd.contains("-") == true
expect app_dir.contains("-") == false
```

</details>

#### test maps to test_runner_new (not test)

- test maps to test_runner_new (not test)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("test maps to test_runner_new (not test)")
val cmd = "test"
val app_dir = "test_runner_new"
expect cmd != app_dir
```

</details>

#### direct name commands: lint, coverage, verify, dashboard, context, mcp, depgraph, lsp, dap

- direct name commands: lint, coverage, verify, dashboard, context, mcp, depgraph, lsp, dap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("direct name commands: lint, coverage, verify, dashboard, context, mcp, depgraph, lsp, dap")
val direct = ["lint", "coverage", "verify", "dashboard", "context",
              "mcp", "depgraph", "lsp", "dap"]
for cmd in direct:
    val path = "src/app/{cmd}/main.spl"
    expect path.contains(cmd) == true
```

</details>

#### EDGE: command name is not always the directory name

- EDGE: command name is not always the directory name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: command name is not always the directory name")
# These commands have different directory names
val mapped = [["fmt", "formatter"], ["test", "test_runner_new"], ["spipe-docgen", "spipe_docgen"]]
for pair in mapped:
    expect pair[0] != pair[1]
```

</details>

#### EDGE: all app directories are snake_case or single word

- EDGE: all app directories are snake_case or single word


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: all app directories are snake_case or single word")
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

- env guard takes highest priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("env guard takes highest priority")
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

- rust-only flags take second priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rust-only flags take second priority")
val env_set = false
val has_rust_flag = true
val app_exists = true
val use_rust = env_set or has_rust_flag
expect use_rust == true
```

</details>

#### simple app used when no env guard and no rust flags

- simple app used when no env guard and no rust flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("simple app used when no env guard and no rust flags")
val env_set = false
val has_rust_flag = false
val app_exists = true
val use_simple = not env_set and not has_rust_flag and app_exists
expect use_simple == true
```

</details>

#### rust fallback used when app not found

- rust fallback used when app not found


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rust fallback used when app not found")
val env_set = false
val has_rust_flag = false
val app_exists = false
val use_simple = not env_set and not has_rust_flag and app_exists
expect use_simple == false
```

</details>

#### EDGE: env guard overrides even with no rust flags

- EDGE: env guard overrides even with no rust flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: env guard overrides even with no rust flags")
val env_set = true
val has_rust_flag = false
val use_rust = env_set
expect use_rust == true
```

</details>

#### EDGE: app not found with no fallback errors

- EDGE: app not found with no fallback errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("EDGE: app not found with no fallback errors")
val app_exists = false
val has_rust_fallback = false
val error = not app_exists and not has_rust_fallback
expect error == true
```

</details>

### full dispatch simulation

#### simulate fmt dispatch: normal args -> Simple

- simulate fmt dispatch: normal args -> Simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("simulate fmt dispatch: normal args -> Simple")
val args = ["fmt", "file.spl", "--check"]
val env_set = false
val needs_rust = args.any(_1 == "--json")
val app_exists = true
val dispatch = dispatch_decision(env_set, needs_rust, app_exists)
expect dispatch == "simple"
```

</details>

#### simulate fmt dispatch: --json -> Rust

- simulate fmt dispatch: --json -> Rust


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("simulate fmt dispatch: --json -> Rust")
val args = ["fmt", "--json", "file.spl"]
val env_set = false
val needs_rust = args.any(_1 == "--json")
val dispatch = dispatch_decision(env_set, needs_rust, true)
expect dispatch == "rust"
```

</details>

#### simulate fmt dispatch: env guard -> Rust

- simulate fmt dispatch: env guard -> Rust


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("simulate fmt dispatch: env guard -> Rust")
val args = ["fmt", "file.spl"]
val env_set = true
val needs_rust = args.any(_1 == "--json")
val dispatch = dispatch_decision(env_set, needs_rust, true)
expect dispatch == "rust"
```

</details>

#### simulate coverage dispatch: no fallback, app exists -> Simple

- simulate coverage dispatch: no fallback, app exists -> Simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("simulate coverage dispatch: no fallback, app exists -> Simple")
val dispatch = if true: "simple" else: "error"
expect dispatch == "simple"
```

</details>

#### simulate coverage dispatch: no fallback, app missing -> error

- simulate coverage dispatch: no fallback, app missing -> error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("simulate coverage dispatch: no fallback, app missing -> error")
val dispatch = if false: "simple" else: "error"
expect dispatch == "error"
```

</details>

#### simulate test dispatch: --watch -> Rust, normal -> Simple

- simulate test dispatch: --watch -> Rust, normal -> Simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("simulate test dispatch: --watch -> Rust, normal -> Simple")
val args_watch = ["test", "--watch"]
val args_normal = ["test", "my_spec.spl"]
val watch_rust = args_watch.any(_1 == "--watch" or _1 == "--parallel" or _1 == "--json")
val normal_rust = args_normal.any(_1 == "--watch" or _1 == "--parallel" or _1 == "--json")
expect watch_rust == true
expect normal_rust == false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/command_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple app files exist, environment guard naming convention, Rust-only flag detection, dispatch argument construction, app path resolution, non-migrated commands, pure Simple commands (no Rust fallback), hybrid commands (Simple default, Rust fallback), flag detection edge cases, argument slicing edge cases, command to app directory mapping, dispatch decision logic, full dispatch simulation.
- Simple app files exist
- environment guard naming convention
- Rust-only flag detection
- dispatch argument construction
- app path resolution
- non-migrated commands
- pure Simple commands (no Rust fallback)
- hybrid commands (Simple default, Rust fallback)
- flag detection edge cases
- argument slicing edge cases
- command to app directory mapping
- dispatch decision logic
- full dispatch simulation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 111 |
| Active scenarios | 111 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `afaf3a8c217d1d0a7264f5f4e0566b90ab06adc5eacccac2766eea0fa69bba3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afaf3a8c217d1d0a7264f5f4e0566b90ab06adc5eacccac2766eea0fa69bba3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afaf3a8c217d1d0a7264f5f4e0566b90ab06adc5eacccac2766eea0fa69bba3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/app/tooling/command_dispatch_spec.spl
mirror: doc/06_spec/01_unit/app/tooling/command_dispatch_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/tooling/command_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/tooling/command_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/tooling/command_dispatch_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formatter app path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/command_dispatch_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lint app path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/command_dispatch_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spipe_docgen app path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/command_dispatch_spec.spl:480:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test runner uses test_runner_new directory' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/tooling/command_dispatch_spec.spl:879:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test maps to test_runner_new (not test)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
