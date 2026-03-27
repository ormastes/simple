# Simple CLI and simple-mcp Completeness — Design

**Date:** 2026-03-27
**Status:** Draft
**Requirement:** [doc/plan/requirement/simple_cli_mcp_completeness.md](../plan/requirement/simple_cli_mcp_completeness.md)
**Plan:** [doc/plan/simple_cli_mcp_completeness_plan_2026-03-27.md](../plan/simple_cli_mcp_completeness_plan_2026-03-27.md)
**Research:** [doc/research/simple_cli_mcp_completeness.md](../research/simple_cli_mcp_completeness.md)

---

## 1. Module Structure

### Files Modified

| File | Change |
|------|--------|
| `src/app/io/cli_commands.spl` | Replace 12 `cli_not_implemented()` stubs with real implementations or experimental guards |
| `src/app/cli/cli_helpers.spl` | Update `print_cli_help()` to exclude experimental commands from default help |
| `src/app/cli/main.spl` | No dispatch changes needed — all 51 case arms already route correctly |

### Files Created

| File | Purpose |
|------|---------|
| `src/app/cli/command_classification.spl` | `CommandClass` enum and canonical inventory table |
| `test/unit/app/cli_command_inventory_spec.spl` | Inventory drift detection test |
| `test/unit/app/cli_help_alignment_spec.spl` | Help text vs dispatch alignment test |
| `test/unit/app/mcp_inventory_alignment_spec.spl` | MCP tool list vs dispatch alignment test |
| `test/unit/app/cli_mcp_alignment_spec.spl` | CLI/MCP capability matrix test |
| `test/unit/app/mcp_wrapper_contract_spec.spl` | Wrapper timeout/exit-code contract test |

### Files Unchanged (Reference Only)

| File | Reason |
|------|--------|
| `src/app/mcp/main.spl` | Schema-dispatch alignment already clean for all 69 tools |
| `src/app/mcp/main_lazy_protocol.spl` | No schema changes needed |
| `src/app/mcp/main_lazy_*.spl` | 8 family files — classification labeling only, no logic changes |

---

## 2. CLI Changes

### 2.1. Command Classification

A new module `src/app/cli/command_classification.spl` defines the canonical classification:

```simple
enum CommandClass:
    Implemented      # Fully wired, in-process handler
    Delegated        # Routes via cli_run_file() to an app module
    Wrapper          # Shells out to external process
    Experimental     # Infrastructure incomplete, hidden from default help

struct CommandEntry:
    name: text
    class: CommandClass
    handler: text          # Function or module path
    help_visible: bool     # Whether shown in default help
    mcp_peer: Option<text> # Matching MCP tool name, if any

fn canonical_inventory() -> [CommandEntry]:
    # Returns the complete list of 51 commands with classification.
    # This is the single source of truth for inventory tests.
    pass_todo
```

**Classification of all 51 CLI commands:**

| Class | Count | Commands |
|-------|-------|----------|
| Implemented | 11 | `-h`, `-v`, `-c`, `compile`, `targets`, `linkers`, `lex`, `lint`, `fmt`, `fix`, `check` |
| Delegated | 24 | `test`, `duplicate-check`, `grammar-doc`, `query`, `spec-coverage`, `feature-gen`, `task-gen`, `spec-gen`, `sspec-docgen`, `feature-doc`, `todo-scan`, `todo-gen`, `wrapper-gen`, `desugar`, `dashboard`, `office`, `add`, `remove`, `install`, `update`, `list`, `tree`, `cache`, `env` |
| Built-in | 5 | `build`, `init`, `stats`, `leak-check`, `run` |
| Wrapper | 1 | `mcp` |
| Experimental | 5 | `verify`, `migrate`, `constr`, `replay`, `gen-lean` |
| Placeholder (to implement) | 5 | `diff`, `info`, `brief`, `ffi-gen`, `i18n` |

**Correction from research:** `linkers` is NOT a placeholder — `print_linkers()` is fully
implemented in `src/app/cli/main.spl` (lines 112-123). `lex` dispatches through
`run_lex_command()` which delegates to `cli_run_lex()` which IS still a placeholder in
`cli_commands.spl`. The dispatch wiring exists but the handler is a stub.

Also: `web` and `diagram` are placeholders in `cli_commands.spl` (`cli_handle_web`,
`cli_handle_diagram`) but were not listed in the research. These two are application
launchers whose infrastructure does not yet exist. They should be hidden as experimental.

**Revised counts:** 7 placeholders to implement (lex, diff, info, brief, ffi-gen, i18n,
watch), 7 to hide as experimental (verify, migrate, constr, replay, gen-lean, web,
diagram).

### 2.2. Implementing Placeholder Commands (7 commands)

#### `lex` — Tokenize a source file

**Integration point:** `src/compiler/10.frontend/lexer_types.spl` contains token type
definitions. The lexer itself is invoked through the compiler frontend.

**Design:**

```simple
# In src/app/io/cli_commands.spl — replace cli_not_implemented stub
fn cli_run_lex(args: [text]) -> i64:
    val stripped = _cli_strip_command(args, "lex")
    if stripped.len() == 0:
        print "Usage: simple lex <file.spl>"
        return 1
    val path = stripped[0]
    if not rt_file_exists(path):
        _cli_eprint("Error: File not found: {path}")
        return 1
    val source = rt_file_read_text(path) ?? ""
    # Use compiler frontend lexer to tokenize
    use compiler.frontend.lexer.{tokenize}
    val tokens = tokenize(source)
    for tok in tokens:
        print "{tok.kind}\t{tok.span.start}..{tok.span.end}\t{tok.text}"
    0
```

The existing `run_lex_command()` in `main.spl` already delegates to `cli_run_lex()`.
Only `cli_commands.spl` needs the stub replaced.

#### `diff` — Semantic diff between two files

**Integration point:** MCP already has `simple_diff` as a CLI-wrapper tool in
`main_lazy_cli_tools.spl`. The CLI command should use the same underlying diff logic.

**Design:**

```simple
fn cli_run_diff(args: [text]) -> i64:
    val stripped = _cli_strip_command(args, "diff")
    if stripped.len() < 2:
        print "Usage: simple diff <old.spl> <new.spl>"
        return 1
    val old_path = stripped[0]
    val new_path = stripped[1]
    if not rt_file_exists(old_path):
        _cli_eprint("Error: File not found: {old_path}")
        return 1
    if not rt_file_exists(new_path):
        _cli_eprint("Error: File not found: {new_path}")
        return 1
    val old_source = rt_file_read_text(old_path) ?? ""
    val new_source = rt_file_read_text(new_path) ?? ""
    # Line-level diff with context
    use std.common.text_diff.{diff_lines, format_unified_diff}
    val hunks = diff_lines(old_source, new_source)
    val output = format_unified_diff(hunks, old_path, new_path)
    print output
    if hunks.len() > 0: 1 else: 0
```

#### `info` — Project metadata query

**Integration point:** `simple.sdn` manifest parsing already exists in
`cli_helpers.spl` (`read_sdn_run_config`). Extend to dump full manifest.

**Design:**

```simple
fn cli_info(args: [text]) -> i64:
    val current_dir = cwd()
    val sdn_path = "{current_dir}/simple.sdn"
    if not rt_file_exists(sdn_path):
        print "No simple.sdn found in current directory"
        return 1
    val content = rt_file_read_text(sdn_path) ?? ""
    print "Project Info:"
    print content
    # Also show compiler version and target
    val v = get_version()
    print ""
    print "Compiler: Simple v{v}"
    0
```

#### `brief` — Brief project summary for LLM context

**Integration point:** `stats` command already exists and collects project metrics.
`brief` produces a condensed single-paragraph output suitable for LLM context windows.

**Design:**

```simple
fn cli_run_brief(args: [text]) -> i64:
    val stripped = _cli_strip_command(args, "brief")
    val path = if stripped.len() > 0: stripped[0] else: "."
    if not rt_file_exists(path):
        _cli_eprint("Error: Path not found: {path}")
        return 1
    # Delegate to stats with --brief flag
    use app.stats.dynamic.{run_stats}
    run_stats(["--brief", path])
    0
```

#### `ffi-gen` — Generate FFI wrappers from annotations

**Integration point:** `wrapper-gen` already exists at `src/app/wrapper_gen/mod.spl`.
`ffi-gen` is the annotation-driven variant using `@Lib` decorators.

**Design:**

```simple
fn cli_run_ffi_gen(args: [text]) -> i64:
    val stripped = _cli_strip_command(args, "ffi-gen")
    if stripped.len() == 0:
        print "Usage: simple ffi-gen <file.spl>"
        print ""
        print "Generates SFFI wrapper code from @Lib annotations."
        return 1
    # Delegate to wrapper_gen with --from-annotations flag
    val run_args = ["--from-annotations"]
    for arg in stripped:
        run_args.push(arg)
    cli_run_file("src/app/wrapper_gen/mod.spl", run_args, false, false)
```

#### `i18n` — Internationalization tool

**Integration point:** `src/i18n/` has 29 files including string tables for Korean
(`*.ko.spl`), parser, runtime, lint integration. The CLI command should expose
string table management.

**Design:**

```simple
fn cli_run_i18n(args: [text]) -> i64:
    val stripped = _cli_strip_command(args, "i18n")
    if stripped.len() == 0:
        print "Usage: simple i18n <subcommand>"
        print ""
        print "Subcommands:"
        print "  list          List available locales"
        print "  check         Validate string tables for completeness"
        print "  missing       Show missing translations"
        return 1
    # Delegate to i18n module
    cli_run_file("src/i18n/__init__.spl", stripped, false, false)
```

#### `watch` — File watcher (partial)

The `watch` command dispatches to `cli_watch_file()` which prints
"Watch mode not yet implemented in pure Simple" and returns 1. This is effectively
a placeholder. The watch-daemon infrastructure exists (`cli_watch_daemon_start()`)
and should be reused:

```simple
fn cli_watch_file(path: text) -> i64:
    use compiler.driver.watcher.watcher_types.{watcher_config_default}
    use compiler.driver.watcher.watcher_daemon.{watcher_daemon_start}
    use app.io.{thread_sleep_ms}

    var config = watcher_config_default()
    config.watch_paths = [path]
    val daemon = watcher_daemon_start(config)
    if not daemon.is_running():
        _cli_eprint("Failed to start file watcher")
        return 1
    print "Watching {path} for changes..."
    while daemon.is_running():
        daemon.run_poll_cycle()
        thread_sleep_ms(config.poll_interval_ms)
    0
```

### 2.3. Hiding Experimental Commands (7 commands)

Commands to hide from default help: `verify`, `migrate`, `constr`, `replay`,
`gen-lean`, `web`, `diagram`.

**Pattern:** Replace `cli_not_implemented()` with a guarded stub that prints
experimental status and exits:

```simple
fn cli_experimental(tool_name: text) -> i64:
    print "[experimental] {tool_name} is not yet available."
    print "This command is under development and hidden from default help."
    print "Run 'simple --help-all' to see all commands including experimental."
    1
```

Apply to each:

```simple
fn cli_run_verify(args: [text], gc_log: bool, gc_off: bool) -> i64:
    cli_experimental("Formal verification (verify)")

fn cli_run_migrate(args: [text]) -> i64:
    cli_experimental("Migration tool (migrate)")

fn cli_constr(args: [text]) -> i64:
    cli_experimental("Constraint checker (constr)")

fn cli_replay(args: [text]) -> i64:
    cli_experimental("Replay tool (replay)")

fn cli_gen_lean(args: [text]) -> i64:
    cli_experimental("Lean4 code generator (gen-lean)")

fn cli_handle_web(args: [text]) -> i64:
    cli_experimental("Web application server (web)")

fn cli_handle_diagram(args: [text]) -> i64:
    cli_experimental("Diagram generator (diagram)")
```

### 2.4. Help Text Update Pattern

**In `src/app/cli/cli_helpers.spl`:**

1. Remove the "Verification" section (lines 78-81) from default help — those commands
   become experimental.
2. Remove "LLM-Friendly Tools" > `diff` and `brief` entries temporarily until
   implemented, then restore them.
3. Add a new `--help-all` flag that shows the full help including experimental commands.
4. Add `[experimental]` tag next to any experimental command shown in `--help-all`.

**Modified help structure:**

```simple
fn print_cli_help():
    # ... existing sections ...
    # REMOVE: Verification section
    # REMOVE: web, diagram from implicit sections
    # ADD at end:
    print ""
    print "Use --help-all to see experimental commands."

fn print_cli_help_all():
    print_cli_help()
    print ""
    print "Experimental (not yet stable):"
    print "  simple verify <file.spl>    [experimental] Formal verification"
    print "  simple gen-lean generate    [experimental] Lean4 verification files"
    print "  simple migrate              [experimental] Code migration"
    print "  simple constr               [experimental] Constraint checking"
    print "  simple replay               [experimental] Execution replay"
    print "  simple web                  [experimental] Web application server"
    print "  simple diagram              [experimental] Diagram generation"
```

**Dispatch addition in `main.spl`:**

```simple
case "--help-all":
    print_cli_help_all()
    return 0
```

---

## 3. MCP Changes

### 3.1. Tool Family Classification Model

No new MCP tools are needed. The 69 existing tools are already schema-dispatch aligned.
The design adds a classification label system for documentation and testing.

**Family maturity model:**

```simple
enum ToolMaturity:
    Stable         # Fully tested, production-ready
    Beta           # Functional but limited test coverage
    Experimental   # May change or be removed

enum ToolType:
    Native         # In-process, direct function call
    Wrapper        # Shells out to bin/simple or external tool
    IPC            # Communicates via file-based IPC (test daemon)

struct ToolClassification:
    name: text
    family: text
    tool_type: ToolType
    maturity: ToolMaturity
    timeout_ms: i64         # 0 = no timeout, >0 = enforced
    mutating: bool
    handler_file: text
```

**Classification table:**

| Family | Count | Type | Maturity | Timeout | Handler File |
|--------|-------|------|----------|---------|--------------|
| Debug | 25 | Native | Stable | 30000 | `main_lazy_debug_tools.spl` |
| Debug Log | 6 | Native | Stable | 10000 | `main_lazy_debug_log_tools.spl` |
| Diagnostics | 9 | Wrapper | Beta | 60000 | `main_lazy_diag_tools.spl` |
| VCS | 8 | Wrapper | Stable | 30000 | `main_lazy_vcs_tools.spl` |
| Query | 8 | Wrapper | Beta | 60000 | `main_lazy_query_tools.spl` |
| CLI Wrapper | 6 | Wrapper | Beta | 120000 | `main_lazy_cli_tools.spl` |
| Task | 3 | Native | Stable | 0 | `main_lazy_tasks.spl` |
| Test Daemon | 4 | IPC | Beta | 30000 | `main_lazy_test_daemon_tools.spl` |

### 3.2. Wrapper Contract

All 35 wrapper-based MCP tools must satisfy these invariants:

1. **Timeout policy:** Every wrapper tool declares a maximum execution time in
   milliseconds. If the subprocess exceeds this, the tool returns an error result
   with `isError: true` and a timeout message. Default: 60000ms.

2. **Output normalization:** Wrapper tools capture stdout and stderr separately.
   The MCP result `content[0].text` contains stdout. Stderr is included in a
   second content block if non-empty. No raw binary output.

3. **Exit status surfacing:** The subprocess exit code is included in the result
   metadata. Non-zero exit codes set `isError: true` on the MCP response.

4. **No recursive invocation:** Wrapper tools that shell out to `bin/simple` must
   not invoke commands that themselves shell out to `bin/simple`. The call graph
   is: MCP tool -> `bin/simple <cmd>` -> in-process handler. No deeper nesting.

**Implementation pattern in wrapper tool handlers:**

```simple
fn handle_wrapper_tool(tool_name: text, args: [text], timeout_ms: i64) -> ToolResult:
    val cmd = "bin/simple " + args.join(" ")
    val result = shell_with_timeout(cmd, timeout_ms)
    if result.timed_out:
        return ToolResult.error("Tool '{tool_name}' timed out after {timeout_ms}ms")
    var content = [TextContent(text: result.stdout)]
    if result.stderr.len() > 0:
        content.push(TextContent(text: "stderr: {result.stderr}"))
    ToolResult(content: content, isError: result.exit_code != 0)
```

### 3.3. No New MCP Tools

The research confirmed all 69 tools have schema and dispatch coverage. No new tools
are needed for this completeness effort. The work is:

- Add maturity labels to tool annotations (documentation-level, no protocol change)
- Add wrapper contract tests
- Add inventory drift tests

---

## 4. CLI/MCP Alignment Matrix

### 4.1. Workflow-to-Surface Mapping

| Workflow | CLI Command | MCP Tool | Canonical Surface |
|----------|-------------|----------|-------------------|
| **Build** | `simple build` | `simple_build` | Both |
| **Test** | `simple test` | `simple_test` | Both |
| **Lint** | `simple lint` | `simple_lint` | Both |
| **Format** | `simple fmt` | `simple_format` | Both |
| **Fix** | `simple fix` | `simple_fix` | Both |
| **Check** | `simple check` | `simple_check` | Both |
| **Run** | `simple run` / `simple <file>` | `simple_run` | Both |
| **Diff** | `simple diff` | `simple_diff` | Both |
| **Query** | `simple query` | `simple_search`, `simple_symbols`, `simple_sem_query`, `simple_ast_query`, `simple_query_schema` | Both (MCP richer) |
| **VCS status** | (none) | `simple_status`, `simple_log` | MCP-only |
| **VCS commit** | (none) | `simple_commit`, `simple_push`, `simple_pull`, `simple_rebase`, `simple_squash` | MCP-only |
| **Edit** | (none) | `simple_edit`, `simple_multi_edit` | MCP-only |
| **Read** | (none) | `simple_read` | MCP-only |
| **Context** | (none) | `simple_context` | MCP-only |
| **New file** | (none) | `simple_new` | MCP-only |
| **Doc coverage** | `simple doc-coverage` | `simple_doc_coverage` | Both |
| **Stats** | `simple stats` | (none) | CLI-only |
| **Init** | `simple init` | (none) | CLI-only |
| **Package mgmt** | `simple add/remove/install/update/list/tree` | (none) | CLI-only |
| **REPL** | `simple` (no args) | (none) | CLI-only |
| **Debug** | (none) | 25 debug tools | MCP-only |
| **Debug log** | (none) | 6 debug log tools | MCP-only |
| **Task mgmt** | (none) | `task_list`, `task_status`, `task_cancel` | MCP-only |
| **Test daemon** | `simple test-daemon` | 4 test daemon tools | Both |
| **Dependencies** | (none) | `simple_dependencies` | MCP-only |
| **API diff** | (none) | `simple_api`, `simple_api_diff` | MCP-only |

### 4.2. Intentional Divergences

| Divergence | Rationale |
|------------|-----------|
| VCS tools MCP-only | VCS is inherently interactive; MCP gives structured state to LLM agents. CLI users use `jj` or `git` directly. |
| Edit/Read MCP-only | File editing through MCP supports structured multi-edit with rollback. CLI users use their editor. |
| Debug tools MCP-only | DAP/GDB orchestration is session-based. MCP provides the session management layer. CLI users connect debuggers directly. |
| Stats CLI-only | Human-readable output best suited for terminal. MCP users get equivalent data through query tools. |
| Package mgmt CLI-only | Interactive package operations are CLI workflows. MCP users can shell out via `simple_run`. |

---

## 5. Inventory Test Design

### 5.1. CLI Inventory Drift Test

**File:** `test/unit/app/cli_command_inventory_spec.spl`

**Approach:** Derive the expected command list from `canonical_inventory()` in
`command_classification.spl`. Compare against the actual case arms in the dispatch.

```simple
use app.cli.command_classification.{canonical_inventory, CommandClass}

describe "CLI command inventory":
    it "has no unclassified commands":
        val inventory = canonical_inventory()
        for entry in inventory:
            # Every command must have a non-default classification
            expect(entry.class).to_not_equal(CommandClass.Unknown)

    it "has no placeholder commands in default help":
        val inventory = canonical_inventory()
        val visible = inventory.filter(\e: e.help_visible)
        for entry in visible:
            expect(entry.class).to_not_equal(CommandClass.Experimental)
            # Verify handler is not cli_not_implemented
            expect(entry.handler).to_not_equal("cli_not_implemented")

    it "accounts for exactly 51 commands":
        val inventory = canonical_inventory()
        expect(inventory.len()).to_equal(51)
```

### 5.2. CLI Help Alignment Test

**File:** `test/unit/app/cli_help_alignment_spec.spl`

**Approach:** Parse `print_cli_help()` output for command names. Verify every listed
command exists in the canonical inventory and is not experimental.

```simple
describe "CLI help alignment":
    it "does not advertise experimental commands":
        # Capture help output
        val help_text = capture_help_output()
        val experimental = ["verify", "migrate", "constr", "replay",
                           "gen-lean", "web", "diagram"]
        for cmd in experimental:
            expect(help_text).to_not_contain("simple {cmd}")

    it "advertises all implemented commands":
        val help_text = capture_help_output()
        val required = ["test", "lint", "fmt", "fix", "check", "build",
                       "compile", "lex", "diff", "info", "brief"]
        for cmd in required:
            expect(help_text).to_contain(cmd)
```

### 5.3. MCP Inventory Alignment Test

**File:** `test/unit/app/mcp_inventory_alignment_spec.spl`

**Approach:** Derive expected tool list from `make_tool_schema()` in
`main_lazy_protocol.spl`. Verify every listed tool has a dispatch handler in
`handle_tool_call()`.

```simple
describe "MCP tool inventory alignment":
    it "has dispatch for every schema-listed tool":
        val schema_tools = get_schema_tool_names()
        val dispatch_tools = get_dispatch_tool_names()
        for tool_name in schema_tools:
            expect(dispatch_tools).to_contain(tool_name)

    it "has schema for every dispatched tool":
        val schema_tools = get_schema_tool_names()
        val dispatch_tools = get_dispatch_tool_names()
        for tool_name in dispatch_tools:
            expect(schema_tools).to_contain(tool_name)

    it "has exactly 69 tools":
        val schema_tools = get_schema_tool_names()
        expect(schema_tools.len()).to_equal(69)
```

### 5.4. CLI/MCP Alignment Test

**File:** `test/unit/app/cli_mcp_alignment_spec.spl`

**Approach:** For dual-surface workflows, verify both CLI and MCP entry points exist.

```simple
describe "CLI/MCP alignment":
    it "has MCP peers for dual-surface commands":
        val dual_surface = [
            ("build", "simple_build"),
            ("test", "simple_test"),
            ("lint", "simple_lint"),
            ("fmt", "simple_format"),
            ("fix", "simple_fix"),
            ("check", "simple_check"),
            ("diff", "simple_diff"),
            ("doc-coverage", "simple_doc_coverage"),
        ]
        for (cli_cmd, mcp_tool) in dual_surface:
            val cli_exists = canonical_inventory().any(\e: e.name == cli_cmd)
            val mcp_exists = get_schema_tool_names().contains(mcp_tool)
            expect(cli_exists).to_equal(true)
            expect(mcp_exists).to_equal(true)
```

### 5.5. MCP Wrapper Contract Test

**File:** `test/unit/app/mcp_wrapper_contract_spec.spl`

**Approach:** For each wrapper tool, verify timeout declaration exists and output
normalization produces valid text content.

```simple
describe "MCP wrapper contract":
    it "all wrapper tools declare timeout":
        val wrappers = get_wrapper_tool_names()
        for tool_name in wrappers:
            val classification = get_tool_classification(tool_name)
            expect(classification.timeout_ms).to_be_greater_than(0)

    it "wrapper tools surface exit code in result":
        # Test with a known-good wrapper tool
        val result = invoke_tool("simple_lint", {"path": "test/fixtures/clean.spl"})
        expect(result.content.len()).to_be_greater_than(0)
        expect(result.content[0].type).to_equal("text")
```

---

## 6. Integration Points

### Per-Command Integration Map

| Command | Integrates With | Module Path |
|---------|----------------|-------------|
| `lex` | Compiler frontend lexer | `src/compiler/10.frontend/lexer_types.spl`, tokenizer in frontend |
| `diff` | Text diff library | `src/lib/common/text_diff/` (or new module) |
| `info` | SDN manifest parser | `src/app/cli/cli_helpers.spl` (`read_sdn_run_config`, `sdn_line_indent`) |
| `brief` | Stats module | `src/app/stats/dynamic.spl` (`run_stats`) |
| `ffi-gen` | Wrapper generator | `src/app/wrapper_gen/mod.spl` (existing app with `--from-annotations` flag) |
| `i18n` | I18n string tables | `src/i18n/__init__.spl` (29 files, Korean locale support) |
| `watch` | Watcher daemon | `src/compiler/driver/watcher/` (existing SHB+SMF daemon) |
| `verify` | (experimental) | No backend yet — formal verification is future work |
| `migrate` | (experimental) | No migration system exists |
| `constr` | (experimental) | Constraint solver in `src/compiler/30.types/` is internal |
| `replay` | (experimental) | No replay infrastructure |
| `gen-lean` | (experimental) | Lean4 codegen is future work |
| `web` | (experimental) | No web server app exists |
| `diagram` | (experimental) | No diagram generator exists |

### Shared Infrastructure

The following modules are used by multiple commands and must remain stable:

- `cli_run_file()` — shared delegation mechanism for 24 commands
- `cli_not_implemented()` — being replaced, but the function signature remains for
  any future placeholder needs
- `_cli_strip_command()` — arg parsing helper used by all new implementations
- `_cli_eprint()` — stderr output (used by all error paths)
- `rt_file_exists()` / `rt_file_read_text()` — FFI file operations (used by lex, diff, info)

### MCP Integration Points

No new MCP-to-CLI wiring is needed. The existing wrapper tools already call
`bin/simple <cmd>` for the relevant commands. When placeholder CLI commands are
implemented, the corresponding MCP wrapper tools will automatically gain real
functionality without any MCP-side changes.

Specifically:
- `simple_diff` (MCP) wraps `simple diff` (CLI) — will work once `cli_run_diff` is implemented
- `simple_lint`, `simple_build`, etc. already work because the CLI commands are implemented

---

## 7. Implementation Order

### Wave 1: Classification and Inventory Tests (no behavior changes)

1. Create `src/app/cli/command_classification.spl`
2. Create `test/unit/app/cli_command_inventory_spec.spl`
3. Create `test/unit/app/mcp_inventory_alignment_spec.spl`
4. Tests should pass against current state (inventories match current reality)

### Wave 2: Placeholder Elimination

1. Implement `lex`, `diff`, `info`, `brief`, `ffi-gen`, `i18n`, `watch` in `cli_commands.spl`
2. Add `cli_experimental()` guard for `verify`, `migrate`, `constr`, `replay`, `gen-lean`, `web`, `diagram`
3. Update help text in `cli_helpers.spl`
4. Add `--help-all` flag
5. Create `test/unit/app/cli_help_alignment_spec.spl`

### Wave 3: MCP Hardening

1. Add wrapper contract documentation to tool family files
2. Create `test/unit/app/mcp_wrapper_contract_spec.spl`
3. Create `test/unit/app/cli_mcp_alignment_spec.spl`

### Wave 4: Verification

1. Run full test suite
2. Verify `simple --help` has no experimental commands
3. Verify `simple --help-all` shows all commands
4. Verify inventory tests pass
5. Verify MCP `tools/list` count remains at 69

---

## 8. Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| `lex` implementation requires deep compiler frontend coupling | Use the existing tokenizer entry point; output is line-per-token, no AST needed |
| `diff` needs a text diff library that may not exist in stdlib | Implement minimal line-diff in `src/lib/common/text_diff/` if needed; unified diff format only |
| `ffi-gen` flag (`--from-annotations`) may not be supported by wrapper-gen | Extend wrapper-gen to accept the flag, or create a thin adapter |
| `i18n` CLI entry point assumes `__init__.spl` handles subcommands | Verify `src/i18n/__init__.spl` can accept CLI args; add subcommand routing if needed |
| Hiding commands from help may break scripts that parse help output | `--help-all` preserves full output; standard help is for human consumption |
| Inventory tests couple to exact command count (51 CLI, 69 MCP) | Tests verify count AND content; adding a command requires updating the canonical inventory |
