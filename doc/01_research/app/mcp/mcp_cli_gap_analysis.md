# MCP vs CLI Gap Analysis & Enhancement Plan

## MCP-Only Features (No CLI Equivalent)

| Category | MCP Tools | Count |
|----------|-----------|-------|
| Debug Sessions | create/step/continue/breakpoint/variables/stack/evaluate/watch | 16 |
| Hardware Debug | trace_capture, coverage, flash, reset, practice_script, openocd | 6 |
| Debug Logging | log_enable/disable/clear/query/tree/status | 6 |
| Background Tasks | task_status/cancel/list | 3 |
| Test Daemon IPC | daemon_run/clean/status/stop | 4 |
| VCS Workflow | log/squash/new/commit/push/rebase/pull | 7 |

**Total: 42 MCP-only tools** with no CLI equivalent.

Everything else (diagnostics, query, search, build, test, format, lint) has a direct CLI command.

---

## Proposed CLI Enhancements

### 1. Brief/Refined Output Mode

Add `--brief` flag to commands that produce verbose output:

```
bin/simple check file.spl              # full output
bin/simple check file.spl --brief      # summary: 3 errors, 2 warnings
bin/simple query workspace-symbols X   # full results
bin/simple query workspace-symbols X --brief  # top 5 matches only
```

**Implementation**: Truncate content to top N items, show count + `(N more...)`.

### 2. Command Log Management

New subcommand `bin/simple log`:

```
bin/simple log last              # full output of last command
bin/simple log <id>              # full output by hash id
bin/simple log list              # recent command ids + summaries
```

Every command execution writes to `.build/command_log/` with:
- Hash ID (short sha of timestamp + command)
- Command name, args, exit code
- Full stdout/stderr capture
- Duration

**Response format**:
```
[a3f2c1] check src/app/cli/main.spl (0.8s, exit 1)
  3 errors, 2 warnings
```

### 3. Diagnostic-Merged File Read

New flag on read/check:

```
bin/simple read file.spl --diagnostics   # file content + inline diagnostics
```

Output merges file lines with diagnostics:

```
 14 | fn process(x: i64):
 15 |     val result = compute(x)
    |         ~~~~~~ warning: unused variable 'result' [W0012]
 16 |     retrun x + 1
    |     ^^^^^^ error: unknown identifier 'retrun', did you mean 'return'? [E0001]
```

### 4. Context/Search with Response Refinement

```
bin/simple context file.spl              # check + symbols + deps summary
bin/simple search "pattern" --context    # search with surrounding code context
```

---

## LSP Diagnostic Expression Across Language Servers

All follow LSP spec severity levels 1-4:

| Severity | Label | Usage |
|----------|-------|-------|
| 1 | **Error** | Parse/type errors blocking compilation |
| 2 | **Warning** | Likely bugs, unused code, deprecation |
| 3 | **Information** | Suggestions, non-bug diagnostics |
| 4 | **Hint** | Simplifications, modernizations |

### Per-Server Notes

**rust-analyzer**: Translates rustc JSON (`--error-format=json`). Includes error codes (E0308), multi-span diagnostics with primary/secondary labels, help/note sub-diagnostics. Warnings from clippy lints.

**Pyright/pylsp**: Rule-based codes (e.g., `reportMissingImports`). Zero-based line/char. pylsp integrates plugins (pycodestyle, mypy, ruff). Pyright has strict/basic/off per-rule config.

**TypeScript (tsserver)**: Event-based (`semanticDiag`, `syntaxDiag`, `suggestionDiag`). Error codes are numeric (TS2304). Suggestions delivered as severity 4 (hint) with diagnostic tags.

**clangd**: Standard LSP format. Fix-it suggestions as code actions. Diagnostic groups from clang-tidy checks. Known bug: sometimes reports severity 0 (invalid).

**gopls**: Error = parse/type errors. Warning = analyzer findings (likely bugs). Info = unused code. Hint = simplifications. Async `publishDiagnostics`. Diagnostics from both compilation and analysis passes.

### Common Display Pattern in Editors

```
filename:line:col: severity: message [code]
  |
  | source line
  | ^^^^^^ underline annotation
  |
  = note: additional context
  = help: suggestion
```

---

## MCP Structured Content Response Format

### Dual Response (MCP spec 2025-06-18)

```json
{
  "content": [
    { "type": "text", "text": "human-readable summary" }
  ],
  "structuredContent": {
    "diagnostics": [...],
    "count": 5,
    "truncated": false
  }
}
```

- **content**: For model consumption, token-efficient
- **structuredContent**: For machine parsing, schema-validated

### Brief vs Full Mode Strategy

| Mode | content text | structuredContent |
|------|-------------|-------------------|
| Brief | ~500 chars, top 3-5 items | `truncated: true, hasMore: true` |
| Full | Complete output | `truncated: false` |

Control via tool parameter (`--brief` or `--max-results N`). Default: brief.

---

## Response ID Format

All command responses include a short hash for log retrieval:

```
[a3f2c1] command_name (duration, exit_code)
  brief summary
  (use `bin/simple log a3f2c1` for full output)
```

Hash: first 6 chars of SHA-256(timestamp + command + args).
