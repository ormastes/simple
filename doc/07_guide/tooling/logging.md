# Logging and Print Guidance

Use `print` for scripts, examples, tests, and intentionally human-facing CLI output.

Production source under `src/app/`, `src/lib/`, and `src/compiler/` should use structured logging APIs instead: `log`, `info`, `warn`, `error`, `debug`, or `trace`. The lint pipeline emits `LOG001` for bare `print` in those production roots while retaining script print allowance elsewhere.

Debug and trace logging must be suppressible in production paths. Hardware access, external process/file/network access, and trace capture should use the AOP/debug logging path when available so `debug_log_tree` can expose foldable human and compact LLM views.

Compiler AOP logging policy lives in `src/compiler/10.frontend/core/aop_log_policy.spl`.
Hardware and external-access joins are audit signals and remain weaveable in
release builds. Debug and trace joins are optional instrumentation; release
builds omit them unless debug logging is explicitly enabled.

Shared CLI log option parsing lives in `std.cli.log_modes`. App entrypoints
that expose structured startup, status, dry-run, or planning output should
accept `--log-mode <human|llm|json>`, `--stdout`, `--tui`, and
`--progress <summary|count|dot|none>`. The parser also accepts shorthand
`--human`, `--llm`, `--json`, `--dots`, `--count`, `--quiet`, and
`--verbose`. Use `render_progress` for consistent summary, count, dot, and
quiet/no-progress output.

Log-mode preflight paths must be startup-light. Help, version, JSON readiness,
invalid-option, and dry-run planning paths should avoid importing broad
compiler, UI, network, terminal, or subprocess graphs before the preflight can
return. Real execution paths may still delegate to their heavier implementation
after shared log options are parsed and stripped.

The current app rollout covers the main `src/app/*/main.spl` command surface,
including MCP/LSP wrappers and grouped commands such as add/remove, bug
add/resolve, session-plan, UI browser/chromium, and Wine hello. Each wired app
has a `test/integration/app/*_log_modes_spec.spl` source-mode spec covering the
shared help or readiness path, invalid mode rejection, and at least one
command-specific JSON or progress path.

For human TUI progress, use `SimpleProgressGroup` with
`render_tui_grouped_counts`. The renderer emits a stable grouped count view with
status, completed/total counts, and percent per group.
