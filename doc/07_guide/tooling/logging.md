# Logging and Print Guidance

Use `print` for scripts, examples, tests, and intentionally human-facing CLI output.

Production source under `src/app/`, `src/lib/`, and `src/compiler/` should use structured logging APIs instead: `log`, `info`, `warn`, `error`, `debug`, or `trace`. The lint pipeline emits `LOG001` for bare `print` in those production roots while retaining script print allowance elsewhere.

Debug and trace logging must be suppressible in production paths. Hardware access, external process/file/network access, and trace capture should use the AOP/debug logging path when available so `debug_log_tree` can expose foldable human and compact LLM views.

Compiler AOP logging policy lives in `src/compiler/10.frontend/core/aop_log_policy.spl`.
Hardware and external-access joins are audit signals and remain weaveable in
release builds. Debug and trace joins are optional instrumentation; release
builds omit them unless debug logging is explicitly enabled.

Shared CLI log option parsing lives in `std.cli.log_modes`. Apps should accept
`--log-mode <human|llm|json>`, `--stdout`, `--tui`, and
`--progress <summary|count|dot|none>` where they expose structured output.
Use `render_progress` for consistent summary, count, dot, and quiet/no-progress
output.

`simple brief` is the first wired app entrypoint. It accepts the shared help
text, rejects invalid log modes, treats `--log-mode=json` as JSON output, and
uses `render_progress` for non-default progress modes.

For human TUI progress, use `SimpleProgressGroup` with
`render_tui_grouped_counts`. The renderer emits a stable grouped count view with
status, completed/total counts, and percent per group.
