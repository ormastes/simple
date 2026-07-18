# Logging and Print Guidance

Use `print` for scripts, examples, tests, and intentionally human-facing CLI output.

Production source under `src/app/`, `src/lib/`, and `src/compiler/` should use structured logging APIs instead: `log`, `info`, `warn`, `error`, `debug`, or `trace`. The lint pipeline emits `LOG001` for bare `print` in those production roots while retaining script print allowance elsewhere.

Debug and trace logging must be suppressible in production paths. Hardware access, external process/file/network access, and trace capture should use the AOP/debug logging path when available so `debug_log_tree` can expose foldable human and compact LLM views.

Compiler AOP logging policy lives in `src/compiler/10.frontend/core/aop_log_policy.spl`.
Hardware and external-access joins are audit signals and remain weaveable in
release builds. Debug and trace joins are optional instrumentation; release
builds omit them unless debug logging is explicitly enabled.

Compiler-inserted debug logging is controlled by global AOP knobs:

| Variable | Meaning |
|----------|---------|
| `SIMPLE_AOP_LOG_CALLS=1` | Enable function-call join-point logging. |
| `SIMPLE_AOP_LOG_ASSIGNMENTS=1` | Enable variable-assignment join-point logging. |
| `SIMPLE_AOP_COMPILE_LOG_LEVEL=<level>` | Compile-time instrumentation level; defaults to `debug`. Use `off` to suppress compiler AOP debug instrumentation. |
| `SIMPLE_AOP_RUNTIME_LOG_LEVEL=<level>` | Runtime level attached to generated log calls; independent from compile-time filtering. |

The disabled/default path reads the effective policy and returns before MIR
join-point scanning, so ordinary builds do not pay per-call or per-assignment
compile-time instrumentation work. When only one join-point flag is enabled,
the compiler builds only that rule set.

For temporary debugging, prefer these AOP knobs over editing source with
removable log calls. Keep manual `log()` calls for state AOP cannot observe
cleanly, such as cross-process protocol frames, hardware status, or summarized
domain values; lower their log level when they are no longer needed at the
previous verbosity.

Bare-metal builds use the no-host-service policy helpers in
`src/os/baremetal/profile/log_policy.spl`. They expose separate compile/runtime
levels plus independent function-call and variable-assignment AOP switches
without environment lookup or hosted runtime dependencies.

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
has a `test/02_integration/app/*_log_modes_spec.spl` source-mode spec covering the
shared help or readiness path, invalid mode rejection, and at least one
command-specific JSON or progress path.

For human TUI progress, use `SimpleProgressGroup` with
`render_tui_grouped_counts`. The renderer emits a stable grouped count view with
status, completed/total counts, and percent per group.
