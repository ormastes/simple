# Cached phase2 resolves the resource-scope shell local as a function

Canonical ID: `phase2_resource_scope_shell_shadow_2026_10_28`
Status: OPEN; source workaround active; authoritative DB reconciliation pending.
Owner: compiler local-name/function-value resolution; next admitted compiler rebuild.

After PR #5170 repaired capture pointer/length transport, the native runner still
failed every bounded child launch. LLDB on the existing phase2-built runner showed
`rt_process_run_bounded_tuple` receiving ARM64 instruction bytes as its command.
The stack passed through `_run_with_unix_limits` and `_legacy_process_fallback`.
The local `shell` binding collides with a global function name in this producer.

Evidence: `/tmp/test-runner-refresh-20261028/child-launch.lldb.log` and
`qualification-patched/`. Original source recovery: `74c4f7c879b`.
Producer: existing `stage2-simple-aliasfix` under
`/Users/ormastes/wt/release-phase2-review/build/verify/pure-spl-aliasfix-p2-20261025-02/`.
The compiler is intentionally not rebuilt in this task.

Workaround: rename only the `_run_with_unix_limits` local to `limit_shell_path`.
Its tagged source and this report are committed before native qualification;
the workaround commit is discoverable with `git log -S phase2_resource_scope_shell_shadow_2026_10_28`.
Retirement requires a new admitted producer and an original-name reproducer that
executes real scoped children. A source rename does not fix the compiler.

Prevention: the native capture fixture now covers the runner's scope entry,
pid-capped and ordinary POSIX shells, empty/spaced/quoted/UTF-8 arguments,
stdout/stderr, child exit 7, missing executable, and timeout classification.
The standalone gate verifies all 11 named cases independently of runner status.
Native runner acceptance uses positive, negative and empty BDD, SSpec, plain SPL,
Markdown and source-comment fixtures; all receipts are retained separately.

Qualification results: pending.
