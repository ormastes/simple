# Native session daemon drops execution profile

Status: source repair prepared; native helper and actual daemon execution pending.

Both native argument parsers disabled session routing regardless of the user's
selection. Removing those assignments alone would send native tests to the
generic daemon's unbound `bin/simple test` shell worker. Its path-only cache
could also return a result from a different producer or policy.

The native request now negotiates `native-session-profile-v1`, preserves the
backend and ordered source roots, and binds a compiled standalone runner via
`SIMPLE_TEST_DAEMON_WORKER` and `SIMPLE_TEST_DAEMON_WORKER_SHA256`. The worker
receives `--no-session-daemon --sequential --no-cache --assert-ran`; that private
recursion guard does not alter the caller's requested session route.

The daemon must share the caller's working directory and inherited environment
(apart from shell bookkeeping `_`, `SHLVL`, and `OLDPWD`). The identity retains
execution mode and all MC/DC, waiver, resource, source and tool variables.
Start it with the effective post-configuration environment, including
`SIMPLE_TEST_MODE`, rather than relying on the daemon to mutate global state.
Producer and worker bytes, `SIMPLE_RUNTIME_PATH/libsimple_native_all.a`, the
managed runtime snapshot and managed native tool authority are rehashed before
spawn. Native-build retains responsibility for validating authority members.
The daemon refuses a missing/incompatible profile and the caller does not
fall back to direct native execution. Native requests bypass the legacy cache
entirely. Passing requires a successful bounded child with a nonempty passing
summary, no failures and no pending cases.

Generic SDK fields are line framed. Native requests reject CR/LF/NUL and
surrounding whitespace; native output escapes line breaks to prevent response
field injection. This does not repair legacy daemon response serialization.

Prepared regressions: `test/01_unit/app/test_daemon/native_profile_spec.spl`
and native session cases in `test_runner_args_flags_spec.spl`. They are not
runtime PASS evidence. Required execution gates remain: real generic daemon
plus pinned compiled worker, plain and SSpec green, genuine assertion red,
missing worker/mismatched environment/changed runtime or tool snapshot,
unsupported old daemon, and no daemon all refusing without a direct fallback.

Markdown/comment doctest orchestration has separate entrypoints and remains
outside this source repair's qualification claim. No deployment, release or
production readiness is claimed by this document.
