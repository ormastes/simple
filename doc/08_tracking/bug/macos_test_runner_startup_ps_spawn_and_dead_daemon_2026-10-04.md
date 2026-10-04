# macOS `simple test` startup: per-module `ps` spawns (FIXED) and an unusable light daemon (OPEN)

- Status: part 1 FIXED (this change), parts 2-3 OPEN
- Host: macOS arm64 (Darwin 25.5), Rust seed built from `origin/main` @ `f0b730f458b`

## 1. FIXED — `read_rss_bytes()` forked `ps` on every call

`src/compiler_rust/compiler/src/watchdog.rs` read RSS on macOS by running
`ps -o rss= -p <pid>`. It is called twice per loaded module
(`ModuleLoadGuard::enter` + drop, `interpreter_module/module_loader.rs`) and
every 100 ms by the watchdog thread whenever `SIMPLE_TIMEOUT_SECONDS` is set
(the directory test runner sets it for every spec child). `sample` of
`simple test --no-session-daemon <tiny spec>` showed ~60% of the main thread
in `__posix_spawn`/`poll` under this function.

Fix: `proc_pidinfo(PROC_PIDTASKINFO)` — the same kernel counter `ps` reports,
floored to whole KB so the value is identical. Pinned by
`watchdog::tests::test_read_rss_bytes_matches_ps_on_macos`.

Measured (same host, alternating before/after, daemon dir cleared per run):

| command | before wall / user / sys | after wall / user / sys |
|---|---|---|
| `simple test <4-line spec>` (client lane) | 10.06s / 1.84 / 1.83 | 5.94s / 1.12 / 0.39 |
| `simple test --no-session-daemon <same>` | 3.47s / 0.71 / 0.71 | 1.94s / 0.42 / 0.15 |
| `simple test browser_engine/html_tokenizer_spec.spl` | 11.84s / 2.36 / 2.04 | 8.14s / 1.52 / 0.53 |

## 2. OPEN — the light daemon cannot identify its own binary on macOS

`src/app/test_daemon/light_daemon.spl` `invoking_binary()` only reads
`/proc/self/exe`, so on macOS it falls through to `"./bin/simple"` and records
that in `.build/test_daemon_light/daemon.binary`. The client
(`test_runner_client.spl`) then always prints
`invoking-binary: test daemon identity is unavailable or mismatched` and runs
directly. Net effect per cold `simple test <spec>`: a whole extra interpreter
process is spawned, the client polls up to 40x50 ms for its lock, and the
daemon then idles 60 s — pure waste. Not fixed here because making the daemon
lane live on macOS changes which process executes specs (frozen-environment
hazards documented in the client). The client's `cli_current_exe_path()`
resolver is the likely fix.

## 3. OPEN — `simple test <directory>` fails on the seed

`simple test test/01_unit/lib/common/aes/` (routes to
`src/app/test_runner_new/main.spl`) exits 1 after ~36-48 s with
`error[E1002]: function \`as\` not found`, after a JIT attempt demotes on
`HIR lowering error: Cannot infer field type: struct 'CostEstimate' field
'scalar_cost'`. Identical before and after part 1, so the "Session setup"
phase cannot be measured on this host via the seed.
