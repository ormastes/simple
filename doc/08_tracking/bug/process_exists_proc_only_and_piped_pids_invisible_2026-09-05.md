# `process_exists` is /proc-only, and piped-child pids are invisible to `process_is_running`

- **Filed:** 2026-09-05 (lane A9, caret_workbench)
- **Host:** macOS arm64, seed runner `src/compiler_rust/target/bootstrap/simple`
- **Status:** worked around in pure Simple; the two runtime defects are NOT fixed

Two independent defects make every "is this child still alive?" answer wrong on
this host. Both were found while wiring a pane-backed agent team
(`src/app/llm_caret/workbench/pane_team.spl`), where the pane's child IS the
managed agent, so its liveness decides teardown.

## Defect 1 — piped pids live in a different registry from async pids

`rt_process_is_running` and `rt_process_kill`
(`src/compiler_rust/compiler/src/interpreter_extern/system.rs:1257,1281`) look
the pid up in `SPAWNED_PROCESSES`, the table `rt_process_spawn_async` writes.
A child spawned by `rt_process_spawn_piped` is registered elsewhere, so it is
simply "not tracked":

```
piped child spawned, and demonstrably alive (it had just answered a nonce):
  process_is_running(pid) -> false
  process_kill(pid)       -> false
  smux_capture(...)       -> "GOT:abc"     # the same child, responding
```

Consequence: any supervisor that polls a piped child through
`process_is_running` sees it as dead immediately, and any teardown assertion
written as `process_is_running(pid) == false` is **vacuously green** — it was
never true in the first place.

## Defect 2 — the two `rt_process_exists` lanes disagree (dual-implementation divergence)

There are two backings for the same extern, and they do not implement the same
thing:

| lane | file | implementation |
|---|---|---|
| C runtime | `src/runtime/runtime_core_host_services.c:112` | `kill(pid, 0) == 0 \|\| errno == EPERM` — correct everywhere |
| Rust interpreter extern | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:2639` | `Path::new("/proc/<pid>").exists()` under `#[cfg(unix)]`; `true` unconditionally otherwise |

macOS is unix and has no `/proc`, so the Rust lane answers `false` for every
live pid, while the C lane answers correctly. Which one a call reaches depends
on whether the module JIT-compiled (C lane) or dropped to the interpreter (Rust
lane) — measured 2026-09-05: the SAME call on the SAME live pid returned `true`
in a plain `run` and `false` inside a `*_spec.spl`, whose closure had fallen
back to the interpreter. A liveness check whose answer depends on the execution
tier is not a check.

The `#[cfg(not(unix))]` arm returning `true` unconditionally is the opposite
failure and is also wrong.

Compounding it, `fn process_exists(pid: i64) -> bool` is defined a second time
in Simple, with an **identical signature**, in
`src/lib/nogc_sync_mut/test_runner/test_db_validation.spl:61` (and its
`src/app/test_runner_new` twin) — another `/proc` stat. Any program
co-compiling both (every `*_spec.spl`, via `std.spec` -> test_runner) hits the
known `compiler_cross_module_private_symbol_collision` fallback, which resolves
by exact arg-type match and, with two identical signatures, silently takes the
last definition.

## Workaround taken (pure Simple, this lane)

- `src/app/io/process_ops.spl` gains `process_pid_exists(pid)`: a
  **uniquely-named** twin of `process_exists` (so the collision cannot bind it)
  that tries the `/proc` extern first and falls back to `ps -p <pid>` when it
  answers false. That is the OS itself answering on a host with no `/proc`;
  Linux keeps the cheap path.
- `pane_team.spl` polls liveness through `smux_pane_alive`
  (-> `process_is_piped_alive`, the correct registry) and tears down through
  `smux_close_pane` (-> `process_close_piped`, which also reaps), never through
  `process_is_running`/`process_kill`.

## Unblock conditions (each needs the Rust seed, out of scope for this lane)

1. `rt_process_is_running` / `rt_process_kill` should consult the piped
   registry as well as the async one, or the Simple facade should expose the
   distinction instead of a single name that silently means "async only".
2. The Rust interpreter's `rt_process_exists` should use `kill(pid, 0)` like the
   C runtime lane already does, so the two implementations of one extern agree.
3. Rename one of the two Simple `process_exists` definitions so the collision
   cannot occur.

## Evidence / reproduction

`test/03_system/app/llm_caret/caret_workbench_prod_spec.spl` asserts teardown
with `process_pid_exists`; swapping it for `process_is_running` makes the
teardown assertions pass without any process ever being checked, which is the
defect in one line.
