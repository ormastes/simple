# `simple test` intermittently aborts: "Module count limit (800) exceeded loading light_protocol.spl"

- **Filed:** 2026-08-08
- **Severity:** High — `simple test` is the verification oracle most lanes depend on.
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  deployed binary is rebuilt** — see *Mitigation now*.
- **Pre-existing:** reproduces against the pre-`2139afa0c90` `origin/main` blob.
  Not introduced by the child-binary resolution fix.

## Mitigation now (no rebuild, works today)

```bash
SIMPLE_MODULE_LIMIT=4000 bin/simple test <spec>
```

Do **not** use `SIMPLE_MODULE_LIMIT=0`. Zero means *unlimited*; the guard exists
to stop the loader OOMing the box, and `earlyoom` is running here with `simple`
on its preferred-kill list.

Also safe today: `bin/simple test <spec> --no-session-daemon` — that route loads
only **43** modules and cannot hit the ceiling (see measurements).

## Symptom

```
error: runtime: Module count limit (800) exceeded loading
  "/home/ormastes/dev/pub/simple/src/app/test_daemon/light_protocol.spl".
  Too many transitive imports.
```

The run aborts with **no `SPEC FILE VERDICT` line**, which is indistinguishable
from the spec under test failing. It is not — nothing under test ever ran. Some
lanes' "verified" results may in fact have been these aborts.

## Root cause

The limit is not being crossed by repeated or duplicate module loading. It is
crossed because the `simple test` client's own import graph sits **at** the
ceiling.

Measured 2026-08-08 with `SIMPLE_LOADER_TRACE=1`, counting
`^\[loader-trace\] loaded:` lines:

| command | unique modules loaded |
|---|---|
| `bin/simple test test/02_integration/simple_launcher_dispatch_spec.spl` | **789** (787 on an earlier run) |
| `bin/simple test test/unit/multi_mode_test_runner_spec.spl` | **800** ← exactly at the limit |
| `bin/simple test <either> --no-session-daemon` | **43** |
| `bin/simple run src/app/test_runner_new/test_runner_client.spl` | **787** |

**Zero repeat loads.** `sort | uniq -c` over the 787 loaded paths returns count
`1` for every single path. There is no leak, no missing cache, and no
failure-to-reset between spec files (`clear_module_cache()` in
`driver/src/cli/test_runner/execution.rs:561` resets `TOTAL_MODULES_LOADED` per
test file, and the spec itself runs in a *different* process from the client).

So the graph is legitimately ~787–800 modules against a 800 ceiling: **0–1.6%
headroom.**

### `light_protocol.spl` is innocent

It is simply the **last** module in the client's import graph (last `use` line in
`src/app/test_runner_new/test_runner_client.spl`, and last `loaded:` line in the
trace). Whatever the limit is set to, it is the module that gets named. Proof —
forcing the limit down reproduces the exact production string at any value:

```
$ SIMPLE_MODULE_LIMIT=786 bin/simple test test/02_integration/simple_launcher_dispatch_spec.spl
error: runtime: Module count limit (786) exceeded loading ".../light_protocol.spl". ...
$ SIMPLE_MODULE_LIMIT=787 bin/simple test test/02_integration/simple_launcher_dispatch_spec.spl
error: runtime: Module count limit (787) exceeded loading ".../light_protocol.spl". ...
```

Control: the same commands at the default limit (800) pass with
`SPEC FILE VERDICT: ... declared>=4 executed=4 passed=4 failed=0 dropped=0`.

### What varies (the intermittency)

The count is **not** fixed. Two things move it:

1. **Which spec is being run.** 789 vs 800 for two specs measured back to back
   on the same binary and the same tree. The daemon-client process resolves
   spec-adjacent modules, so the spec contributes to the same counter.
2. **Run-to-run drift on the same spec** — 787 then 789 for
   `simple_launcher_dispatch_spec.spl`, and any working-tree change that adds a
   module to the graph moves it further. With ≤13 modules of headroom, a single
   added `use` anywhere in the 787-module closure tips a passing lane into an
   abort. In this shared working copy, parallel sessions edit that closure
   continuously.

The `--no-session-daemon` route (43 modules) never trips, which is why
"it vanished under `--no-session-daemon`" has been a recurring observation.

### The real over-import (the thing worth fixing properly)

**746 of the 787 modules — 95%, including all 537 `src/compiler/**` modules —
come from one import line.** Attribution from the trace: 41 modules are loaded
before line 3603, where
`use std.test_runner.test_runner_modes.{run_spl_doctest_mode}`
(`test_runner_client.spl:9`) begins resolving; 746 are loaded after it.

Breakdown of the 787 by tree: `src/compiler` **538**, `src/std` 174,
`src/lib` 38, `src/app` 37.

That single symbol is used in exactly one place —
`run_scoped_spl_doctest()` (`test_runner_client.spl:259`), reachable only when
`--spl-doctest` is on the command line. So a client whose job is to encode a
request file and hand it to a daemon eagerly loads the **entire pure-Simple
compiler** on every single `simple test` invocation. That is also why the
client's startup is slow: `test_runner_modes.spl` alone took **22,396 ms** to
load in the traced run.

Fixing that would drop the client from ~790 to ~45 modules and make the ceiling
irrelevant. It is **not** landed here because it cannot be done live: the
`--spl-doctest` handling would have to move out of the client, and
`src/app/test_runner_new/test_runner_single.spl` (the `--no-session-daemon`
target) does not implement `--spl-doctest`, while
`test_runner_main.spl:875` does. Routing `--spl-doctest` to `test_runner_main`
requires editing `test_should_use_light_daemon_client` in
`src/compiler_rust/driver/src/main.rs:235` — a Rust change, which is not live
until a rebuild. Landing the `.spl` half alone would silently drop
`--spl-doctest`. Tracked as follow-up below.

## Fix landed

**Implementation changed: Rust seed only** (`src/compiler_rust/**`). There is no
pure-Simple twin — `grep -rn "SIMPLE_MODULE_LIMIT\|module_limit" --include=*.spl src/`
returns nothing. The limit lives solely in the seed's interpreter module loader.
No runtime-C twin either.

1. `src/compiler_rust/compiler/src/memory_guard.rs` — `DEFAULT_MODULE_LIMIT`
   **800 → 4000**, with the measurement recorded in the comment. Justified
   because there is provably no duplicate loading: raising it is not deferring a
   perf defect, it is giving a legitimately-large graph a real budget instead of
   a knife-edge. 4000 is ~5x the measured graph, restoring the headroom the
   constant was presumably meant to have.
2. `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs` —
   the exceeded-limit path now prints an unmistakable, deliberately
   **non-verdict-shaped** banner to stderr:
   - states `HARNESS ABORT (module loader) — this is NOT a test/spec failure`
     and that nothing under test executed,
   - reports the actual count reached and the limit,
   - states explicitly that the named module is the **last** in the graph and
     almost never the cause,
   - prints the `SIMPLE_MODULE_LIMIT=` mitigation and the
     `SIMPLE_LOADER_TRACE=1 | grep -c` diagnosis recipe,
   - warns against `SIMPLE_MODULE_LIMIT=0`.
   The returned `CompileError::Runtime` string carries the same framing so it
   is legible even where only the error text is captured.

Verified with `cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler`
— clean (the 2 warnings are pre-existing, in `interpreter_call/block_execution.rs`).

### Remaining step — this is NOT live yet

`bin/release/x86_64-unknown-linux-gnu/simple` was deliberately **not** redeployed
(≈10 sessions depend on it, and Stage-3 self-host is currently blocked — see
`.claude/rules/bootstrap.md`). The deployed binary keeps the 800 limit and the
old message until someone rebuilds and redeploys. Until then, lanes must use
`SIMPLE_MODULE_LIMIT=4000` or `--no-session-daemon`.

## Follow-ups (separate defects, not the 800 cause)

- **Client over-import.** Move `--spl-doctest` handling out of
  `test_runner_client.spl` and route it to `test_runner_main.spl`
  (`test_should_use_light_daemon_client`, `driver/src/main.rs:235`). Drops the
  client from ~790 to ~45 modules and removes ~22 s of startup.
- **`src/std -> lib` symlink defeats stdlib cache retention.** `src/std` is a
  symlink to `src/lib`. Loader traces show `src/std/...` paths, while
  `clear_module_cache_selective()`'s `is_stdlib()`
  (`src/compiler_rust/compiler/src/module_cache.rs:114`) matches only the
  literal substrings `src/lib/` / `src\lib\`. If those paths are not
  canonicalized before the `retain`, the stdlib-retention optimization is a
  no-op and stdlib is re-parsed for every test file. Candidate explanation for
  the 22,396 ms `test_runner_modes.spl` load. Needs its own measurement.

## Reproduction / control

```bash
# Reproduce the exact production error string (any tree state):
SIMPLE_MODULE_LIMIT=786 bin/simple test test/02_integration/simple_launcher_dispatch_spec.spl

# Control (passes, emits a real verdict):
bin/simple test test/02_integration/simple_launcher_dispatch_spec.spl

# Measure the count for any command:
SIMPLE_LOADER_TRACE=1 <cmd> 2>&1 | grep -c '^\[loader-trace\] loaded:'
# Prove there is no duplicate loading:
SIMPLE_LOADER_TRACE=1 <cmd> 2>&1 | grep '^\[loader-trace\] loaded:' \
  | awk '{print $3}' | sort | uniq -c | sort -rn | head
```
