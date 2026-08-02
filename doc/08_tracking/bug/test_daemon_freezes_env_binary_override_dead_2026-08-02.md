# The test daemon freezes the environment, so a binary override is silently dead

- **Date:** 2026-08-02
- **Status:** fixed (client-side lane bypass); protocol-level fix still open
- **Severity:** measurement integrity — affected specs fail silently *green*
- **Evidence tier:** Rust seed (`bin/simple`; bootstrap-identity probe
  `strings bin/simple | grep -c "enum construction: unregistered enum"` = 0)

## Summary

`bin/simple test <spec>` does not normally run the spec in the process you
launched. When the request qualifies (`test_should_use_light_daemon_client` in
`src/compiler_rust/driver/src/main.rs`), the path is handed to a long-lived
helper, `src/app/test_daemon/light_daemon.spl`, through a request file.

The v1 request encoding carries **no environment**:

```
fn light_request_encode(path: text, expiry_micros: i64) -> text:
    "{LIGHT_REQUEST_V1_HEADER}\n{expiry_micros}\n{path}"
```

The daemon's own environment is whatever the invocation that first started it
happened to have, and it then outlives that invocation by minutes. Every
subsequent `bin/simple test` run therefore executes spec bodies under a
**stale, frozen environment** — silently.

For the ~39 specs that resolve *which binary they exercise* from the
environment, this means the override the caller named is discarded and the spec
goes on testing the default `bin/simple` under the name of the selected one.

## Reproduction (measured)

```
$ <kill any running light_daemon>
$ SIMPLE_TEST_BINARY=VALUE_FIVE bin/simple test <probe> --no-db
PROBE env_get(SIMPLE_TEST_BINARY)=[VALUE_FIVE]     <- correct, this run started the daemon
PROBE SHELL_SEES=[VALUE_FIVE]

$ SIMPLE_TEST_BINARY=VALUE_SIX  bin/simple test <probe> --no-db
PROBE env_get(SIMPLE_TEST_BINARY)=[VALUE_FIVE]     <- WRONG: replays the previous run
PROBE SHELL_SEES=[VALUE_FIVE]                      <- WRONG
```

An unrelated variable set only in the *first* run (`SIMPLE_MEM_PROBE_SENTINEL=HELLO`)
also kept reappearing in later runs that never set it, which is what identified
the frozen-environment mechanism. The process holding it was confirmed directly:

```
pid=2067913 cmd=src/compiler_rust/target/debug/simple run src/app/test_daemon/light_daemon.spl
```

## The workaround that does NOT work

Commit `c6e30f3a745` diagnosed this as "the runner does not surface that
variable to spec bodies" and fixed it by resolving the override in the child
shell — `"${SIMPLE_TEST_BINARY:-bin/simple}"` — instead of via `env_get`.

**That does not fix it.** The child shell is forked *by the daemon*, so it
inherits the daemon's frozen environment too. In the transcript above,
`SHELL_SEES` is wrong on exactly the same runs where `env_get` is wrong. The
shell form appeared to work only because the run that exercised it happened to
be the run that started the daemon.

The true axis is not *how the spec spells the lookup* — it is *which process
the spec body runs in*. Both spellings are live with no daemon running, and
both are dead with a stale one.

## Fix

`src/app/test_runner_new/test_runner_client.spl` already carried the precedent:
`SIMPLE_COVERAGE` bypasses the daemon lane because "the daemon's environment
predates this request". The binary-override family is the same defect class,
one step worse because it fails silently rather than merely under-reporting.

Any request naming `SIMPLE_TEST_BINARY`, `SIMPLE_BINARY`, `SIMPLE_BIN`,
`SIMPLE_SEED_BINARY` or `SIMPLE_SPEC_COMPILER` now takes the direct lane. None
of these is set in a normal run, so the daemon lane is unaffected on the hot
path.

Verified after the fix, with a daemon alive throughout:

```
binary-override: SIMPLE_TEST_BINARY set; bypassing test daemon so the override reaches the spec
PROBE env_get(SIMPLE_TEST_BINARY)=[VALUE_SEVEN]
PROBE SHELL_SEES=[VALUE_SEVEN]
```

Regression coverage:
`test/03_system/check/test_daemon_env_override_passthrough_spec.spl`
(deliberately seeds a daemon from a non-overridden invocation first, then
asserts both channels observe the caller's value).

## Still open

The protocol-level fix. `light_request_encode`/`light_request_parse` should
carry the client's environment (a v2 request) so that *any* env-sensitive spec
is correct on the daemon lane, not just the names enumerated above. Until then,
any NEW env var that selects behaviour inside a spec body is silently stale on
the daemon lane unless it is added to `_binary_override_vars()`.

## Results this invalidates

Any past verdict from a spec whose binary override was supposed to select a
non-default binary, when a daemon was already running, was produced against
`bin/simple` regardless of what was requested. In particular the sabotage
control in `c6e30f3a745` — "pointing the override at a deliberately broken
binary and the spec still passed" — was correct as an *observation* but was
misattributed to `env_get`; the shell-based replacement it motivated is
equally dead, so that spec's override remained non-decisive until this fix.

## Second, independent vacuity found during the sweep

Several of the sibling specs also carry a **self-heal fallback ladder**: if the
selected binary's output does not contain the expected marker, they silently
re-run against `src/compiler_rust/target/{release,debug}/simple`. With the
override now genuinely delivered, pointing these at a *nonexistent* binary
still leaves them green, because the ladder swallows the failure. So for these,
the override is delivered but **not decisive** — a broken selected binary
cannot turn them red. Measured (daemon killed before every run, override
pointed at a stub that exits 42):

| spec | override delivered | broken binary turns it red? |
|------|--------------------|------------------------------|
| test/01_unit/compiler/interp/mem_guard_rate_spec.spl | yes | no — ladder masks it |
| test/01_unit/runtime/mem_attr_gate_spec.spl | yes | no — ladder masks it |
| test/03_system/check/doctest_lane_symmetry_contract_spec.spl | yes | yes — 6/6 failed |

The ladders are deliberate (they absorb a deployed binary that predates a newly
added extern), so removing them is a separate decision, but they must not be
mistaken for override coverage.
