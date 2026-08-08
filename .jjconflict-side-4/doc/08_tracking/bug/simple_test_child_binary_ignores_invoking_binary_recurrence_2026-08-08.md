# `simple test` child binary still ignores the invoking binary — a rebuilt seed silently tests with the stale deployed one

- **ID:** simple_test_child_binary_ignores_invoking_binary_recurrence_2026-08-08
- **Status:** FIXED 2026-08-08 (see "Root cause" and "Fix" below)
- **Severity:** high (measurement trap — a verified-looking fix run is executed
  by a binary that does not contain the fix)
- **Date:** 2026-08-08
- **Prior:** `test_runner_child_binary_ignores_invoking_binary_2026-07-27.md`

## Symptom

Running a spec with a freshly rebuilt compiler:

```
$ src/compiler_rust/target/release/simple test test/unit/lib/zz_ann_probe_spec.spl
...
child binary: /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
error: semantic: variable `noalloc` not found
Results: 1 total, 0 passed, 1 failed
```

The spec is executed by the **stale deployed** binary, not the invoking one, so
the run reports the pre-fix behaviour and looks like "the fix did not work".
With `SIMPLE_BINARY` pointed at the same rebuilt binary, the identical spec
passes 1/1.

## Root cause (2026-08-08) — the `/proc/self/exe` step was NOT the failure

The `/proc/self/exe` step in `test_runner_single.spl` worked correctly the whole
time. It resolves the exe of *the process interpreting that script* — and that
process had **already been chosen wrongly one hop earlier**.

`simple test <spec>` is a three-process chain:

```
<invoked binary>  test <spec>
  -> test_runner_new/test_runner_client.spl      simple_binary()   <-- DEFECT
       -> (direct lane)  <chosen> test --no-session-daemon <spec>
       -> (daemon lane)  light_daemon.spl        simple_binary()   <-- DEFECT
            -> <chosen> run test_runner_new/test_runner_single.spl <spec>
                 -> find_simple_binary()  /proc/self/exe  (CORRECT, but the
                    process is already the wrong binary)
```

Three sibling `simple_binary()` resolvers — `test_runner_client.spl`,
`test_daemon/light_daemon.spl`, `test_daemon/main.spl` — each cross-referenced
"same fix as test_runner_single.spl's simple_binary()" but **none of them
actually carried the `/proc/self/exe` step**:

- they checked `cli_get_args()[0]`, which here is the SUBCOMMAND / this script's
  own `.spl` path, so it never matches `*/simple` and always falls through;
- then they returned the hardcoded `bin/simple` — the **deployed** binary;
- `test_runner_client.spl` / `light_daemon.spl` did contain a literal
  `/proc/self/exe` candidate, but **BELOW** the `bin/simple` check, so it was
  dead code on any machine with a deployed binary.

So the answer to "unset, overridden, resolved before a chdir, lost across a
re-exec, or preferred-below something else?" is: **preferred-below — and in two
of the three resolvers, absent entirely.** The 2026-07-27 fix was applied to the
last hop of the chain only.

The **daemon lane is worse than a lookup-order bug**: the light daemon is a
long-lived process pinned to whichever binary spawned it, and the v1 request
carries only a path + expiry — no binary. A daemon started by an earlier session
serves *every* later session's specs with its own compiler, so no lookup order in
the client can fix it.

## Fix

Pure-Simple only (`src/app/**`). **No Rust-seed twin is needed:** the seed's own
`find_simple_binary()` (`src/compiler_rust/driver/src/cli/test_runner/execution.rs:1566`)
already prefers `std::env::current_exe()` over its candidate list, and the seed's
`test` delegates into these `.spl` runners anyway (the `child binary:` line is
printed by `test_runner_single.spl`).

1. `src/app/test_runner_new/test_runner_client.spl`,
   `src/app/test_daemon/light_daemon.spl`, `src/app/test_daemon/main.spl`:
   new `invoking_binary()` (canonicalize `/proc/self/exe` in-process, never
   shell out), placed **above** the `bin/simple` / debug-seed candidate list.
   An explicit `SIMPLE_BINARY` still wins — that is the one legitimate reason to
   run a spec on a binary other than the invoking one, and it is now preserved
   explicitly rather than by fall-through.
2. Daemon lane: `light_daemon.spl` publishes the binary it serves to
   `.build/test_daemon_light/daemon.binary`; the client compares it against its
   own invoker and **bypasses the daemon on mismatch**, printing
   `invoking-binary: live test daemon runs X but this process is Y; bypassing
   daemon ...`. A daemon predating the record is treated as `bin/simple`, which
   is what every pre-fix daemon actually used.
3. `test_runner_single.spl` now fails loud: when the resolved child binary is
   not the invoking one and `SIMPLE_BINARY` is unset it prints
   `WARNING: child binary <X> is NOT the invoking binary <Y>; this run does not
   measure the invoking compiler`.

## Verification (positive control — asserts WHICH binary ran)

Probe: `test/fixtures/binprov/binary_provenance_probe_spec.spl`.
Invoker `src/compiler_rust/target/release/simple` (md5 `3b192713…`) vs deployed
`bin/release/x86_64-unknown-linux-gnu/simple` (md5 `bd545788…`).

| run | client | lane | `child binary:` |
|-----|--------|------|-----------------|
| before | origin | daemon | `…/bin/release/x86_64-unknown-linux-gnu/simple` (WRONG, rc=0 green) |
| before | origin | direct (`--timeout 700`) | `…/bin/release/x86_64-unknown-linux-gnu/simple` (WRONG, rc=0 green) |
| after | fixed | direct (daemon-mismatch bypass) | `…/src/compiler_rust/target/release/simple` (CORRECT) |
| after | fixed | daemon (freshly spawned) | `…/src/compiler_rust/target/release/simple` (CORRECT) |
| control | reverted to origin blob | daemon | `…/bin/release/…/simple` again (WRONG) — defect returns |
| after | fixed, restored | direct | `…/src/compiler_rust/target/release/simple` (CORRECT) |

Both lanes reproduced the defect and both are fixed. The control run is the
point: it was `rc=0`, `1 passed, 0 failed` — a green run that measured a
compiler the caller never built.

## Why the 2026-07-27 guard did not hold

`find_simple_binary()` (`src/app/test_runner_new/test_runner_single.spl:158`)
is supposed to resolve the invoking binary in-process via
`rt_path_absolute("/proc/self/exe")` precisely to avoid this. In this
configuration that step did not yield the invoking binary and resolution fell
through to `bin/simple`. The 2026-07-27 fix is therefore not covering the
"run a non-deployed binary directly" case.

## Impact

Anyone who rebuilds the seed to verify a compiler fix and then runs
`<rebuilt> test <spec>` gets a **silently stale** result. This is the same class
of trap as the `bin/simple run` script-directory stdlib resolution finding
(which invalidated a 4-row table cited as authoritative four times).

## Reading a run after the fix

`SIMPLE_BINARY` is no longer required to get the right child; it remains the
explicit override. **Still read the `child binary:` line** — it is the evidence,
and a `WARNING: child binary ... is NOT the invoking binary` now names any
remaining divergence instead of leaving it silent.

## Follow-up not done here

The light-request protocol (`app/test_daemon/light_protocol.spl`) is still v1:
path + expiry, no environment and no binary. The daemon.binary record + bypass
closes the binary hole; the *environment* hole (a daemon freezing env selectors,
already documented in `test_runner_client.spl`'s `_binary_override_vars` note)
is still handled by an allowlist that must stay closed over the family. A v2
request carrying the caller's binary + selected env would retire both.
