# `exp` app CLI: experiment script execution falls back to usage/help text instead of delegating
## FIXED 2026-11-25 — see Resolution section at bottom
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-20
**Component:** `src/app/exp/main.spl` CLI script-delegation path
**Severity:** Low-Medium — single isolated example; 4 of 5 examples in the
spec file pass
**Found by:** whole-suite triage campaign,
`test/02_integration/app/exp_log_modes_spec.spl`

## Symptom

```simple
it "delegates experiment script execution":
    val (out, err, code) = _run_exp_temp_script()
    expect(code).to_equal(0)
    expect(out).to_contain("exp-run-ok")
```

fails: expected `out` to contain the marker `exp-run-ok` (which the target
temp script presumably prints when actually executed), but actual output
starts with the CLI's own usage banner (`usage: 0/1 (0%)\nexp - Experiment
Tracking CLI...`) — i.e. the `exp` CLI printed its help/usage text instead
of delegating to and running the temp script.

## Root-cause hypothesis

Not root-caused to the exact dispatch code in `src/app/exp/main.spl`
(time-boxed triage). Looks like whatever argument shape `_run_exp_temp_script()`
constructs (helper not inspected in depth here) isn't being recognized by
the CLI's script-delegation branch, so it falls through to the default
usage-printing path — consistent with either an arg-parsing gap or the
delegation subcommand having a different expected invocation shape than the
test provides.

## Note

Spec left unmodified — could not confirm from source whether the test's
invocation shape or the CLI's dispatch is out of sync; flagging as a
genuine gap.


## Resolution 2026-11-25 (p2w2-ab lane, Windows x86_64, pinned seed `bin/simple.exe` v1.0.0-rc.1)

**Status: FIXED.**

Root cause (two cooperating gaps, confirmed empirically):

1. The seed's `run` arg forwarding drops ALL script args when a second
   `.spl`-suffixed argument follows the run target: `bin/simple run
   build/argprobe.spl run foo.spl` delivers `argc=0` to the script, while
   `run foo.txt` delivers both args and a lone `foo.spl` is kept. With
   `argc=0`, `exp` main falls into the help branch — exactly the usage banner
   the spec saw. Inserting the `--` separator (`run <target> -- run foo.spl`)
   forwards everything, including a literal `--` as `args[0]`.
2. `src/app/exp/main.spl` did not strip that leading `--`, so even the
   separator shape landed on `Unknown command: --` + help. Three other app
   mains already strip it (`src/app/build/submodule_verify_main.spl:12`,
   `src/app/build/scheduler/worker_main.spl:16`,
   `trusted_ssh_probe_main.spl:12`) — the exp CLI was out of sync with that
   convention.

Fix (minimal, both sides):

- `src/app/exp/main.spl`: strip a leading `--` from the cleaned args, the
  same one-liner convention as `worker_main.spl`.
- `test/02_integration/app/exp_log_modes_spec.spl`: the delegation helper now
  invokes `["src/app/exp/main.spl", "--", "run", script_path]` — the `--`
  separator is required for `.spl` script args to survive the seed's `run`
  arg forwarding. Assertions unchanged.

Evidence (spec-harness runs are environment-blocked at HEAD — the pinned
binary rejects `@representation_boundary` in
`src/app/test_runner_new/test_runner_client.spl` — so each example was
replicated with the fixture's exact invocation shape,
`bin/simple.exe run src/app/exp/main.spl [args]`, `SIMPLE_LIB=src`):

- BEFORE: `... main.spl run <probe.spl>` (and `-- run <probe.spl>`) printed
  the usage banner; `exp-run-ok` absent.
- AFTER: `-- run <probe.spl>` prints `exp-run-ok` (inner
  `./bin/simple run <probe.spl>` delegation executed), exit 0.
- Regression probes, all matching the spec's expectations: `--help` -> code 0
  with `Usage: exp` / `--log-mode` / `--progress`; `--log-mode=json` -> code 0
  `{"command":"exp","status":"ready"}`; `--progress=dot --help` -> code 0,
  output starts with `.`, contains `Usage: exp`; `--log-mode=noisy` -> code 1.

Limit: the seed's `.spl`-arg drop itself is Rust-seed arg-parsing behavior and
was not changed (seed is bootstrap-only). The `--` separator convention works
on both the seed and the self-hosted CLI contract.
