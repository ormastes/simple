# `X test <spec>` never runs the spec under X — child resolver falls back to stale `bin/simple`

**Status:** fixed (pending deploy) — `find_simple_binary()` in
`src/app/test_runner_new/test_runner_single.spl` now resolves the invoking
binary in-process via `rt_path_absolute("/proc/self/exe")` (same primitive as
the CLI's fork-bomb fix, 0531ca8ce266) between the `SIMPLE_BINARY` env check
and the `bin/simple` fallback, and the run header logs `child binary: <path>`.
Note: this doc's Area path said `src/app/test/`; the actual file lives in
`src/app/test_runner_new/`.
**Found:** 2026-07-27 (Simple RISC-V hardening campaign, Lane D reconciliation)
**Area:** `src/app/test/test_runner_single.spl` — `find_simple_binary()` (line ~156),
child spawn at lines ~329/363
**Severity:** high — evidence-integrity: the binary you invoke is silently NOT the
binary that executes the spec

## Finding

`simple test <spec>` does not evaluate the spec in-process. It spawns a **child**
`run <spec>` whose binary is chosen by `find_simple_binary()`:

1. `SIMPLE_BINARY` env var, if set
2. `cli_get_args()[0]`
3. fallback: `bin/simple`

Step 2 is defective: `cli_get_args()[0]` is the **subcommand** (`"test"`), not
argv0, so it never matches an executable and the resolver **always falls through
to `bin/simple`** when `SIMPLE_BINARY` is unset.

Consequence: `/path/to/freshly-built/simple test spec.spl` runs the runner from
the fresh binary but executes the spec under the **deployed `bin/simple`** —
which on this host is a stale seed-clobbered binary.

## How this manifested

Two sessions ran the identical command on the identical tree and got opposite
verdicts:

- With `SIMPLE_BINARY=<fixed binary>`: `Results: 9 total, 9 passed, 0 failed`
- Bare invocation: `error: semantic: variable 'hardware' not found`,
  `1 total, 0 passed, 1 failed` (the stale child predates the `@hardware` fix)

The discrepancy consumed a full verification cycle and briefly produced a wrong
"the seed has a second unfixed interpreter" theory — `interpreter/expr/literals.rs:368`
is merely the error *emitter inside the stale child process*, not a second
decision point. Proof of the actual mechanism: a logging shim set as
`SIMPLE_BINARY` captured exactly one child invocation (`run <spec>`), and setting
it made the same `test` invocation pass.

## Why this is worse than an inconvenience

This is the third evidence-integrity defect found in one day with the same shape —
**the toolchain silently substituting a different binary than the one the
operator believes is under test**:

1. `bin/release/<triple>/simple` seed-clobbered (filed)
2. `check-riscv-fpga-sidecar-contract.shs` anti-seed guard testing path, not
   identity (filed)
3. This: `X test` executing specs under `bin/simple` regardless of X

The SPipe rule "verify which binary produced your evidence" currently cannot be
satisfied for `test` runs at all without knowing about `SIMPLE_BINARY`.

## Reproduction

```bash
cd /home/ormastes/dev/pub/simple
# any spec whose verdict differs between two binaries; then:
/path/to/binary-A test <spec>          # actually executes under bin/simple
SIMPLE_BINARY=/path/to/binary-A /path/to/binary-A test <spec>   # executes under A
```

## Suggested fix

In `find_simple_binary()`, resolve the invoking binary from the true argv0 /
`/proc/self/exe` **in-process** (NOT by shelling out to `readlink` — see the
fork-bomb history in `cli_self_exe_ppid_fork_bomb_2026-07-25`), falling back to
`bin/simple` only when self-resolution fails. Log the chosen child binary path in
the run header so evidence is self-describing.

## Related

- `doc/08_tracking/bug/riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md`
- `doc/08_tracking/bug/riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md`
- `project_cli_self_exe_ppid_fork_bomb_2026-07-25` (why argv0 resolution must be in-process)
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`
