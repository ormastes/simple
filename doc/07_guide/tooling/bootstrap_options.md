# `bootstrap-from-scratch.sh` option surface

Authoritative map of every flag of `scripts/bootstrap/bootstrap-from-scratch.sh`,
read out of the script at `origin/main` and re-verified by RUNNING `--help` and
each subcommand after the 14-scripts-to-2 consolidation (`dc86db785b4`,
2026-08-23). Covers the positional **subcommands** and the `BOOTSTRAP_LIB_ONLY=1`
sourcing contract as well as the flags. Companion to
`doc/07_guide/tooling/bootstrap_phase_verification.md` (phase -> artifact map).

**This script is the only sanctioned way to run any bootstrap stage.** Do not
hand-type the stage `native-build` lines; every flag on them is load-bearing
(`scripts/check/check-sanctioned-bootstrap-invocation.shs`).

## Entry policy: the receipt gate

Running bare exits **64** with
`bootstrap-policy-error: reason-receipt-required`. That is policy, not breakage.
Two ways past it:

| lane | invocation |
|---|---|
| receipt-free (the sole one) | `--strategy=adhoc --full-bootstrap --stop-after-stage2 --output=<dir>` |
| planned | `--bootstrap-receipt=<path>` from `src/app/build/bootstrap_receipt_main.spl` |

Receipt validation also exits 64 on `malformed-or-untrusted-planner-admission-v2`
and `planner-admission-target-mismatch`. `--validate-bootstrap-receipt` validates
and exits 0 with `execution=not-attempted` — it never starts a stage.

## Strategies — `--strategy=adhoc|normal|full` (default `normal`)

A **failure policy and scheduling** choice, *not* a lighter build. There is no
reduced-closure stage-1 path in this repo.

| value | meaning |
|---|---|
| `adhoc` | fail-fast failure policy |
| `normal` | default; reuses incremental caches, schedules isolated phase verification |
| `full` | inventories every eligible build and test to a terminal summary even after task crashes |

Validated by `bootstrap_strategy_validate`, which now lives inside
`bootstrap-from-scratch.sh` itself (line ~104) — the old
`scripts/bootstrap/bootstrap-cache-policy.shs` no longer exists (see
"Subcommands" below). Unknown values exit 1. Env: `SIMPLE_BOOTSTRAP_STRATEGY`. Unless
`SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1`, the script re-execs itself under the
coordinated strategy supervisor; `--help`, `--validate-bootstrap-receipt`,
`--stop-after-stage2`, `--stop-after-stage3`, the two `--resume-*` flags,
`--diagnostic-sweep`, and `--target=simpleos-*|freebsd-*` bypass the supervisor.

## Modes — `--mode=dynload|one-binary` (default `dynload`)

| value | meaning |
|---|---|
| `dynload` | stages consume compiler/app/lib edits through dynload native caches; the full CLI relink is skipped unless asked for |
| `one-binary` | single linked artifact; **implies `--full-cli`** |

Unknown values exit 1. Env: `SIMPLE_BOOTSTRAP_MODE`. `SIMPLE_NO_STUB_FALLBACK=1`
makes staged failures fatal.

**The Rust seed does not implement `--mode=dynload`.** `native_build.rs` defaults
to `one-binary` and its own `--help` says so verbatim: `(dynload is not
implemented by the Rust seed and is skipped)`
(`src/compiler_rust/driver/src/cli/native_build.rs:815-816`; the module header at
`:26` and `:44` states the same). So a stage driven by the seed silently runs
one-binary regardless of what you asked for, with that note as the only signal.
Only pure-Simple stages honour `dynload`.

## Flags

| flag | effect |
|---|---|
| `--full-cli` | Stage 4: relink the full CLI (`src/app/cli/main.spl`) with the verified stage3 compiler. Native Linux/macOS hosts only. **Implied by `--deploy` and `--mode=one-binary`.** Without it the run prints `Pure-Simple dynload build complete; full CLI relink skipped.` Refuses to run on a seed fallback (`exit 2`) — a full CLI is only ever built by a provenance-verified stage2/stage3 compiler. |
| `--pure-simple` | Compatibility alias for the default no-Rust-rebuild mode. Conflicts with `--full-bootstrap` (exit 1). |
| `--deploy` | Copy the resulting compiler artifact into `bin/simple`. Sets `full_cli=1`. |
| `--release` | `--deploy` plus the release-blocking whole test suite (Stage 6). |
| `--release-local` | Alias for `--release` (same code path — one `case` arm, script line ~4152). Exists so a local release lane reads differently from CI; it changes nothing. |
| `--clean-release` | Final release proof: sets execution profile `clean-release`, `--fresh-cache`, release tests, and deploy. Clears every reusable native cache before each batch. |
| `--stop-after-stage2` | With `--full-bootstrap`: build and admit the measured Stage-2 trust root, then stop. **The sole receipt-free lane.** Excludes Stage 3/4, resume, `--full-cli`, deploy, release and diagnostic options, and requires `--mode=dynload`. Conflicts with `--resume-stage3-from-admitted`. |
| `--stop-after-stage3` | Stop after producing and independently verifying the provenance-bound Stage 3 compiler. Requires a planner receipt targeting `//bootstrap:stage3`; never starts Stage 4/deploy/release/diagnostics; same exclusion set as above. |
| `--resume-stage3-from-admitted=<output>` | Resume only Stage 3 from OUTPUT's frozen admitted Stage 2 on a new one-thread recovery lane. Mutually exclusive with rebuild/deploy/diagnostic options; only `--jobs=1` (it execs `resume-stage3-from-admitted.sh`, which pins `--threads 1`). |
| `--resume-stage4-from-admitted=<output>` | Continue at Stage 4 from OUTPUT's provenance-admitted Stage 3 without rebuilding or mutating Stage 2/3. **Requires `--deploy`**, only `--jobs=1`; sets `output_dir` and `full_cli=1`. |
| `--diagnostic-sweep` | Continue checking independent `.spl` files after failures, group all diagnostics, and **never build or deploy artifacts**. |
| `--incremental-unlimited` | Execution profile `incremental-unlimited`: reuse incremental caches including one-binary Stage 4, use every detected host CPU, retain Stage 4 structural streaming ownership. |
| `--verbose` | Accepted for compatibility. |
| `--no-mcp` | Skip the MCP server builds (Stage 5). |
| `--progress[=<path>]` | Append milestone/liveness samples. Default `<output>/bootstrap-progress.log`; env `SIMPLE_BOOTSTRAP_PROGRESS_LOG`. **The heartbeat is ON by default** — a stage can run 15+ minutes writing nothing, and three sessions have killed healthy builds on that ambiguity. `--progress-interval=<seconds>` (default 30, must be a positive integer or exit 1; env `SIMPLE_BOOTSTRAP_PROGRESS_INTERVAL`). |
| `--validate-bootstrap-receipt` | Validate authorization and exit 0 without starting any stage. |
| `--jobs=<n\|full\|half\|min\|auto>` | Native build workers. Default: half the CPUs locally, 2 on GitHub Actions. Rejected with anything but `1` on the two resume lanes. |
| `--output=<dir>` | Output directory for bootstrap artifacts. Default `build/bootstrap`. Artifacts land at `<output>/stage{1,2,3}/<triple>/simple`. |
| `--backend=<llvm\|llvm-lib\|cranelift>` | Backend for stage2/3/4. Default `llvm`; anything else exits 1. |
| `--bootstrap-receipt=<path>` | The canonical typed-reason planner receipt (see the receipt gate above). |
| `--full-bootstrap` | Rebuild the Rust seed/runtime when missing or stale, then rebuild the pure-Simple stages. Without it bootstrap never runs cargo. |
| `--fresh-cache` / `--no-cache` | Clear the dynload native cache once before rebuilding. |
| `--diagnostics[=off\|debug\|test]` | Opt-in compiler observability; bare `--diagnostics` selects `debug`. Both non-off modes imply `--progress`. `debug` additionally keeps LLVM IR and memory snapshots. Env `SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE`. |
| `--diagnostic-root=<path>` | File/dir selected by `--diagnostic-sweep`; repeatable. Default `src/compiler`, `src/lib`, `src/app`. |
| `--diagnostic-child-compiler=<path>` | Admitted pure-Simple worker for diagnostic child processes. Default `bin/simple`; env `SIMPLE_BOOTSTRAP_DIAGNOSTIC_CHILD_COMPILER`. |
| `--target=<triple>` | `freebsd-x86_64` (must run inside FreeBSD; Linux hosts use `scripts/check/check-freebsd-bootstrap-qemu.shs`) or `simpleos-x86_64` (host-driven guest lane, execs `src/os/port/bootstrap_cross.spl`). |
| `--keep-artifacts`, `--no-verify` | Accepted for compatibility; artifacts are always kept and hash verification always runs. |
| `--help` / `-h` | Usage. |

## Subcommands (positional, must be the FIRST argument)

`scripts/bootstrap/` was consolidated from **14 scripts to 2**
(`bootstrap-from-scratch.sh` + `bootstrap-windows.cmd`, commit `dc86db785b4`).
Thirteen former sibling scripts were folded in. If a doc, script or habit still
names one of the old `.shs`/`.sh` paths, it is stale — the file is gone.

Nine became positional subcommands. Each was verified to appear in `--help`
**and** to actually dispatch (2026-08-23; the rc/first-line column is what a
bare or minimal invocation really prints, which is how each was proved to reach
its own folded code rather than the unknown-option path):

| subcommand | former script | verified dispatch |
|---|---|---|
| `preserve-phase-binary <binary> <phase>` / `--gc <days>` | `preserve-phase-binary.shs` | rc=2 `usage: preserve-phase-binary.shs <binary> <phase>` |
| `progress-watch --pid=N --progress-log=PATH` | `bootstrap-progress-watch.shs` | rc=2 `error: --pid requires a numeric PID` |
| `planner-admission-v2 --target=... [--selftest]` | `produce-bootstrap-planner-admission-v2.shs` | rc=0 `PASS — 13 fixture(s) checked` |
| `stage2-sanity-diagnostic [--selftest]` | `check-stage2-sanity-diagnostic.shs` | rc=0 `PASS — 7 fixture(s) checked` |
| `rollback-deploy [args]` | `rollback-deploy` script | rc=2 `error: deployment is locked` |
| `stage4-tooling-matrix [args]` | `stage4-tooling-matrix.shs` | rc=2 `unknown option: --selftest` (it has no `--selftest`; `--help` does not claim one) |
| `stage4-tools-only [args]` | `stage4-tools-only.sh` | rc=1 `unknown option: --help` (no `--help` of its own) |
| `resume-stage3 <output>` | `resume-stage3-from-admitted.sh` | rc=2 `usage: resume-stage3-from-admitted.sh OUTPUT_DIR` |
| `windows-entry [--msvc\|--mingw]` | `bootstrap-windows-entry` | rc=0 `this script is Windows-only ...; nothing to do on Linux` |

Two caveats worth stating rather than leaving to be discovered:
`stage4-tooling-matrix` and `stage4-tools-only` reject `--selftest`/`--help`
respectively — the top-level `--help` documents them as `[args]` and does not
promise either flag. `resume-stage3` is also reachable as the flag
`--resume-stage3-from-admitted=<output>`, which simply `exec`s this subcommand.

### Library use — `BOOTSTRAP_LIB_ONLY=1`

The remaining folded code is exposed as pure predicate/helper functions with no
pipeline side effects:

```sh
BOOTSTRAP_LIB_ONLY=1 . scripts/bootstrap/bootstrap-from-scratch.sh
```

Verified by running it (2026-08-23): the sourced shell returns **rc=0** and
`type bootstrap_strategy_validate` reports a defined function, so the helpers are
live and no stage started. The guard sits at script line ~3860 — *after* the
subcommand `case` at ~3839, so source it with **no positional arguments**; a
stray first argument matching a subcommand name would dispatch before the guard
is reached. Without `BOOTSTRAP_LIB_ONLY=1`, sourcing the file runs the
bootstrap.

### `--identity-parent` is NOT a bootstrap flag

`--identity-parent` appears once in the script (line 3906 post-consolidation —
it was ~117 before `dc86db785b4` moved it) as an argument the
script passes to `scripts/check/lib/portable-session-exec.pl` when
`SIMPLE_BOOTSTRAP_SESSION_READY=1`, to read back `pid=`/`pgid=` and keep the
bootstrap and every non-detached descendant in one dedicated kernel process
group (lock recovery stays fail-closed while any group member lives). It is not
accepted on this script's own command line; passing it falls through to the
unknown-option path. Failure to verify the session identity exits **70**.

## How a bootstrap phase runs tests

Two mechanisms, by design — see
`scripts/check/check-stage-phase-test-capability.shs`, which pins the split.

1. **Stage 2/3 binaries are compilers only.** `src/app/cli/bootstrap_main.spl`
   exposes `compile --format=smf`, `native-build`, `--version`, `--help`, and
   nothing else. Its function names are hardcoded "known bootstrap builtins" in
   the Stage3/4 self-hosting capsule lowering, and the script's COMPANION RULE
   is explicit that the bootstrap path carries exactly what the next step
   requires. Adding a `test` subcommand there would pull the whole test-runner
   closure into the capsule and enlarge the bootstrap problem. **Do not add it.**
   A stage binary runs a spec the way it runs any program:
   `<stage>/simple native-build <spec>.spl -o <bin> && <bin>` — a `*_spec.spl`
   is a self-executing program.
2. **The `test` subcommand arrives at Stage 4 via `--full-cli`,** which compiles
   `src/app/cli/main.spl` (~60 commands via `src/app/cli/dispatch/table.spl`)
   with the provenance-verified stage3 compiler. `--deploy` and
   `--mode=one-binary` imply it.

Baseline for the gate (seed full CLI, 2026-08-23, `bin/simple test` on
`test/01_unit/std/{condition,context,spec_to_be_true_matcher}_spec.spl`):
**3 spec files requested, 3 executed, 6 examples, 0 failures.** A stage-built
full CLI must reproduce this.
