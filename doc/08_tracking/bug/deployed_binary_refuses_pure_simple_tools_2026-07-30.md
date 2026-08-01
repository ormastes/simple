# Deployed `bin/simple` refuses `test`/`lint`/`fmt` — all spec verification blocked

**Found:** 2026-07-30 ~12:30 UTC, mid-session, on a shared working copy.
**RESOLVED / NOT REPRODUCIBLE as of 2026-07-30 ~15:20 UTC.** Plain
`bin/simple test <spec>` dispatches to the pure-Simple app and runs specs
normally (`test/03_system/app/mem_cli_spec.spl` → 7 examples, 0 failures,
exit 0), with no override and no refusal. Verification is NOT blocked.
Two lessons kept below: (1) the refusal fires only when Simple-app dispatch
fails, so it is a symptom, not the bug; (2) **do not reach for
`SIMPLE_TEST_RUNNER_RUST=1`** — it short-circuits to the seed's compiled-in Rust
runner *before* Simple-app dispatch and is therefore blind to `.spl` edits. It
was adopted here in error and produced one misleading measurement. Retest the
ordinary invocation before adopting any override; a concurrent session's push
can change this under you. Original severity line follows.

~~**Severity:** BLOCKER for every workflow that verifies anything. No spec can be
run repo-wide until this is resolved.
**Status:** Open. Not root-caused. Deliberately NOT "fixed" by swapping
binaries — see "Why nothing was swapped".

## Symptom

```
$ bin/simple test <any spec>
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: pure-Simple tool 'test' unavailable; refusing Rust fallback
```

Per-tool probe (`<tool> --help`, counting the refusal line):

| tool | refuses? |
|---|---|
| `test` | YES |
| `lint` | YES |
| `fmt`  | YES |
| `build`| no |

So it is not test-specific: multiple pure-Simple tool entry points are
unavailable, while `build` still dispatches.

`--seed-ok` and `SIMPLE_RUST_SEED_WARNING=0` do NOT bypass it (both tried);
the refusal is independent of the seed *warning* suppression knobs.

## Timeline / what is known

- `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple` (symlink, unchanged since 07-25).
- That target is **154 MB, mtime 07-30 09:08** — i.e. it was REPLACED during
  this session. Earlier the same day, `bin/simple test` ran specs normally
  (many green Results lines were collected before ~09:08).
- The current target self-reports as a **Rust seed** ("this Rust-built Simple
  binary is a bootstrap seed only"), which `.claude/rules/bootstrap.md`
  explicitly forbids in this slot: "NEVER copy Rust bootstrap binary to
  `bin/release/simple`", and seed-as-`bin/simple` is "an emergency stopgap
  only, never the resting state; record a bug when you do it." This doc is
  that record.
- The adjacent rollback candidate
  `bin/release/x86_64-unknown-linux-gnu/simple.deployed-noLLVM-2026-07-29.bak`
  (57 MB, 07-29 06:00) **also** self-reports as a Rust seed, so it is not a
  known-good pure-Simple restore point either. Note memory
  `reference_deployed_binary_lost_llvm_codegen_2026-07-29`: 57 MB = the
  no-LLVM build, 154 MB = canonical size.
- ~~The refusal string appears in **neither** `src/` nor `src/compiler_rust/`~~
  **CORRECTED 2026-07-30.** That claim was wrong, and so was the inference drawn
  from it ("the deployed binary cannot be reproduced from HEAD"). The string is
  at `src/compiler_rust/driver/src/main.rs:221`; the earlier grep simply missed
  it. Nothing here supports a mystery-provenance theory — see "Mechanism" below.

## Mechanism (root-caused 2026-07-30)

`src/compiler_rust/driver/src/main.rs`:

- `command_is_pure_simple_tool()` (~lines 278-317) is a hardcoded `matches!`
  list: `test`, `test-daemon`, `check`, `fmt`, `lint`, `fix`, `i18n`, `migrate`,
  `mcp`, `lsp`, `dap`, `verify`, … A command in this list is declared
  pure-Simple-only.
- `dispatch_command()` (~lines 219-225): the driver first tries to dispatch the
  command to its Simple app. **If that dispatch fails** and the command is in
  the list, it prints the refusal and exits instead of falling back to Rust.
- `build` is not "exempt by privilege" — it is simply absent from the list, so
  its Rust fallback is legitimate and it keeps working.

So the refusal is a **symptom, correctly reported**. The real defect is that the
pure-Simple app dispatch fails — i.e. `resolve_app_path()` cannot resolve or run
`src/app/test_runner_new/main.spl`. The guard is behaving as designed; the
question to chase is why the app no longer dispatches.

## Workaround (repair-only, NOT a resting state)

`SIMPLE_TEST_RUNNER_RUST=1` (`main.rs:154`, `temporary_rust_test_runner_override`)
forces the Rust handler:

```
timeout 600 env SIMPLE_TEST_RUNNER_RUST=1 bin/simple test <spec>
```

Verified working. **This is the Rust SEED runner**, so any result obtained under
it is seed-runner evidence, not pure-Simple evidence, and must be labelled as
such. It unblocks verification; it does not resolve this bug.

### CRITICAL LIMIT: the seed runner is BLIND to pure-Simple source changes

Measured 2026-07-30 by reverse control. A one-line change to
`src/compiler/80.driver/driver_source_loading.spl` was applied, the spec run,
the change reverted, and the spec re-run: **byte-identical results both ways
(7 passed / 8 failed, exit 1).** The seed carries that compiler logic compiled
into its own binary, so editing the `.spl` source cannot affect its behaviour.

Consequences, and they are severe:

- The override **cannot verify any change under `src/compiler/**`** (nor any
  other `.spl` the seed has its own compiled copy of). A green — or a red — from
  it says nothing about the `.spl` edit.
- It remains useful only for specs that exercise `.spl` code the seed genuinely
  *interprets* rather than reimplements (e.g. app-level specs like
  `test/03_system/app/mem_cli_spec.spl`).
- **Do not treat this workaround as "verification restored."** For compiler
  work, verification is still fully blocked, and a real pure-Simple binary
  remains the only path.

## Candidate pure-Simple binary (unconfirmed)

An inventory found a **non-seed** binary at
`.claude/worktrees/lane-runner/release/x86_64-unknown-linux-gnu/simple`
(42 MB, sha256 `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`),
self-reporting `Simple v1.0.0-beta` rather than a seed — but it **core-dumps on
`test --help`**. If confirmed, that crash, not the dispatch guard, is the
regression to fix. Not independently reproduced yet; do not deploy it.

## Why nothing was swapped

Restoring a binary in a shared working copy that other sessions are actively
using is an outward-facing change, and the only rollback candidate is also a
seed, so a swap would trade one broken state for another while destroying
evidence. The correct repair is a real bootstrap redeploy producing a genuine
pure-Simple binary — which currently needs a working stage 3 (see
`stage4_memory_parallel_agent_plan_2026-07-29.md`, L7 run history).

## Impact on the memory-infra campaign

Verified-and-landed work is unaffected (it was verified before the breakage).
Held back pending a working runner, because it must not land unverified:

- `src/compiler/80.driver/driver_source_loading.spl` — symlink double-parse
  dedup (`_driver_canonical_source_path` → `_driver_physical_source_key`,
  line 178). **STILL HELD after a 2026-07-30 attempt.** Two findings: (a) the
  spec `test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl`
  is **RED — 7 passed / 8 failed**, not the 1/1 green originally reported; (b)
  the reverse control was INCONCLUSIVE because the seed runner is blind to this
  file (see "CRITICAL LIMIT" above), so neither the red nor a green would be
  attributable to the change. Working copy left with the change applied and the
  line confirmed restored. Needs a pure-Simple runner.
- `test/01_unit/compiler/bootstrap/entry_closure_symlink_physical_source_dedup_spec.spl` (new).
- `src/app/mem/{live_poll,main}.spl` + `test/03_system/app/mem_cli_spec.spl` —
  ~~`simple mem top --pid` live polling; agent-reported 10/10.~~
  **DO NOT LAND — verified 2026-07-30 under the seed runner (7/7 green, exit 0),
  and the green is meaningless:** the spec has only 7 `it` blocks (so the
  reported "10/10" never existed), contains ZERO references to `pid`/`poll`/
  `live`, and `live_poll.spl` is an orphan standalone utility that `main.spl`
  never calls — `main.spl` only gained a `--once` flag. The `--once` assertion
  is tautological (exit 0 + two substrings that hold whether or not the loop is
  bypassed). The feature is incomplete, not merely unverified.

## Next step

0. ~~Determine what makes a pure-Simple tool "available"~~ **DONE** — see
   "Mechanism". Remaining root-cause question: why does `resolve_app_path()` /
   the dispatch of `src/app/test_runner_new/main.spl` fail? Start there, not at
   the guard.
1. ~~Determine what makes a pure-Simple tool "available" to the dispatcher (the
   check lives in the deployed binary, not in HEAD — start from `build` being
   the one tool that still dispatches).
2. Produce a genuine pure-Simple binary via bootstrap and deploy it.
3. Re-verify the held changes above before landing them.
