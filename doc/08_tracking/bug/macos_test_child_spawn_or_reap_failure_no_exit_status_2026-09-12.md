# macOS arm64: `simple test` child produces no exit status — spawn/reap failure at the process layer

- **Status:** OPEN (filed 2026-09-12)
- **Status:** RESOLVED 2026-09-12 (see the RESOLVED section at the end)
- **Severity:** P1 — `simple test` cannot execute ANY spec on this host
- **Lane:** macOS open-bugs round 2, LANE 3. Found while fixing
  `test_runner_reports_early_child_death_as_outer_bound_timeout_2026-09-12.md`,
  which was the MISREPORTING of this defect. That one is resolved; this is the
  underlying fault and it is untouched.
- **Host:** macOS 25.5.0, Apple M4
- **Binary:** `/Users/ormastes/simple/build/cargo-r2/release/simple`
  (`stat -f '%z %m'` = `39528776 1789199850`) — a CURRENT seed, not the stale
  Jul-25 full CLI. This is NOT the stale-deploy-slot defect.

## Reproduce (exact command, any spec — the spec is irrelevant)

```
timeout 120 /Users/ormastes/simple/build/cargo-r2/release/simple test \
  --no-session-daemon --timeout 900 \
  test/01_unit/lib/common/spec/exists_check_assertion_generalization_spec.spl
```

```
inner_rc=5
Results: 0 total, 0 passed, 0 failed
Duration: 3ms
UNVERIFIED <spec>: TERMINATED: child produced no exit status -- spawn or reap
  failure at the process layer, not a timeout and not a signal death (unverified)
```

The same spec run through `run` instead of `test` passes 4/4, so neither the
spec nor the compiler is at fault:

```
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 <seed> run <spec>
  -> 4 examples, 0 failures
```

## What is known

- **3ms, every time.** Nothing is executed; the failure is at spawn/reap, before
  any spec code runs.
- **The inner single-runner already classifies it correctly** — it says in so
  many words "not a timeout and not a signal death". The diagnosis was present
  in the tree the whole time; only the outer client
  (`test_runner_new/test_runner_client.spl`, `run_one_direct`) discarded it and
  reported `reason=outer-bound-timeout budget_ms=930000`. That laundering is
  what hid this defect, and is now fixed — hence this record exists at all.
- **Not the stale deploy slot.** `macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot_2026-08-31.md`
  describes `bin/simple` resolving to a bootstrap CLI in the stage-4 full-CLI
  slot. This reproduction bypasses `bin/simple` entirely and invokes a current
  seed by absolute path, so that record does not explain it. The two are
  related only in that both block `simple test` on this host.

## Not yet investigated

The process layer itself — `app.io.process_ops.process_run_bounded` and the
`rt_process_*` backing it on Darwin. "No exit status" points at a `waitpid`
/ `posix_spawn` path returning something the wrapper cannot map, plausibly a
macOS-specific gap in the reap loop. Nobody has read that code for this symptom
yet; this record deliberately stops at the measurement rather than guessing.

## Unblock condition

`simple test <any spec>` executes the spec's examples and reports a real
verdict, matching what `simple run <same spec>` reports.

## Impact

Every lane oracle phrased as "`simple test` and `simple run` agree" is
unreachable on macOS arm64 until this is fixed. Lane 3's oracle is in that
shape and is therefore NOT met: the disagreement is now honestly reported
rather than resolved.

## RESOLVED 2026-09-12 — it was never a process-layer fault

**Root cause: `src/app/io/cli_ops.spl:161-189` (`_cli_current_exe_path`).**
The driver REPLACES the Simple-visible argv with the SCRIPT's args before any
`.spl` runs (`rt_set_args`, `src/compiler_rust/runtime/src/value/args.rs`), so
`sys_get_args()[0]` is the `.spl` SOURCE FILE, not the executable. On Linux the
function returns from `/proc/self/exe` and never reaches the argv0 fallback.
macOS has no `/proc`, so it fell through to that fallback and returned the
`.spl` path. `_cli_source_entry_executable` (`cli_ops.spl:142`) rescues exactly
this case — but only when `SIMPLE_BINARY` is already set, which it is not on a
plain invocation.

`find_simple_binary()` (`src/app/test_runner_new/test_runner_single.spl:276`)
therefore handed a **source file** to `process_run_bounded`, which tried to
spawn it. The spawn failed, and the facade's `-1` was reported as "child
produced no exit status — spawn or reap failure at the process layer".

Evidence that pinned it, already present in the failing output and overlooked:
`child binary: .../src/app/test_runner_new/test_runner_single.spl`
(printed by `test_runner_single.spl:1072`). And
`SIMPLE_BINARY=<seed> <seed> test --no-session-daemon <spec>` passed 1/1 at the
time `<seed> test <spec>` was dying in 3 ms.

- `runtime_need`: none. The process externs and `process_run_bounded` are
  correct — verified by spec: a child that `exit 7` is reported as 7.
- `facade_checked`: `app.io.cli_ops`, `app.io.process_ops`,
  `src/compiler_rust/runtime/src/value/args.rs` (`rt_set_args`/`rt_get_args`),
  `value/cli_sffi.rs` (`rt_cli_arg_at` routes to the SAME replaced table, so it
  is not an alternative source of the real argv).
- `chosen_path`: pure Simple. `_cli_current_exe_path` now refuses to return a
  `.spl` and asks the kernel about its OWN pid (`ps -o comm= -p <getpid()>`,
  verified on this host to report the absolute exec path), resolving and
  canonicalizing the result through the existing helpers. Linux is untouched:
  the `/proc/self/exe` branch still returns first.
- `rejected_shortcuts`: (a) rebuilding the Rust seed to add an
  `rt_current_exe_path` extern — the defect is provably not in the seed;
  (b) exporting `SIMPLE_BINARY` from the spawn site — that only patches the
  runner, leaving every other `cli_current_exe_path()` caller broken on macOS;
  (c) `readlink -f /proc/self/exe` shell-out — no `/proc` here, and the
  helper-describes-itself trap the surrounding comments warn about.

Also fixed, newly visible once specs could run at all:
`unrun_verdict_line` (`src/app/test_daemon/light_protocol.spl:128`) emitted no
`outcome=` field, so a spec that executed NOTHING printed a verdict line no
outcome-reading sweep could classify. It now carries `outcome=ERROR` in the
driver's own field position.

Fail-closed guard added at `test_runner_single.spl:276` — a `.spl` candidate is
now rejected by name with a remedy, so this can never again present as a
process-layer fault.

### Evidence (seed `/Users/ormastes/simple/build/cargo-r2/release/simple`, 39528776/1789199850)

| command (no flags, default daemon path) | before | after |
|---|---|---|
| `test <green spec>` | `Results: 0 total, 0 passed, 0 failed`, `reason=child-died-early exit_code=-1 elapsed_ms=3`, exit 5 | `Results: 1 total, 1 passed, 0 failed`, exit 0 |
| `test <deliberate-red spec>` | same 3 ms death | `Results: 1 total, 0 passed, 1 failed`, exit 1 |
| `check-test-runner-executes-bodies.shs` | `FAIL — 3 probe(s) executed, 3 failed` | `PASS — 3 probe(s) executed, runner executes it bodies and discriminates` |

Specs: `test/01_unit/app/test_runner_new/child_spawn_binary_identity_spec.spl`
(reproducer — example 1 runs inside `simple test`, the exact failing condition;
examples 2-3 pin the spawn facade so a real spawn/reap defect stays
distinguishable from this identity defect). Sabotage proof: reverting
`cli_ops.spl` alone turns example 1 red (`✗ is never a .spl source file`,
`1 example, 1 failure`) and restores green.

`test_runner_reports_early_child_death_as_outer_bound_timeout_2026-09-12.md`
(the misreporting layer) had already landed; that fix is what made this
diagnosable at all.

### Pre-push gate record (scoped-delta step-over, 2026-09-12)

`check-test-tree-divergence-delta.shs 8ae99f5e7a0..5aa13beb7db`:
`PASS — 3209 pre-existing offender(s), 0 introduced by this range` (exit 0).
Base verdict is RED and pre-existing: `FAIL — 3943 diverged vs 965 baselined
(3081 new, 103 fixed-but-still-baselined); 26 mirror-only (25 unallowlisted)`.
Offender list saved by the helper to
`$TMPDIR/test_tree_divergence_preexisting.txt`. This range adds one spec under
`test/01_unit/app/test_runner_new/` with no twin on the mirror side and changes
no existing pair.

Other guards on this range: conflict-markers PASS (6 files, exit 0); tree-size
PASS (1 commit, base 136276 files, exit 0). Pre-existing RED, not introduced
here and not touched by this diff: `check-rt-dual-implementation-ratchet.shs`
FAIL (4 new / 1 stale — `rt_file_atomic_write_mode`, `rt_file_list_dir`,
`rt_file_mode`, `rt_fs_read_text`, stale `rt_transient_raw_words`; this commit
adds no `rt_*` symbol) and `check-guard-wiring.shs` FAIL (1 new unwired,
`check-t32-mcp-server-runnable.shs`; this commit adds no guard script).
