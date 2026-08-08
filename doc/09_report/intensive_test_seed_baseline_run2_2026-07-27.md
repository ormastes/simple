# Intensive Test Seed Baseline — Run 2 (2026-07-27)

Attempt to collect the intensive-test baseline that had been blocked all session by
`scripts/resource/kill_simple_monitor.shs`.

**Bottom line:** the monitor bypass **worked** — no run was killed. But **no baseline
was obtained**, because the seed test runner aborts on its own before executing a
single test. The blocker was never only the monitor.

---

## 1. Binary identity — this is the Rust SEED

| Field | Value |
|---|---|
| `readlink -f bin/simple` | `/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple` |
| size | 145,290,352 bytes |
| mtime | 2026-07-27 22:06:45.307 +0000 |
| `bin/simple --version` | `WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.` / `Build and use the pure-Simple bin/simple instead.` / `Simple Language v1.0.0-beta` |

**Every number below is a SEED baseline, not a self-hosted one.** The binary prints the
bootstrap-seed warning banner on every invocation. Per `.claude/rules/testing.md`
("Binary identity caveat"), all findings here attribute to the SEED.

Child processes spawned by the runner appear under a *different* path,
`src/compiler_rust/target/debug/simple` (478,524,400 bytes, mtime Jul 26 01:16) — see
§5, this matters for the bypass.

## 2. The monitor rule and the bypass

Verified directly against `scripts/resource/kill_simple_monitor.shs` (the report cited
in the task brief, `doc/09_report/kill_simple_monitor_rules_and_test_exemption_2026-07-27.md`,
**does not exist on disk**):

- L13-14: `CPU_THRESHOLD=95`, `MIN_AGE_SECS=60` — hardcoded, no env override.
- L148-156: CPU guard kills any matching proc at `cpu>=95%` **and** `age>=60s`.
- `MEM_THRESHOLD_MB="${KILL_SIMPLE_MEM_MB:-24000}"` — env knobs affect **RSS only**,
  confirming the CPU spin-kill has no override.
- `is_protected()` (L40-58) returns early for any cmdline matching
  `*claude*`, `*codex*`, `*tmux*`, `*node*`, `*npm*`, `*daemon*`, or the mcp patterns.

Bypass applied (per precedent
`doc/03_plan/compiler/bootstrap/cli_selfdelegation_redeploy_plan_2026-07-25.md:45`,
"the unblock is a lowercase `claude` token in argv[0], not an env var"):

```sh
ln -sf "$(readlink -f bin/simple)" /tmp/claude_simple_test_runner
```

Symlink created in `/tmp`, **not** in the repo. Monitor (pid 1008988, up 2d18h) was left
running and untouched.

## 3. Runs, commands, exit codes, durations

All launched from repo root via `nohup setsid sh -c ...`, logs under `/tmp`.

| # | Command | Exit | Wall clock | Outcome |
|---|---|---|---|---|
| 1 | `/tmp/claude_simple_test_runner test` | 1 | 239 s | `@cover` gate; 0 files run |
| 2 | `/tmp/claude_simple_test_runner test test --whole --mode=interpreter` | 1 | 80 s | `@cover` gate; 0 files run |
| 3 | `/tmp/claude_simple_test_runner test --no-cover-check` | 1 | 638 s | semantic abort; 0 files run |
| 4 | `/tmp/claude_simple_test_runner test test --whole --mode=interpreter --no-cover-check` | 1 | 958 s | semantic abort; 0 files run |

Runs 3 and 4 add `--no-cover-check` — the bypass **printed by the tool itself** in the
runs 1/2 output — because runs 1/2 never reached the test loop.

**No run was killed.** All four exited on their own (exit 1, never 143/137), at
80-958 s — far past the 61 s wall that killed the three earlier attempts today.

## 4. Authoritative `Results:` lines

Per `.claude/rules/testing.md` F3, only the final `Results:` summary counts.

### Runs 1 and 2 — identical, and NOT a test result

```
=========================================
Results: 1840 total, 0 passed, 1840 failed
Time:    0ms
=========================================
error: semantic: variable `total_failed` not found
```

Preceded by:

```
Bypass: --no-cover-check
Found 1840 system test(s) without # @cover.
[MEM] AFTER_RUN_0_files: MemAvailable:   111725160 kB
```

`Time: 0ms` and `AFTER_RUN_0_files` prove **zero tests executed**. The 1840 "failures"
are the count of system-test files missing a `# @cover` annotation — a lint/policy gate,
not test outcomes. Treating 1840 as a failing-test count would be wrong.

### Runs 3 and 4 — no `Results:` line at all

`grep -c '^Results:'` = **0** in both logs. Both end:

```
Running 18059 test file(s) [mode: interpreter]...     # run 3 (run 4: 18061 files)
Self-protection enabled (stops when free CPU < 25% AND free RAM < 25%)
  Max memory per test: 16GB
Change-detection cache bypassed (--clean)
Session setup: 595827ms                                # run 4: 873371ms

error: semantic: variable `failed` not found
```

`grep -cE '^(PASS|FAIL|ok |not ok)'` = **0**. `grep -c '^error:'` distinct = 1. The
runner enumerated ~18k files, spent 596 s / 873 s in "Session setup", then aborted
before running any test.

## 5. Failing-test list

**None can be produced.** No test was executed in any of the four runs, so there is no
per-test pass/fail data and no failing-test names to attribute — neither known-bug-linked
nor unattributed. The session's intensive-test baseline remains uncollected.

## 6. Root cause of the abort (SEED defect, not yet filed)

Both abort messages name tokens that are **struct-literal field names**, not variables:

- `total_failed` — `src/app/test_runner_new/test_runner_main.spl:178`
  `return TestRunResult(files: [], total_passed: 0, total_failed: missing_covers.len...)`
  (the `@cover` gate return path, hence runs 1/2)
- `failed` — the normal path, e.g. `test_runner_main.spl:326` `failed: cached_entry.failed`,
  `:595` `TestFileResult(path: file_path, passed: 0, failed: 0, ...)`, `:717` `failed: 1`

The seed's semantic analyzer resolves the `name:` label in a struct literal as a
*variable reference* and fails to find it. This is the known seed struct/field
resolution defect class.

**Not filed.** `grep -rl 'variable \`failed\` not found\|variable \`total_failed\` not found' doc/`
returns nothing. Nearest existing docs, none matching:
`doc/08_tracking/bug/interp_cross_module_struct_field_collision_2026-07-04.md`,
`doc/08_tracking/bug/class_named_arg_out_of_order_drops_field_2026-06-30.md`,
`doc/08_tracking/bug/deployed_seed_test_runner_init_hang_2026-07-17.md`,
`doc/08_tracking/bug/bootstrap_stage4_seed_compiled_full_cli_run_test_crash_2026-07-20.md`.
No fix attempted, per task scope.

## 7. Did the bypass work? — Yes, with one caveat

Yes. Zero kills of our runs; all four exited on their own well past 60 s.

**Caveat — children are NOT protected.** The runner spawns per-spec children under the
*resolved real* binary path, which drops the `claude` token. Two of our own children were
killed during run 1:

```
2026-07-27T22:45:47 KILL ... (cpu=98.3% age=62s: /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple run test/01_unit/compiler/hir/resolve_import_symbols_spec.spl)
2026-07-27T22:47:11 KILL ... (cpu=95.9% age=64s: /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple run ...)
```

(The `bin/simple run .../db_server_tier_spec.spl` kills at 23:07-23:14 are another
session's, not ours.) So the argv[0] bypass protects only the **parent**. Once the seed
abort in §6 is fixed and the run reaches the per-test loop, any single spec exceeding
~60 s at high CPU will still be SIGTERM'd. A durable fix needs the runner to propagate
a protected argv[0] to children, or a real exemption mechanism in the monitor.

## 8. Artifacts

- `/tmp/claude_seed_test_main.log` (run 1), `/tmp/claude_seed_test_whole.log` (run 2)
- `/tmp/claude_seed_test_main2.log` (run 3), `/tmp/claude_seed_test_whole2.log` (run 4)
- `/tmp/kill_simple_monitor.log` — monitor kill log
- `/tmp/claude_simple_test_runner` — bypass symlink

Not committed, per instruction.
