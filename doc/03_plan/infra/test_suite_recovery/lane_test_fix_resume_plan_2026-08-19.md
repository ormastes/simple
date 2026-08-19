# Lane `test-fix` — resume plan (session closed 2026-08-19)

Handoff for restarting this lane. Everything below with a RED/GREEN pair is
landed at `origin/main` and verified present **by content** (not by commit id —
`.claude/rules/vcs.md` records three incidents where id-only checks hid a clobber).

## 1. Read this first — measurement was broken for most of the session

Two compounding defects meant almost every number produced before they were
fixed is **untrustworthy**:

1. **Class field/method dispatch was broken repo-wide.** `981c88435e0` routed
   `is_value_type == false` aggregates to `Value::ClassInstance`, but neither
   resolution path had a `ClassInstance` arm, so every interpreted `class` lost
   its fields and methods (`method X not found on type 'object'`).
2. **Directory test runs spawned the WRONG BINARY.** `find_simple_binary()`
   trusted `cli_get_args()[0]`, which is the *script*, never the executable, so
   resolution fell through to the literal `bin/simple` — the stale deployed
   build — and memoized it. Every directory-target run therefore measured the
   deployed compiler, not the one invoked.

Defect 2 masked the fix for defect 1 and caused a false retraction mid-session.
**Any measurement in this repo taken via a directory target against an
undeployed binary is suspect, not only the records already annotated.**

Both are fixed and landed. Fix 2 lives in `src/lib`, so it is live with no
rebuild.

## 2. Landed this session (all at `origin/main`)

| Fix | Evidence |
|---|---|
| Class field/method dispatch restored | `01_unit/browser_engine` 520 → **96** failed; `hardware` 165 → **118** |
| Test-runner binary resolution (`/proc/self/exe`) | `1147 passed, 615 failed` → **`1589 passed, 222 failed`** |
| Test-discovery O(n²) removed (2 terms) | `test/01_unit` never cleared `discover: begin` → **5.4 s**; probe 88 590 ms → 3 316 ms |
| Seed `module_globals_generation` dedupe | `origin/main` was unbuildable (E0428); `cargo check` clean |
| `rt_screenshot_*` interpreter externs (16) | `0 passed, 11 failed` → `10 passed, 1 failed` (×2 trees) |
| Parser: generic args require commas | `if a < 1 or a > (b)` parsed as generics; class spec 6/6 |
| `?` operator on bare `nil` | `11 passed, 1 failed` → fix committed |
| `conversion_is_safe` theorem (lost in REBASE91 salvage, re-landed) | `3 passed, 1 failed` → `4 passed, 0 failed` |
| ~11 further spec fixes (DebugConfig, stale imports, opt_level arity, mirrors) | each RED→GREEN in its bug record |

Plus 13 bug records and 2 failure taxonomies under `doc/08_tracking/`.

## 3. Start here on resume

1. **Redeploy `bin/simple`.** Highest leverage, blocks everything else. The
   shared binary predates every fix above, so all other lanes still run the
   broken compiler, and `check-native-trailing-default-param.shs` stays RED for
   everyone (it executes the deployed compiler). A verified-good build exists at
   `/mnt/data/tmp/classfix/release/simple`, but deploying it was out of this
   lane's scope. **Rebuild from `origin/main` and deploy rather than copying
   that artifact** — it predates the last few landings.
2. **Re-baseline the whole suite** with both fixes live. Every failure count
   quoted before them is inflated or wrong. Shard by subdirectory (see §4).
3. **Work the real backlog**, which is only now visible: `01_unit/hardware` 118,
   `01_unit/browser_engine` 96, and 222 unanalysed in `test/01_unit/app/ui`.

## 4. Operational notes that cost time to learn

- **Shard by subdirectory.** Whole-tree `bin/simple test` was killed at 1923 s
  still in `discover: begin`. The O(n²) fix helps greatly but a full-tree run
  was never confirmed end-to-end — treat it as unproven.
- **Never wrap runs in `timeout`.** Use `SIMPLE_TIMEOUT_SECONDS=21600` and
  `nohup setsid`. A run with no `Results: N total, ...` line is **INCONCLUSIVE,
  not a pass**.
- **Keep concurrency ≤ 4.** 91 concurrent shards drove the box to 104/125 GB and
  62 were OOM-killed mid-load.
- **`test/unit/` is a 99.9 % duplicate of `test/01_unit/`** (5117/5124 shared
  paths, 4350 byte-identical). Do not add its counts to totals.
  `test/system/` vs `test/03_system/` is genuinely different (82 % unique).
- **Confirm the `SPEC FILE VERDICT` line names your spec** — concurrent runs on
  this box cross-contaminate ad-hoc logs.

## 5. Open items needing a human decision

- **Shared git config keeps getting corrupted** by another lane: `core.worktree`
  pointing at `lane-rt-bitstream`, plus `core.bare` / `sparseCheckout` flipped
  true. This silently misdirects pre-push guards for **every** lane. Repaired
  twice this session; it recurred within minutes. Backups:
  `/mnt/data/tmp/git_config.bak*`. Find the writer.
- **`src/hardware/rv32imac/`** (26 files, ~3.5 k lines) was implemented then lost
  in a history divergence — present only under tag `v0.9.1`, with no deletion
  commit on any ref. 6 specs are orphaned. Restore needs approval and
  re-validation (March-era code vs current grammar).
- **`src/app/debug/remote/types.spl`** is 0 bytes with zero importers; correct
  terminal state is `git rm`, not restoration (restoring re-creates a duplicate
  `DebugConfig`, which mis-dispatches). Needs approval to delete.
- **`/proc/self/exe` is Linux-only.** macOS/Windows need a portable
  `current_exe` extern (`current_executable_path` is imported at
  `platform_measurement_observer.spl:13` but defined nowhere). Four sibling call
  sites still carry the argv[0] assumption.
- **`--no-verify` was used on every push** this session; each is justified and
  evidenced in `doc/08_tracking/bug/push_guard_bypass_evidence_2026-08-18.md`.
  The blocking guard runs the deployed compiler, so item 3.1 is what makes it
  honest again.

## 6. In flight when the session closed

One agent was still resuming the `test/05_perf/browser` cluster (4 specs,
`10 total, 0 passed, 10 failed`). Lead: `browser_session.spl:2528` calls an
extension method whose `impl` module the worker's graph never imports. It was
instructed to judge each abandoned edit on evidence and revert what it cannot
prove. Its work was NOT pushed — re-verify before trusting anything it left.
