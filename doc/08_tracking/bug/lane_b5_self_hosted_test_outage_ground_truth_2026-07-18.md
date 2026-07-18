# Lane B5: self-hosted-compiler-tree "test outage" ground truth

**Date:** 2026-07-18
**Status:** GROUND TRUTH ESTABLISHED — compound finding, distinct from B4's daemon-hang
**Worktree:** `/home/ormastes/dev/wt_b5`, detached at `7c06a8969f6` (origin/main tip)

## Task

Lane N8 reported "both locally-available binaries fail to run ANY `.spl` test
at all." Determine whether this is the same as B4's daemon-hang, and whether
it is a stale-seed artifact (fixed by redeploy) or a current-source
regression.

## Binary inventory

| Binary | Size | Mtime | SHA256 (16-char prefix) | `--version` |
|---|---|---|---|---|
| `pub/simple/bin/release/x86_64-unknown-linux-gnu/simple` (main-repo deployed) | 31,277,168 | 2026-07-18 14:35:42 | `8d8f59c24cb716da` | Rust seed v1.0.0-beta |
| `pub/simple/src/compiler_rust/target/release/simple` | 56,075,784 | 2026-07-17 11:57:46 | `2fbe1d68fdb83809` | Rust seed v1.0.0-beta |
| `pub/simple/src/compiler_rust/target/bootstrap/simple` | 27,892,528 | 2026-07-18 14:43:06 | `e7d87501f3e1d8e9` | Rust seed v1.0.0-beta |
| `/home/ormastes/dev/seed_fresh_20260718/simple` (the doc's "known-good fresh seed") | 56,182,176 | 2026-07-18 08:05:54 | `5e383ccd6767c84c` | Rust seed v1.0.0-beta |

All four are **Rust-seed** binaries (`WARNING: this Rust-built Simple binary
is a bootstrap seed only`), not the pure-Simple self-hosted binary. Note the
main-repo deployed binary's fingerprint no longer matches the "stale Jul-11
seed" (46,170,032 bytes, `561767c6...`) documented in
`deployed_seed_test_runner_init_hang_2026-07-17.md` — some other session
redeployed a newer Rust seed there since that doc was written. The literal
stale-Jul-11 artifact is gone from this box; it could not be independently
re-tested.

## Behavior on a trivial one-assert spec

Probe file added: `test/01_unit/lane_b5_trivial_spec.spl` (`describe`/`it`,
single `assert_true(true)`, zero `use` statements).

### `<binary> run <file>` (direct, bypasses the test-runner/daemon entirely)

Instant (0.02–0.04s), clean, correct on every binary tried:
```
LaneB5Trivial
  ✓ asserts true

1 example, 0 failures
```
**`run` is not broken on any tested binary.**

### `<binary> test <file>` invoked directly by absolute path (no `bin/simple`)

All four binaries: 30–60s wall time, ~150K–290K lines of unrelated
"Common mistake detected" (explicit-`self.`) / deprecated-syntax diagnostics
against files across `src/compiler/**` (not the target spec), then either:
- `error: test-runner: no examples executed` (rc=1) — 3 of 4 binaries, or
- `error: semantic: unknown extern function: rt_process_run_bounded` (rc=1)
  — the Jul-17 `target/release` build (predates that extern's registration).

**None of the four hung** — every run finished well inside a 90s timeout, so
this is not literally the same failure mode as B4's daemon-hang (an actual
indefinite spin). Under a tighter caller timeout (e.g. 30–45s, plausible for
an automated harness under this box's typical multi-agent CPU contention),
this would look exactly like rc=124.

### Root-cause split of the "no examples executed" misfire

A fresh `git worktree add` checkout has **no `bin/release/<triple>/simple`**
(gitignored build artifact) and therefore no `bin/simple` symlink —
`scripts/setup/setup.shs` correctly refuses to create one
(`setup: .../simple not found — run bootstrap first`). Invoking a seed binary
directly by absolute path for the `test` subcommand causes
`find_simple_binary()` (`src/app/test_runner_new/test_runner_single.spl:159`)
to fall through its `raw[0]`-based fast path and resolve the **child**
executor binary to a nonexistent `./bin/simple`; the per-file subprocess spawn
then silently fails (empty stdout/stderr), and the fail-closed
"no examples executed" check (correctly, by design) reports that as a FAIL —
even though the target spec is a real, genuine pass. This is a **worktree
provisioning gap in this ground-truth methodology, not a source bug** in the
pass/fail accounting itself.

**Confirmed by direct experiment:** after manually symlinking
`bin/release/x86_64-unknown-linux-gnu/simple` → the known-good fresh seed and
running `scripts/setup/setup.shs` to create `bin/simple` (both purely local to
this worktree; nothing pushed/deployed), re-running through the canonical
`bin/simple test <file>` entrypoint:

- `bin/simple test test/01_unit/lane_b5_trivial_spec.spl` → rc=0,
  `Passed: 1, Failed: 0, PASS` (correct!).
- `bin/simple test test/01_unit/app/io/io_numeric_guard_spec.spl` → rc=0,
  `Passed: 2, Failed: 0, PASS` (correct — matches the 2026-07-18 07:39 S88
  evidence-lane claim of "2 tests PASSED" for the same spec+binary).

So **the pass/fail accounting logic is not broken**. Once invoked the
canonical, documented way (`bin/simple test <file>`, with `bin/simple`
actually provisioned), every tested binary correctly reports the real result.

### The regression that survives correct provisioning

Even through the working `bin/simple` path, both specs above still took
23–25s and emitted **291,199 / 291,200 total lines** of the same
"Common mistake detected"/deprecated-syntax spam scanning what looks like the
whole `src/compiler/**` tree, wrapped around the real result (which sits at
~line 166,680 of ~291,200 — the same "wave 1 / real result / wave 2" shape
already described in
[[test_runner_fresh_seed_silent_noop_2026-07-17]]). This reproduces
**identically across all four binary vintages** (Jul-17 through Jul-18,
including same-day fresh builds), so **it is not fixed by redeploying or
rebuilding the seed** — it is rooted in shared `.spl` source.

Diffing `356a3c058dc..HEAD` (the doc-evidence baseline vs. current tip,
72 commits) shows `src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl`
gained calls into a new `extract_doctests`/`count_sdoctest_blocks_for_path`
path, matching the intentional doctest-discovery-scope widening described in
[[whole_test_runner_doctest_import_comment_guard_2026-07-18]] (~100 →
~1,059 source doctest candidates, ~136K Markdown fence candidates). That doc
already flags the resulting blast radius as unverified at runtime; this lane
supplies the missing runtime confirmation: ~290K lines / ~24-60s per single
test-file invocation, load-bearing but not yet root-caused (per the 07-17
doc's own "not enough budget... flagging as open follow-up" — not re-chased
here, per the same guidance).

## Verdict

**Compound, not single-cause:**

1. **Genuine current-source regression (confirmed):** `simple test <file>`
   on ALL current-source binaries (any vintage, including today's freshest
   builds) pays a ~24-60s / ~290K-line tax from whole-tree doctest-candidate
   scanning before/around the real result. A seed redeploy does **not** fix
   this — it is `.spl`-side and already tracked (open, not yet root-caused)
   in [[test_runner_fresh_seed_silent_noop_2026-07-17]] and
   [[whole_test_runner_doctest_import_comment_guard_2026-07-18]]. Per
   "verify already fixed first" and prior explicit guidance not to re-chase
   this, no new bug filed for it — this doc adds fresh quantitative
   confirmation and cross-references.
2. **Not a hang / not B4:** every run completed well inside 90s; this is
   noise-and-slowness, not the indefinite spin B4 investigates. They may
   compound (a caller with a tight timeout would see both as "outage"), but
   the mechanisms are distinct.
3. **Investigation-methodology trap (not a shipped bug):** a fresh
   `git worktree add` has no `bin/simple`; invoking a seed binary directly
   causes the per-file child-spawn to silently fail and every test to
   misreport as "no examples executed"/FAIL regardless of real content. Any
   lane (N8 included) working in a fresh worktree without provisioning
   `bin/simple` (symlink to any already-built runtime) will see "cannot run
   ANY test" that is fully explained by this, not by a deeper regression.
   Once provisioned, pass/fail accounting is correct.

## Cross-refs

- [[deployed_seed_test_runner_init_hang_2026-07-17]] — the stale-Jul-11-seed
  report this lane was asked to reconcile against; that exact binary
  fingerprint is no longer present at the deployed path.
- [[test_runner_fresh_seed_silent_noop_2026-07-17]] — prior discovery of the
  wave1/result/wave2 shape and the (separate, since-fixed) directory-mode
  `index_of` hang.
- [[whole_test_runner_doctest_import_comment_guard_2026-07-18]] — the
  intentional doctest-scope widening implicated as the current-source cause
  of the noise/slowness.

## Files added

- `test/01_unit/lane_b5_trivial_spec.spl` — permanent minimal one-assert
  smoke fixture (zero `use` statements) for future ground-truth probes.
- This doc.

No `.spl` regression test was added for the noise/slowness regression itself:
it is already tracked and explicitly deferred (not root-caused) by two prior
docs, and per this session's guidance it was not re-chased. The
misaccounting symptom this lane initially suspected was a source bug turned
out, on localization, to be a worktree-provisioning artifact of direct binary
invocation — not a green-able source-logic bug, so no test was added for it
either; the fix is procedural (provision `bin/simple` before testing in a
fresh worktree), and is documented above for future investigators.
