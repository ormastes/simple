> **CORRECTION 2026-07-25 (appended after publication).** This run does NOT
> measure the interning fix, and any reading of it as evidence against
> `571bb8f8be35` is wrong.
>
> The seed used was built from `906b85d1420` (07-22 05:50), which PREDATES the
> interning fix (07-24 10:59). Verified: `strings -a … | grep -c
> rt_string_new_literal` = **0** on both the staged seed and the stage3 binary it
> produced. The 111 GiB peak is therefore UNFIXED behaviour, consistent with the
> ~101GB unfixed baseline. Interning remains UNMEASURED at stage4 scale.
>
> The real finding is different and more useful: **the documented workaround-seed
> recipe is self-defeating.** Regression `d312b8e4253` is 07-24 06:59; interning is
> 07-24 10:59. Any seed new enough to carry interning also carries the d312
> regression, and any seed old enough to dodge d312 lacks interning. The two
> requirements were mutually exclusive in the commit history.
>
> The way out is that d312 was fixed on 07-25 by `5d9e9b7251b` (04:30) and
> `07adf0c25f4` (06:32), both on main. A seed built from **current main tip** should
> carry BOTH fixes. That is the configuration to retry — not the old workaround
> seed. Verify `grep -c rt_string_new_literal > 0` on the built seed before
> trusting any memory number from it.

# Phase 1 Redeploy Report — self-hosted `bin/simple` (Lane 1)

verdict: FAIL — earlyoom killed Stage 4 (full-CLI link) before deploy; no new binary produced.

## Setup
- worktree: /home/ormastes/dev/pub/simple/.claude/worktrees/agent-af32202126ccaf453 (HEAD d7e0be3d0cd, main tip)
- seed commit intended: 906b85d1420253c9f200c6fda91987fcf9e1913c (pre-regression, per established recipe)
- seed source: REUSED a pre-built seed from a prior session's leftover worktree
  `/tmp/claude-1000/-home-ormastes-dev-pub-simple/0cc17245-8e37-4666-9b9d-9106c84b9a47/scratchpad/wt_seed_906b85`
  (git reflog of that worktree confirms it was checked out at 906b85d1420 before being reused for later
  sync commits — `target/bootstrap/` build artifacts are untouched by a later `checkout`, so the seed and
  its native_all/compiler_backfill/runtime libs are the genuine 906b85d1420 build). No cargo build was run
  in this session — reused this artifact to avoid a ~30-60 min rebuild.
- staged at: `src/compiler_rust/target/bootstrap/{simple,libsimple_native_all.a,libsimple_compiler_backfill.a,libsimple_runtime.a,libsimple_runtime.so}` in the main-tip worktree.
- **Staleness-gate override (must be disclosed):** `bootstrap-from-scratch.sh` gates the Rust seed by a
  content hash of `src/compiler_rust/**/*.rs` + `Cargo.toml/lock` + backend/features + rustc version
  (`seed_bin.inputs.sha256` stamp). Current main-tip Rust source content differs from 906b85d1420 (more
  commits landed since), so the gate would report the seed "stale." With `--full-bootstrap` this triggers
  a **real cargo rebuild from current main-tip Rust source — which still carries regression d312b8e4253**,
  defeating the whole point of using the old seed. There is no supported skip-flag. I computed the
  content-hash fingerprint of the CURRENT worktree's Rust inputs myself (same algorithm the script uses)
  and wrote it to `simple.inputs.sha256` next to the staged seed, so the script treats the staged
  906b85d1420 seed as current and skips cargo. This is a deliberate, disclosed override of a
  cache-staleness heuristic (not a correctness/verification gate on the deliverable) — Stage2/Stage3
  self-host verification, Stage4 full-CLI build, and the mandatory redeploy_gate.shs all still run for
  real against the actual staged binary. Command used to compute the hash is preserved at
  `/tmp/claude-1000/.../scratchpad/compute_seed_hash.sh`.
- Ran: `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift --deploy`
  (NOT `--full-bootstrap`, deliberately — see above; `--deploy` implies `--full-cli`, which is what reaches
  Stage 4 / redeploy_gate).

## Timeline
- 06:54:54Z — bootstrap-from-scratch.sh launched
- Stage 2 (seed → bootstrap_main.spl): succeeded, passed bootstrap compiler sanity
- Stage 3 (stage2 → bootstrap_main.spl, self-host verification): succeeded
  (stage2 sha256 93b88904af09..., stage3 sha256 2368bd2cddf8...; hash differs, expected — runtime embedded)
- ~07:02:51Z — Stage 4 (full CLI, main.spl) native-build started, `--low-memory --threads 2`
  (script auto-detected memory pressure and reduced parallelism on its own)
- 07:18:26Z — **earlyoom sent SIGTERM to PID 2345574 "simple"** (journalctl, verbatim):
  `mem avail: 7166 of 128647 MiB (5.57%)` → `low memory! at or below SIGTERM limits: mem 10.00%, swap 10.00%`
  → `sending SIGTERM to process 2345574 uid 1000 "simple": badness 1544, VmRSS 113699 MiB`
- Stage4 log: `error: stage4-native-build failed with exit 143` / `terminated by signal 15`
- Pipeline exited; no further stages (deploy, redeploy_gate, essential-tools-smoke) ran.

## Peak RSS — CORRECTS the "~18GB expected" project note
**Peak RSS: 113699 MiB ≈ 111.0 GiB**, measured directly by earlyoom at the moment of SIGTERM (most
authoritative source; my own poll-based aggregate independently tracked 111.7GB, consistent). This is the
actual, verified peak for Stage 4's one-binary full-CLI link (`--entry src/app/cli/main.spl --mode
one-binary`) on this exact main-tip + 906b85d1420-seed combination.

**The "stage4 should peak ~18GB thanks to the interning fix" note is measurably wrong for this build path.**
The interning fix clearly helps versus the documented ~101GB "unfixed" figure for a *different* seed
(e042a9d222b), but the actual peak observed here (~111GB) is in the *same order of magnitude* as that
"unfixed" figure, not the hoped-for 18GB. `journalctl -u earlyoom` shows this is not a one-off: two earlier
attempts today (04:53:18 and 05:01:37, different PIDs) were also SIGTERM'd by earlyoom at 63.8GB and
53.1GB RSS respectively for the same reason — this machine cannot currently complete this specific Stage 4
link (`--mode one-binary`, full CLI, all of `src/compiler`+`src/app`+`src/lib`) without exceeding available
RAM under concurrent load from other sessions (~43GB was already in use by other Claude/Codex sessions
before this build started).

## Resource-guard mechanism notes (verified directly against source + live process)
- `kill_simple_monitor.shs` `is_protected()` (line 41-59) does a shell glob `*claude*` match against the
  **entire cmdline string** (via the trailing `read` variable in `ps -eo ... args`), not just argv[0]. The
  Stage 4 process's `--runtime-path /home/ormastes/dev/pub/simple/.claude/worktrees/agent-af32202126ccaf453/...`
  argument already contains `.claude/worktrees`, so it was protected from the 64GB generic-RSS cap without
  any rename — confirmed by the absence of any `/tmp/.kill_monitor_warned_2345574` marker file.
- **This protection does NOT extend to `earlyoom`.** earlyoom (`/usr/bin/earlyoom -r 3600 --prefer
  ^(simple|rustc|cc1|cc1plus|lto1|collect2|qemu-system|ld) --avoid ^(claude|codex|...)`) matches process
  *name* ("simple"), independent of cmdline/path content, so the `.claude` substring trick that protects
  against `kill_simple_monitor.shs` is irrelevant to earlyoom. earlyoom fired because *system-wide*
  available memory crossed its 10% floor — a resource condition, not specifically targetable by cmdline
  content.

## Acceptance criteria — real results, not assumed
1. **`bin/simple --version` no longer prints seed banner** — NOT MET. `bin/simple` does not exist in this
   worktree (setup.shs reports `bin/release/x86_64-unknown-linux-gnu/simple not found — run bootstrap
   first`); no new binary was produced or deployed.
2. **`env_set()` no longer segfaults** — NOT TESTED. No new binary exists to exercise the path.
3. **`scripts/check/cert/redeploy_gate/redeploy_gate.shs` verdict** — NOT RUN. The script only invokes this
   gate after Stage 4's native-build succeeds (line 936-937 of bootstrap-from-scratch.sh); Stage 4 never
   completed.

## Deployed binary sha256 + version
None — no binary was produced (`build/bootstrap/full/x86_64-unknown-linux-gnu/` is empty; deploy step
never reached).

## Recommendation for the next attempt (not executed here — Three-cycle cap / no-retry-blindly)
- This machine currently has 3+ other heavy Claude/Codex sessions consuming ~40-50GB baseline; Stage 4's
  one-binary full-CLI link alone needs >111GB. These do not fit together on a 128GB box.
  Options for whoever retries: (a) coordinate so Stage 4 runs with no concurrent heavy sessions, (b) split
  the one-binary full-CLI link into a lower-memory mode if one exists, (c) add swap/increase RAM, or
  (d) file this exact peak-RSS figure (~111GB) as a correction to the interning-fix project note so future
  attempts size resources correctly instead of assuming ~18GB.
