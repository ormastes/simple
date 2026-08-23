# lane-bootstrap — self-hosted deploy plan / handoff (2026-08-19)

Goal given to this lane: get a working pure-Simple self-hosted compiler deployed.
Status: **NOT deployed.** Stage 1 and Stage 2 pass; Stage 3 has never completed.

## What actually blocked it (root cause, fixed)

origin/main's **Rust seed did not compile**, so no bootstrap could clear Stage 1.
This is why four "redeploys" on 2026-08-18 all produced a seed: they were cargo
seed refreshes that never reached a bootstrap stage.

`scripts/check/check-bootstrap-preflight.shs`: `FAIL` (cargo-check) -> `PASS` after the fix.

Three independent half-landed merges:

| Error | File | Cause |
|---|---|---|
| E0592 duplicate `INLINE_INT_BITS` | `runtime/src/value/core.rs` | `b8ca72d8c3b` re-introduced what `4e265503e0c` fixed — stale-forward clobber |
| E0432 `module_globals_generation` undefined | `interpreter_call/core/function_exec.rs` | `7dc9d1f962f` landed import + call sites, never the definition |
| E0599 `as_ref()` on `&FunctionDef` | `interpreter_sffi.rs` | `faf5e71bfa6`, a single line unrelated to that commit's subject |

Fixed locally in `e14f8796cd2`. **This commit must NOT be pushed** — verified
2026-08-18 that origin/main now fixes all three independently (`0aeebdbe425`,
`a5c30b6bba1`, which port a `GenTrackedCell` design differing from mine).
Pushing it would be exactly the stale-forward clobber that caused defect #1.
Correct action for the next session: **abandon `e14f8796cd2`**, rebase, and
re-verify the bootstrap against origin's version of the fix.

## Progress reached

- **Stage 1** (Rust seed + runtime): PASS. Produces
  `src/compiler_rust/target/bootstrap/simple` (156406992 B) and
  `libsimple_native_all.a` (375594022 B) — artifacts that existed in NO worktree before.
- **Stage 2**: PASS, admitted. `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`,
  131399424 B, banner `simple-bootstrap 1.0.0-RC`, no seed warning, non-vacuous.
- **Stage 3**: FAILED twice, **both times by SIGTERM (exit 143), never by a compile error.**
  Killed ~1 min in during phase-2 parse, after loading all 888 sources cleanly.
- **Stage 4**: never reached.

## The receipt gate (solved — do not re-derive this)

`--full-bootstrap --deploy` exits 64 with `bootstrap-policy-error: reason-receipt-required`.
The rules file does not mention this. Findings:

- The ONLY receipt-free entry is the trust root: `--full-bootstrap --stop-after-stage2 --mode=dynload`.
- The planner (`bootstrap_receipt_main.spl`) must NOT be invoked by hand; it only records
  hashes. The verifier wants a 29-field admission emitted solely by
  `scripts/bootstrap/bootstrap-from-scratch.sh planner-admission-v2`.
- Working invocation:
  `produce-bootstrap-planner-admission-v2.shs --target=//bootstrap:stage4
   --reason=self-host-convergence-check --parent-compiler=build/bootstrap/stage2/<triple>/simple --out=<path>`
- `//bootstrap:stage2` is authorized by NO typed reason — hence the trust-root exception.
- A produced receipt is at `<scratchpad>/admission-stage4.env` (`status=pass`).

## Why Stage 3 died — host, not compiler

Two distinct killers, which is why this looked contradictory:

1. **earlyoom** (`-r 3600 --prefer ^(simple|rustc|...)$ --avoid ^(claude|...)$`) SIGTERMs at
   10% free memory. 699 SIGTERMs at `simple` in 6h. Userspace, so **nothing appears in dmesg**.
   `simple` is top of its kill list, so the compiler is the designated victim of any host pressure.
2. **Kernel OOM killer** took 3 claude sessions at 23:30:27 because a memory-guard script had
   set `oom_score_adj=1000` on them.

Underlying input: 28 orphaned `simple test` processes held **90.8 GB** of 125 GB, swap **0**.
Reaped 2026-08-19 -> 109 GB free. `lane-stage3-memguard` owns the durable fix and has already
landed the wrapper change so a signal death is no longer reported as `stage3 self-host failed`.

## Next session, in order

1. Abandon `e14f8796cd2`; `jj git fetch && rebase -d main@origin`; re-run preflight.
2. Re-run trust-root Stage 2, then the Stage 3+4 run with a fresh admission receipt.
   Do it while memory is free — the two failures were both host kills, so Stage 3 is
   **unproven, not known-broken**. Do not report it as a compiler defect without a
   non-143 exit.
3. Verify any Stage 4 binary with `<scratchpad>/verify_stage4.sh` — symbol/size floors,
   seed-banner rejection, full-CLI subcommand set, a negative control that Stage 3 REJECTS
   `lint`, and a real compile+execute. **Exit code is not evidence**: a vacuous Stage 3/4
   binary has previously exited 0.
4. Deploy only after that passes. `--deploy` runs `setup.shs`, which repoints this
   worktree's `bin/simple` (currently a symlink into the shared simple-main tree).

## Unverified / open

- Stage 3 has never been observed to fail for a compiler reason. Unknown whether it passes.
- `verify_stage4.sh` size/symbol floors are conservative guesses — no known-good Stage 4
  binary existed to calibrate against.
- `land.shs` runs 2 of 63 guards (mandatory ones sit in rules.sdl group `full`, it gates
  `quick`). Patch prepared at `<scratchpad>/land_shs_seed_guard.patch`, `git apply --check`
  clean, **not applied**.
- Duplicate top-level declarations in `.spl` are silent: `SymbolTable.define`
  (`src/compiler/20.hir/hir_types.spl:299`) is first-wins for types, **last-wins for functions**
  (`:363`, unguarded), and never diagnoses. One confirmed live defect in
  `simple_web_html_layout_renderer_foundation.spl` (weaker validator wins). Unfiled by this lane.
