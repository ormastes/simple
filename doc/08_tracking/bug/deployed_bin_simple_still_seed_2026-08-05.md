# Deployed `bin/simple` is still the Rust seed, not the self-hosted binary

- **ID:** BUG-2026-08-05-deployed-seed-not-selfhosted
- **Date:** 2026-08-05
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** medium — contradicts stated policy, hides pure-Simple interpreter
  fixes from `bin/simple run`/`bin/simple test` until redeployed

## Summary

`.claude/rules/bootstrap.md` states: "Default tooling = pure-Simple
self-hosted binary, not the Rust seed... resting state, not an emergency
stopgap." As of this date, `bin/simple` (symlink to
`bin/release/x86_64-unknown-linux-gnu/simple`) still prints:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
```

on every invocation, including `--version`, even though the file's mtime is
current (rebuilt today by some other lane). The binary being fresh does not
make it self-hosted — it is still a seed build.

## Consequence for interpreter-tier fixes

Source changes to `src/compiler/10.frontend/core/interpreter/*.spl` (the
pure-Simple tree-walking interpreter) are NOT executed by the deployed
`bin/simple run` / `bin/simple` bare-positional lanes, because:

- The Rust seed has its own, separate, native interpreter implementation
  (`src/compiler_rust/compiler/src/interpreter_control.rs`) that a program
  actually runs through on the seed — it does not dispatch through the
  `.spl` interpreter source tree.
- `bin/simple test` also hard-defaults to a tree-walk interpreter, but per
  `.claude/rules/testing.md` this is the SEED's own harness, not necessarily
  the pure-Simple `eval.spl` tree either, for ordinary (non-imported-as-library)
  execution.
- The `.spl` interpreter source tree IS reachable from the seed, but only as
  ordinary library code that a test file explicitly imports and calls
  functions from directly (as `test/01_unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl`
  does) — never as "the interpreter that runs subsequent arbitrary source",
  since the seed doesn't use it that way.

Net effect: a fix landed in `eval.spl`/`eval_decls.spl`/`eval_tables.spl` is
verifiable by importing and calling its functions directly from a spec (source
level), but is **not observable** by writing a `.spl` program and running it
through the deployed `bin/simple` today. This affected verification of
BUG-2026-08-01-match-fallthrough's severity-wiring follow-up (`SIMPLE_SAFETY_PROFILE`
promoting the match-fallthrough diagnostic to a hard error) — that wiring is
proven correct at the source/unit level (see
`test/01_unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl`)
but not end-to-end through `bin/simple run`.

## What was checked, not done

- Did not attempt a full bootstrap (explicit repo policy: ad-hoc incremental
  only, escalate only if proven insufficient; also explicit user instruction
  this session).
- Spot-checked existing `.bak` binaries under
  `bin/release/x86_64-unknown-linux-gnu/` for a usable self-hosted build.
  `simple.bootstrap-main-stage-2026-08-01.bak` does NOT print the seed
  warning (banner: `simple-bootstrap 1.0.0-beta`) and may be a genuine
  self-hosted or later-stage build, but its provenance/completeness was not
  verified and it was not promoted to `bin/simple` — that decision needs its
  own verification pass (what stage produced it, whether it has full
  LLVM/JIT/interpreter parity), not a drive-by symlink swap while fixing an
  unrelated feature.

## Suggested next step (not done here)

Verify `simple.bootstrap-main-stage-2026-08-01.bak` (or a fresh T1 incremental
build per `.claude/rules/bootstrap.md`) end-to-end against a small test suite
before considering it for promotion to `bin/simple`.

## Update 2026-08-06 — full T3 bootstrap redeploy attempted, still blocked

Per explicit user authorization this session, a full T3 bootstrap was run
(escalating past the ad-hoc-incremental-only policy noted above):

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --output=build/bootstrap-t3-redeploy-20260806 --progress
```

- Verified no competing bootstrap process was already running before starting
  (one unrelated, already-finished ad-hoc stage2→stage3 replay from earlier in
  this session was found and NOT raced — it had already exited by the time it
  was checked).
- Rust seed/runtime cargo rebuild **succeeded**, picking up today's HEAD
  commits (`i64.to_char`, `rt_array_data_ptr_u8`, `rt_io_file_*` interpreter
  registrations, SIMD FFI alignment fix) — the seed at
  `src/compiler_rust/target/bootstrap/simple` is no longer stale.
- Stage 2 (seed → `bootstrap_main.spl`) **passed**.
- Stage 3 (stage2 self-host) **failed**: `HIR lowering error in
  src/compiler/driver/cache/cache_validator.spl: unresolved type: ByteOrder`.
  The wrapper correctly refused to fall back to the seed for the full CLI
  build/deploy. Full diagnosis, evidence, and next steps filed as a new bug:
  `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`.
- `bin/simple` / `bin/release/x86_64-unknown-linux-gnu/simple` **remain the
  Rust seed** — nothing was promoted or deployed. The Rust seed binary was
  **not** copied to `bin/release/.../simple` (standing prohibition honored).
  `src/compiler_rust/linker/native_binary/stubs.rs` / `RT_KEEP` was not
  touched (explicit out-of-scope boundary for this task).
- Net effect: this remains an OPEN blocker, now with a precise, evidenced
  root-cause candidate (see the new bug doc) rather than "bootstrap not
  attempted".

## Related

- `.claude/rules/bootstrap.md` — stated policy this contradicts
- `doc/08_tracking/bug/match_enum_fallthrough_silent_2026-08-01.md` — the
  feature whose severity-wiring follow-up this gap affects
- `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
  — 2026-08-06 full-bootstrap attempt and the Stage 3 blocker it hit

---

## 2026-08-17 re-verification (wave_01 lane H3) — STILL LIVE, confirmed by probe

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59536728 2026-08-16 22:59:37.799277177 +0000
$ nice -n 19 timeout 60 bin/simple --version ; echo rc=$?
rc=0
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
```

Unchanged in substance since 2026-08-05: the artifact is fresh (rebuilt
2026-08-16 22:59 by another lane) and still self-identifies as a seed. Freshness
is not self-hostedness.

**Two corrections to the surrounding record, both established today:**

1. This is now the ONLY live member of the deployed-binary family. Its sibling
   `deployed_bin_simple_bootstrap_only_2026-07-31.md` was closed today as
   not-reproducing: the current seed accepts `test`/`lint` and compiles a bodiless
   `@extern fn` at rc=0. The "bootstrap-only, `compile`-only" condition is gone;
   only the seed-vs-self-hosted condition remains.
2. `bin/release/.../simple` (this bug, a Rust seed) and
   `release/.../simple` (SHA-256 `04a38e21…`, a stale pure-Simple artifact that
   SIGSEGVs — `deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`) are
   different files on different paths. Both were re-probed today and both still
   hold. Do not conflate them.

**No fix attempted.** The remedy is a redeploy
(`--full-bootstrap --deploy`), which this lane is explicitly forbidden to
perform (a bootstrap is live and owns the box). Status stays OPEN (P2) as a
deployment-state item, not a source defect.

## Update 2026-08-24 — optimizer verification remains blocked

The SFFI hardening lane invoked the documented optimizer entrypoint through
`bin/simple`. The release symlink resolved to
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
a 60,650,360-byte executable that again printed the Rust bootstrap-seed warning.
The three attempted optimizer processes measured 8.48 s / 270,628 KiB, 5.67 s /
280,312 KiB, and 5.34 s / 279,484 KiB, respectively, but those findings are
diagnostic-only and cannot be accepted as pure-Simple verification. No retry or
seed substitution was performed.
