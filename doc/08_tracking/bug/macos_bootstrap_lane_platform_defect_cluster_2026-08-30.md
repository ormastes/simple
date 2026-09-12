# macOS bootstrap lane: a cluster of eight platform defects, none of them visible from Linux

Status: OPEN (fixes landed for all eight; lane not yet green through Stage 2)
Area: bootstrap / runtime / tooling / macOS
Severity: blocker — no macOS bootstrap could start, and none could finish

Companion record for the first one found:
`macos_seed_unbuildable_metal_module_ungated_2026-08-30.md`.

## Summary

Attempting the sanctioned bootstrap on aarch64-apple-darwin surfaced **eight
independent defects**. Every one of them is correct on Linux and wrong on macOS,
and every one sat in `main` unnoticed. They are listed in the order the lane
found them, because that order is itself the finding: each was only reachable
after the previous was fixed, and four of them cost a ~25-minute compile to
discover.

| # | Site | Defect | Class |
|---|---|---|---|
| 1 | `.claude/hooks/ctx_common.shs:19` | `sed` BRE `\|` alternation | GNU-only syntax |
| 2 | `runtime/src/metal_graphics_runtime.rs` (69 sites) | cfg gated on `target_os` after deps went feature-optional | gate mismatch |
| 3 | `interpreter_extern/file_io.rs:327` | `u16` `mode_t` passed to variadic `open(2)` | Apple ABI |
| 4 | `interpreter_extern/file_io.rs:3052` | `st_mtimespec` — absent from libc on Apple | Apple libc |
| 5 | `check-bootstrap-preflight.shs:25` | `CARGO_TARGET_DIR=/mnt/data/...` | Linux-only path |
| 6 | `phase2-runtime-capsule.shs:66`, `bootstrap-stage3/authority.shs:1147` | `find -perm /0222` | GNU-only syntax, **fail-open** |
| 7 | `native_project/tools.rs:927` | weak-symbol detection via `nm` kind letters `W`/`V` | ELF-only symbol model |
| 8 | `io/process_ops.spl` (**two twin copies**) + `run-process-group-timeout.shs:12` | `setsid` | util-linux, absent on macOS |

## Why none of this was caught

`scripts/check/check-seed-builds-push.shs` exists and would catch the
compile-time members of this cluster, but it is in **no push-tier row** of
`config/check/must_check_gates.sdn`, so nothing runs it on a push. Even if it
were wired, it is **host-shaped**: a Linux pusher running it passes all eight,
because all eight are macOS-only. CI does have a `Native — macOS aarch64` job
and it is **failing on `main`**.

Two of the defects are worse than "it does not build", and are the reason this
record exists separately from the per-defect ones:

**#6 is fail-open in a security-relevant check.** Two frozen-capsule
immutability checks assert no file under a capsule is writable, via
`[ -z "$(find ... -perm /0222 -print -quit)" ]`. BSD find rejects the GNU
`-perm /MODE` syntax, writes `illegal mode string` to **stderr**, and prints
nothing to stdout — so the test saw an empty string and reported the tree
immutable regardless of actual permissions. Demonstrated on this host: a 0644
file under the scanned directory still yields a clean verdict.

**#5 made the gate that should have caught the others useless.**
`.claude/rules/bootstrap.md` instructs running `check-bootstrap-preflight.shs`
before *any* bootstrap. On macOS it failed unconditionally at
`failed to create directory /mnt/data/tmp`. A gate that is always RED on a
platform trains everyone on that platform to skip it.

## Diagnosis hazards encountered (worth reading before debugging this lane)

- **The lane reports these as `UNDIAGNOSABLE`.** #8 surfaced as
  `Stage 2 struct receiver/runtime capability failed` with
  `UNDIAGNOSABLE: the stage failed with no error message of any kind`, because
  exit 127 came from `/bin/sh`, not from a compiler diagnostic. The real text
  (`exec: setsid: not found`) was only in
  `build/bootstrap/stage3/<triple>/stage2-receiver.log`. Worse, the probe it
  was gating had already printed `bootstrap_stage2_struct_receiver=PASS` — the
  failure is *after* the thing whose name is in the error.
- **Duplicated module trees.** `src/app/io/process_ops.spl` is a near-twin of
  `src/lib/nogc_sync_mut/io/process_ops.spl` and the CLI resolves the **app**
  copy. Fixing the lib copy alone changed nothing and cost a full 25-minute
  rebuild to discover. This mirrors the known `test/01_unit` vs `test/unit`
  divergence that `check-test-tree-divergence.shs` polices; nothing polices the
  source twins.
- **Interactive `find`/`grep` may be shimmed.** In some environments `find` is a
  shell function wrapping a GNU-compatible implementation, so testing #6 by
  hand appears to *disprove* the bug. The bootstrap runs under `/bin/sh` and
  gets `/usr/bin/find`. Always test portability claims with absolute paths.
- **`nm` weakness is invisible in the kind column on Mach-O.** `nm -g -p`
  prints `T` for both a weak and a strong definition; only `nm -m` distinguishes
  them (`weak external`). Any tool reasoning about weak symbols from the kind
  letter is silently wrong on macOS.
- **The `exec` in a `setsid` wrapper is load-bearing.** Wrapping the fallback in
  a shell function invoked as `wrapper "$@" &` records the *subshell* in `$!`,
  leaving the real session leader a grandchild in the old process group — so a
  group kill signals the wrong group and a timed-out tree survives. The
  `run-process-group-timeout-test.shs` selftest catches this; it hangs without
  `exec` and passes with it.

## Fixes

All eight fixed, each in its own commit, each verified independently rather than
by "the lane got further":
- `cargo check --target aarch64-apple-darwin` clean for `simple-runtime`
  (73 errors -> 0) and `simple-compiler` (5 errors -> 0)
- `bash_net_blocker.shs --selftest`: 10 denied, 7 allowed, empty input denied
- `check-bootstrap-preflight.shs --selftest`: 9 fixtures, 0 failed
- `run-process-group-timeout-test.shs`: PASS, group terminated and reaped
- `find` and `nm` claims measured against `/usr/bin/find` and real fixtures

## Recommended follow-ups

1. Wire a **macOS** seed-build gate. Wiring `check-seed-builds-push.shs` on
   Linux alone would not have caught a single defect in this cluster.
2. Fix or acknowledge the failing `Native — macOS aarch64` CI job; while it is
   red on `main`, macOS regressions are indistinguishable from the baseline.
3. Consider a lint for GNU-only constructs in `.shs` (`sed \|`, `find -perm /`,
   `setsid`, `stdbuf`, GNU `mktemp` flags), since four of the eight are that
   single class.
4. Police the `src/lib` vs `src/app` module twins the way test-tree divergence
   is policed, or de-duplicate them.

## Re-audit 2026-09-12 (aarch64-apple-darwin, M4)

Status of this record's own subject — the eight defects — is unchanged: all
eight are fixed, and nothing in this re-audit found a ninth of that class.

What has moved is the "lane not yet green through Stage 2" qualifier, which is
what kept the record OPEN. The lane's *remaining* blockers were characterised in
`bootstrap_macos_blocked_seed_compile_and_linux_only_stage3_authority_2026-09-06.md`
as two independent items, A (the smoke driver hands the child procfs paths) and
B (the Stage-2 binary SEGVs in `serialize_mir_function`). Re-audited here:

- **Blocker A is CLOSED** as of `e1c40702a20` (2026-09-10), which added a
  `darwin-pinned` capture kind to `candidate_frontend_admission.shs`. Verified on
  this host by running its three shipped tests, all PASS — transcript in the
  companion record's "Re-audit 2026-09-12" section.
- **Blocker B was NOT re-reproduced in this session** — reproducing it requires a
  Stage-2 binary, and the `--full-bootstrap --stop-after-stage2` run started for
  that purpose spent its first 18m35s on a cold Rust seed build (246 crates,
  `Finished \`bootstrap\` profile [optimized] target(s) in 18m 35s` in
  `.simple/storage/build/bootstrap/logs/aarch64-apple-darwin/rust-seed-build.log`)
  — a useful datum on its own, since it is the cost any macOS lane pays before
  it can even attempt Stage 1. Whether Stage-2 admission then reproduces the SEGV
  was not settled within this session.
  Carrying the 2026-09-06 record's finding forward unverified: on that evidence
  blocker B is now the single remaining gating defect between this host and a
  Stage-2 admission. That is a citation, not a fresh measurement.

So this record's recommended follow-up #1 ("wire a macOS seed-build gate") is
still the right ask and is still unmet, but the cluster itself is no longer what
stops the lane.

Recommended follow-up #3 ("a lint for GNU-only constructs in `.shs`") gained
fresh evidence for being worth doing: the 2026-09-06 lane hit `stat -Lc` and an
unconditional `/proc/self/stat` read — the same GNU/Linux-only class as four of
the eight here — in a tree that had already been swept once. A one-off sweep does
not hold; only a gate does.
