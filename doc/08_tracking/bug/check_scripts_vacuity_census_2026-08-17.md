# scripts/check vacuity census — guards that pass by construction or exit mute

**Date:** 2026-08-17
**Status:** OPEN
**Lane:** scripts
**Related:** `doc/08_tracking/bug/engine_divergence_guard_hardcodes_stale_seed_2026-08-17.md`

## Summary

Census of all 637 `scripts/check/*.shs` against the two vacuity failure modes
named in `.claude/rules/vcs.md`: (a) pinning to a hardcoded, possibly stale
binary, and (b) exiting 0 having checked nothing / exiting non-zero without a
verdict line.

Measured, not inferred, unless marked.

## Census (measured by static scan, 2026-08-17)

| category | count (of 637) |
|---|---|
| A. references `bin/simple` with **no** `SIMPLE_BIN`/`SIMPLE_BINARY` override | 87 |
| B. contains **no** verdict token (`PASS —`/`FAIL —`/`ERROR —`) at all | 478 |
| C. has `PASS —`/`FAIL —` but **no** `ERROR — nothing was checked` path | 37 |
| D. has verdict lines but **no** `--selftest` | 103 |

Restricted to the 67 guards actually **wired** into the pre-push hook /
`land.shs` / `*.sdl` rule groups — i.e. load-bearing:

- **16 wired guards** are in category A (hardcoded `bin/simple`, no override).
  `bin/simple` here resolves to `bin/release/x86_64-unknown-linux-gnu/simple`,
  a Rust seed built **2026-08-16 22:59:37** — a guard pinned to it reports on
  the seed regardless of tree content.
  `check-engine-claiming-specs-use-probe`, `check-env-get-dead-fallback-guard`,
  `check-env-get-nil-abort-guard`, `check-lexer-radix-literal-suffix`,
  `check-lint-binary-staleness`, `check-lint-census`, `check-no-jit-module-drop`,
  `check-predicate-parser-native-build`, `check-render-perf-milestone-gate`,
  `check-simpleos-shell-hello-e2e`, `check-spec-lane`,
  `check-test-tree-divergence`, `check-trait-solver-method-resolution-variant`,
  `check-ui-showcase-layering`, `check-use-warning-oracle-deployed`,
  `check-utf8-slice-audit-live`.
- **12 wired guards** are in category B (no verdict line at all).

## Confirmed fail-open, by execution (exit code read into a variable, never through a pipe)

| guard | exit | last stdout line | defect |
|---|---|---|---|
| `check-cpu-backend-artifacts.shs` | **0** | `cpu_backend_matrix status=SKIP_UNAVAILABLE failures=0 skips=18` | passes having checked **0** of 18 items; no verdict line |
| `check-gpu-backend-layer-evidence.shs` | **0** | `gpu_backend_matrix status=SKIP_UNAVAILABLE backends=5 layers=20 ...` | same shape: every backend skipped, still exit 0 |
| `check-gui-web-2d-completion-criteria-placeholders.shs` | 0 | `gui_web_2d_completion_criteria_report=...` | exit 0, no verdict line |
| `check-x25519mlkem768-cpu-simd.shs` | 0 | `STATUS: PASS ...` | non-conforming verdict format (`STATUS: PASS`, not `PASS — <n> checked`); count never stated |
| `check-bootstrap-platform-handoff-readiness.shs` | **1** | `platform_acceptance_claimed=false` | exits 1 **mute** — same defect class as the trailing-default-param guard |
| `check-lint-census.shs` | 2 | `ERROR: no targets given ...` | exit 2 but non-conforming verdict text |

`SKIP_UNAVAILABLE` returning exit 0 is the highest-severity item here: it is
indistinguishable, to any caller reading only the exit code, from a run that
verified all 18/20 items. Per the project convention, absence of a backend is
absence of evidence and must be `ERROR — nothing was checked` (exit 2), or at
minimum a `PASS` line that STATES `0 checked`, which then trips the
n > 0 rule.

## Why these were not fixed in this pass

Whether `SKIP_UNAVAILABLE` should be ERROR or a recorded-skip PASS is a policy
call about the GPU/CPU-backend and crypto lanes' intent on a machine with no
such hardware, not a mechanical reporting fix. Changing it blind would alter
each guard's verdict, which the scripts lane was explicitly scoped out of.
Filed rather than guessed.

## Fixed in this pass

`scripts/check/check-native-trailing-default-param.shs` only — see that file's
header. Two defects: (1) `set -eu` + bare `test -x bin/simple` exited **1 with
zero bytes of output** from a worktree with no built compiler; (2) a caller's
`FIXTURE`/`SIMPLE_BINARY` env leaked into the `--selftest` recursion, so
`FIXTURE=missing.spl <guard>` aborted with "selftest failed" instead of the
real missing-fixture ERROR. Selftest extended from 7 to 8 fatal fixtures.

## Suggested order of work

1. `check-cpu-backend-artifacts` / `check-gpu-backend-layer-evidence` — the two
   proven fail-opens.
2. `check-bootstrap-platform-handoff-readiness` — mute exit 1.
3. The 16 category-A wired guards — apply the established
   `SIMPLE="${SIMPLE_BIN:-$ROOT/bin/simple}"` pattern plus a refusal to PASS
   when the binary predates the newest source it probes.

## 2026-11-09 re-census (release/1.0.0)

Re-derived against the current tree. Items 1–2 above and every guard in the
"Confirmed fail-open, by execution" table now emit conforming
`PASS —`/`FAIL —`/`ERROR — nothing was checked` verdicts with exit 0/1/2
(most via 0f5b67b79b4; the named repro target
`check-jit-unresolved-symbol-guard.shs` is sound by construction, KNOWN-RED
until the seed JIT is fixed).

Seven additional wired gates were made sound in this pass (all verified with
clean-PASS / sabotage-FAIL / environment-ERROR fixtures):

- `check-runtime-concat-nul.shs` — was `set -eu` mute abort + no verdict at
  all; now verdict-conforming. Its probe also gained the sibling-pattern
  `spl_panic` stub (`rt_text_clone_contract_selfcheck.c` et al. already do
  this) so it links `runtime_native.c` at all.
- `check-session-heap-reclaim.shs`, `check-tcp-write-nosigpipe.shs`,
  `check-allocation-registry-churn.shs` — same mute `set -eu` /
  exit-1-without-verdict shape; now verdict-conforming.
- `check-tui-standalone-closure.shs` — `error=` lines + mute exit 1, fixed
  `/tmp` scratch file; now verdict-conforming with mktemp scratch.
- `check-module-surface-hint-scan-fast-path.shs` — `error=` exits and
  non-conforming `STATUS: PASS`; now verdict-conforming.
- `check-trace-query-p0.shs` — mute `|| exit 2` git-plumbing paths and a raw
  spec-status exit with no guard verdict; now every exit path names a
  PASS/FAIL/ERROR verdict.

Remaining backlog: 63 of the 201 gates wired in
`config/check/must_check_gates.sdn` still lack a conforming verdict or FAIL
emitter (this count includes colon-style/`STATUS:` partial conformers; the
GPU/CPU-backend `SKIP_UNAVAILABLE` policy question above is still open).

## 2026-11-09 wave 2 (work/p3-gate-oracle2-20261109)

Eight more wired gates were made verdict-conforming in this pass (each
verified with a clean-tree run, a sabotage fixture FAIL (rc=1, verdict last
line), and a missing-input/unreadable-scan ERROR (rc=2) where applicable;
`sh -n` clean on all):

- `check-lib-common-no-os-import.shs` — hyphen-style `PASS/FAIL/ERROR -`
  verdicts (non-conforming per the em-dash convention) converted; the fs scan
  also piped grep into `extract`, so a grep hard-failure (rc 2) scanned as
  "0 imports" — now read directly, rc > 1 is ERROR.
- `check-bootstrap-stale-runtime-archive-selftest.shs` — hyphen-style verdicts;
  `mktemp -d || exit 2` mute abort now names an ERROR verdict.
- `check-bootstrap-phase-collect-failures.shs` — colon-style `PASS:`/`FAIL:`
  verdicts and `set -eu` mute aborts (mktemp, missing runner); every exit
  path now names a verdict, missing runner is ERROR, runner-shape change is
  FAIL. Verified against a sabotaged runner whose failure latch was erased
  (FAIL, rc=1).
- `check-shs-native-tool-boundary-preserved.shs` — hyphen-style verdicts
  converted. NOTE: honestly RED on this host before and after (boundary file
  INCLUDE/LIB form); only the verdict separator changed.
- `check-tracking-doc-registration.shs` — `PASS rows=…`/`FAIL rows=…`/`ERROR
  incomplete-scan` non-conforming verdicts converted; six mute `|| exit 2`
  paths (usage, root, missing db, shard merge, mktemp, find) now name ERROR
  verdicts; audit-engine crash (rc>=126) is ERROR instead of propagating a
  mute code. Its selftest (`test/01_unit/scripts/tracking_doc_registration_test.shs`)
  tokens updated to the new format. Still honestly RED (670 pre-existing
  registration findings, unchanged counts).
- `check-memory-deallocation-ownership.shs` — colon-style verdicts and
  `set -eu` mute aborts; an unreadable retired-API authority scan was
  misclassified as FAIL — now `ERROR — nothing was checked` (exit 2); PASS
  now states the invariant count (32).
- `check-runtime-log-hosted-probe-head.shs` — colon-style PASS and mute
  aborts (mktemp, missing cc, compile failure, probe failure, header
  mismatch); all now named. Non-Linux `SKIP:` exit 0 converted to ERROR
  exit 2 per the absence-of-evidence convention (the probe cannot run, so
  nothing was checked).
- `check-crypto-verify-symbol-collisions.shs` — `OK`/`FAILED` colon-style
  verdicts; the definition scan masked grep failures with `|| true`, so an
  unreadable/absent `src/` scanned as "0 definitions, clean" (fail-open) —
  grep rc is now read directly, rc > 1 is ERROR; unknown-option path emits
  an ERROR verdict.

Remaining backlog: 55 of the 201 wired gates (63 minus these 8). The
GPU/CPU-backend `SKIP_UNAVAILABLE` policy question remains open and is now
the largest single class in the backlog; gates needing binaries, GPU,
Windows, or QEMU machinery stay in the backlog per lane policy.

## 2026-11-09 wave 3 (work/p3-gate-oracle3-20261109)

Eight more wired gates were made verdict-conforming in this pass. Each was
verified with a clean-tree run (where the gate is green on this host), a
sabotage fixture FAIL (rc=1, verdict last line), and a missing-input or
unreadable-scan ERROR (rc=2) where applicable; `sh -n` and `bash -n` clean on
all eight. No gate's actual checks were weakened; two genuinely fail-open
grep paths now fail closed:

- `check-no-placeholder-callbacks.shs` — hyphen-style `PASS -` verdicts; the
  hit grep was piped through two filters, so a grep hard-failure (rc 2, e.g.
  an unreadable tree) scanned as "0 hits" and passed — the grep rc is now
  read directly, rc > 1 is ERROR.
- `check-tierless-std-js-imports.shs` — `PASS --`/`FAIL --`/`ERROR --`
  verdicts converted; the count grep piped into `wc` masked rc > 1 the same
  way — now read directly, ERROR; the selftest's unchecked `mktemp` now
  names an ERROR verdict.
- `check-enum-discriminant-convention-fence.shs` — hyphen-style verdicts;
  both source greps masked hard failures (one piped into `while`, one a
  `! grep -q` whose rc 2 read as "convention changed") — now ERROR.
  NOTE: honestly RED on this host before and after: `runtime_native.c`
  mentions `hash_variant_discriminant` in a prose comment and the
  bare-symbol grep trips on it; only the separator changed — the fence
  semantics were not touched.
- `check-product-private-repository.shs` — per-control `PASS <name>` lines
  and rejection paths that exited 1 with **no verdict at all**; every
  control now names a FAIL verdict on refusal and the run ends
  `PASS — 4 controls checked`; missing lib / mktemp failure is ERROR.
- `check-product-private-materialization.shs` — same shape: mute `exit 1`
  rejections and bare `set -eu` asserts; now named FAIL verdicts and
  `PASS — 9 controls checked`.
- `check-stage2-parent-runtime-inheritance.shs` — colon-style `PASS:` and
  `FAIL:` lines plus `set -eu` mute aborts (mktemp, assertion failures, the
  env-var leak check); every exit path now names a verdict,
  `PASS — 5 control(s) checked`.
- `check-stage2-parent-runtime-launcher.shs` — same; the refusal-reason grep
  and the selection-block extraction now name FAIL verdicts,
  `PASS — 6 control(s) checked`.
- `check-test-aggregate-rss-policy.shs` — `FAIL:` to stderr (so stdout's
  last line was not a verdict) and colon-style `PASS:`; missing
  perl/guard/mktemp paths were mute — now named ERROR. The env-override
  rejection runs in a subshell whose failure now propagates the verdict
  instead of a mute `set -eu` abort. NOTE: honestly RED on this host before
  and after: the watchdog's compiler ceiling moved (48 GiB) while the gate
  still asserts the old 8 GiB admission bounds — checks untouched; the run
  now fails closed with a named verdict.

Remaining backlog: 47 of the 201 wired gates (55 minus these 8). The
GPU/CPU-backend `SKIP_UNAVAILABLE` policy question remains open; gates
needing binaries, GPU, Windows, QEMU, rustc, or an admitted Stage-2 compiler
stay in the backlog per lane policy.




## 2026-11-09 wave 4 (work/p3-gate-oracle4-20261109)

Backlog re-derived from the live tree first: the gate registry grew since the
wave-1 count (many rows marked "wired 2026-11-09" from guard-wiring triage),
so the wired universe is now 245 unique gate scripts, of which 80 lacked a
conforming em-dash verdict at wave-4 start (the documented 47 was measured
against the smaller registry; the growth is newly wired gates, not a
methodology change).

Eight more wired gates were made verdict-conforming in this pass. Each was
verified with a clean-tree run (PASS, rc=0, verdict last stdout line), a
sabotage fixture (named FAIL, rc=1), and a missing-input/unavailable-tool
fixture (named ERROR, rc=2) where applicable; `sh -n` and `bash -n` clean on
all eight. No gate's actual checks were weakened:

- `check-watchdog-monotonic-budget.shs` — hyphen-style `ERROR -`/`FAIL -`
  verdicts emitted via `die` (stderr, exit 255) and a Test::More harness whose
  failures exited 255 with no verdict; now every exit names a verdict
  (exit 0/1/2), Test2 counters are read explicitly (`no_ending` prevents the
  Test::More END block from overriding the exit code), and 0 checks ran is
  ERROR.
- `check-no-unbounded-tcp-read-line.shs` — hyphen-style verdicts; the scan
  grep rc was swallowed by command substitution so an unreadable tree read as
  "0 files" — rc is now read directly, rc > 1 is ERROR.
- `check-mir-class-identity-raw.shs` — hyphen-style verdicts; the hit grep was
  piped through `xargs` inside command substitution so grep rc 2 (unreadable)
  scanned as "0 hits" fail-open — now a direct recursive grep, rc > 1 is
  ERROR, and 0 scanned files is ERROR.
- `check-bootstrap-channel-host-selection.shs` — `set -eu` mute aborts
  (mktemp, owner extraction, every assertion) and colon-style FAIL to stderr;
  now named verdicts, `PASS — 8 ... cases` + `PASS — 4 ... cases`, missing
  owner is ERROR.
- `check-committed-control-materialization.shs` — `set -eu` mute aborts and
  colon-style FAIL; fixture git/materialize failures are ERROR, materialize
  refusing a valid fixture is FAIL, `PASS — 15 ... assertions`.
- `check-stage4-continuation-receipts.shs` — `set -eu` mute aborts, FAIL to
  stderr, and a non-conforming final line; finalize/verify/cmp failures now
  name FAIL verdicts, missing libs/mktemp are ERROR,
  `PASS — 17 receipt-graph checks`.
- `check-submodule-branch-ancestry-fixture.shs` — `set -eu` mute aborts and
  bare `test` assertions; fixture git failures are ERROR, ancestry
  mismatches name FAIL, `PASS — 7 shallow-ancestry checks`.
- `check-bootstrap-stage2-resume-platform.shs` — `set -eu` mute aborts
  (extraction, contract grep, canonical-case refusal) and printf PASS;
  empty extractions are ERROR, contract-text drift is FAIL,
  `PASS — 24 platform path cases`.

Remaining backlog: 72 of the 245 wired gate scripts (80 minus these 8; the
201-gate figure is stale — the registry grew same-day). The
GPU/CPU-backend `SKIP_UNAVAILABLE` policy question remains open; gates
needing binaries, GPU, QEMU, rustc, lake, or an admitted Stage-2 compiler
stay in the backlog per lane policy.

## 2026-11-09 wave 5 (work/p3-gate-oracle5-20261109)

Backlog re-derived from the live tree first: 245 unique wired gate scripts,
72 non-conforming at wave-5 start (unchanged from wave 4 — waves 1–4 all
merged, 31 scripts fixed; the re-derivation reproduced the wave-4 count
exactly).

Eight more wired gates were made verdict-conforming in this pass. Each was
verified with a clean-tree run (PASS where green on this host, rc=0, verdict
last stdout line), a sabotage fixture (named FAIL, rc=1), and a
missing-input/unavailable-tool fixture (named ERROR, rc=2) where applicable;
`sh -n` and `bash -n` clean on all eight. No gate's actual checks were
weakened:

- `check-bug-difficulty-coverage.shs` — colon-style `PASS:`/`FAIL:` with the
  findings printed after the verdict line, ERROR to stderr, mute `exit 2` on
  a missing db, awk/grep exit statuses unreadable through pipes, and no
  vacuity guard for a parse that finds zero non-closed bugs; now em-dash
  verdict as the last stdout line (findings first), ERROR on missing db /
  awk failure / zero parsed rows, exit 0/1/2. NOTE: honestly RED on this
  host before and after: 830 of 1230 non-closed bugs lack difficulty rows —
  the check itself is untouched, the run now fails closed with a named FAIL.
- `check-requalification-control-state.shs` — colon-style PASS and `set -eu`
  mute aborts (mktemp, git init/commit, python3, fixture materialize/seal)
  plus FAIL to stderr; every exit path now names a verdict, missing
  tools/fixture failures are ERROR, `PASS — 18 qualification control-state
  assertions`.
- `check-llm-strict-host-prereq-doctor-contract.shs` —
  `STATUS: PASS`/`STATUS: FAIL` machine lines (the FAIL path ended stdout
  with a non-conforming line and never emitted `FAIL —`), hyphen-style
  verdicts, and an ERROR that went to stderr only; now the em-dash verdict
  is always the last stdout line (env evidence file unchanged), the mkdir
  mute abort names an ERROR, vacuity floor intact.
- `check-llm-finetune-setup-contract.shs` — same shape (34 contract cases);
  verdict block conformed, mkdir mute abort named ERROR.
- `check-llm-runtime-slang-setup-contract.shs` — same shape (41 cases).
- `check-llm-runtime-torch-setup-contract.shs` — same shape (33 cases).
- `check-shs-path-conversion-equivalence.shs` — hyphen-style verdicts
  converted to em-dash; exit statuses were already read directly (never
  through pipes) and the zero-assertion ERROR already existed, so only the
  verdict separator changed. Verified: sabotaged classifier selftest →
  `FAIL —` rc=1; unwritable TMPDIR → `ERROR —` rc=2; clean PASS — 2
  assertions (execution half honestly not-run: no cygpath on Linux).
- `check-split-impl-import-visibility.shs` — hyphen-style verdicts, an
  unchecked `mktemp -d`, and a mute `selftest || exit 2`; now em-dash
  verdicts, mktemp/selftest failures name ERROR, `--selftest` prints
  `PASS — selftest only, 3 fixtures`. NOTE: honestly RED on this host before
  and after: 6 new unimported split-impl calls vs the frozen baseline
  (105 total across 72 split types) — the check itself is untouched, the run
  now fails closed with a named FAIL.

Remaining backlog: 64 of the 245 wired gate scripts (72 minus these 8). The
GPU/CPU-backend `SKIP_UNAVAILABLE` policy question remains open; gates
needing binaries, GPU, QEMU, rustc, lake, or an admitted Stage-2 compiler
stay in the backlog per lane policy.
