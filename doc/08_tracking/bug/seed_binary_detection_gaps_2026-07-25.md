# Bug: seed-binary detection is path-based and defeated by cosmetic misdetection

**Date:** 2026-07-25  
**Status:** DETECTION UNRELIABLE - Identification gap in evidence gates

## Problem
The `is_rust_seed_simple()` classifier in `check-hosted-wm-capture-evidence.shs` uses path substring matching (`src/compiler_rust/*`) as its sole detection criterion. A seed binary copied to a self-hosted-looking deploy path is silently accepted by evidence gates.

Aggravating: the deployed stage4 self-hosted binary itself prints the seed WARNING line in some run lanes (known cosmetic misdetection, recorded in `doc/03_plan/compiler/bootstrap/stage4_macos_deploy_2026-07-25.md`) and embeds the warning string. This links seed driver components, causing string/warning probes to misclassify the self-hosted binary as seed.

**Result:** Identification is unreliable in both directions.

## Consequence
- Deployed self-hosted binaries may be rejected or incorrectly validated
- Seed binaries with relocated paths bypass detection
- Evidence matrix gates cannot reliably distinguish self-hosted from seed runs
- Blocks reproducible evidence collection

## Fix Direction
Implement a definitive self-ID channel (e.g., `--version` reporting: `build_lane=seed|stage4-selfhosted` + `source_sha=<hash>`). Consume this across all evidence-gate scripts. Fix the cosmetic warning misdetection at its root in the deployed binary.

---

## 2026-08-17 — REPRODUCED on the real default binary, then FIXED (content-based classification)

### Reproduction (no synthetic copy needed — the deployed default already defeats it)

The doc framed this as "a seed binary *copied* to a self-hosted-looking deploy
path". It is worse than that: the binary the whole repo defaults to is already at
such a path. `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
which `--version` announces as a seed, has no `src/compiler_rust/` component in
its resolved path. Running the old classifier verbatim against the live tree:

```
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple  path_verdict=NOT-SEED  content_truth=SEED
/mnt/data/worktrees/simple-main/bin/simple                                   path_verdict=NOT-SEED  content_truth=SEED
/mnt/data/worktrees/simple-main/bootstrap/stage3/simple                      path_verdict=NOT-SEED  content_truth=NOT-SEED
```

`content_truth` is `grep -a -c 'bootstrap seed only'` on the binary. So the
pre-flight admission gate (`SIMPLE_BIN_STATUS=forbidden`, line ~110) never fired
for the seed; the seed was admitted, launched, and only caught *post hoc* by the
runtime log grep at what is now line ~217 — and when the capture run failed or
timed out first, the reported reason was `capture-program-failed` /
`hosted-wm-capture-timeout`, misattributing a forbidden-binary run.

### The "aggravating" half of this doc is STALE — measured, not assumed

The doc claims the deployed self-hosted binary "embeds the warning string", so
string probes misclassify it as seed, making detection unreliable *in both
directions*. Measured on the in-tree binaries:

| binary | size | `grep -a -c 'bootstrap seed only'` |
|---|---|---|
| `bin/release/x86_64-unknown-linux-gnu/simple` (seed) | 59,536,728 | **1** |
| `bootstrap/stage3/simple` (self-hosted) | 3,464,072 | **0** |

`grep -rn 'bootstrap seed only' src/` finds exactly one emitter,
`src/compiler_rust/driver/src/seed_warning.rs:20` — Rust-only, with no
Simple-side counterpart. So a binary-content probe separates the two correctly in
both directions, and the second-direction failure this doc asserts does not
reproduce. The `--version`-based `build_lane=` self-ID channel in "Fix Direction"
is therefore not required to close this row (it remains a reasonable
improvement, but it is not the blocker the doc implies).

### Fix

`scripts/check/check-hosted-wm-capture-evidence.shs` — `is_rust_seed_simple()`
is now **content-first**: the `src/compiler_rust/` path case is kept as an
additional *positive* signal (it catches a seed built in place that has not been
run or deployed), and a `grep -a -q -F` probe for the seed-warning literal
decides every other candidate. Seed identity is a property of the binary, not of
where it happens to sit.

Verified against the live tree — the gate now fails closed **pre-flight**, with
the correct reason instead of a misattributed one:

```
$ SIMPLE_BIN=bin/simple sh scripts/check/check-hosted-wm-capture-evidence.shs
hosted_wm_capture_status=fail
hosted_wm_capture_reason=simple-bin-forbidden
hosted_wm_capture_simple_bin_source=explicit-env-rust-seed-forbidden
hosted_wm_capture_simple_bin_status=forbidden
```

### `--selftest` (fatal, runs before every scan)

Added `hwce_selftest`, invoked on `--selftest` and also silently before each real
scan, so the classifier cannot regress unnoticed. Repo verdict convention:
`PASS — <n> selftest fixture(s) checked, 0 failed` exit 0 / `FAIL` exit 1 /
`ERROR — nothing was checked` exit 2 (a run that checked 0 fixtures is an ERROR,
never a pass).

Five fixtures. (1) **reproducing**: seed-content binary at
`bin/release/<triple>/simple` — the exact deployed shape. (2)–(5)
**generalizing**, covering the whole defect class ("identity inferred from
location") in both directions so neither probe can be dropped without a red:
seed-by-path with no marker; a self-hosted binary that must **not** false-positive
(guards the direction this doc worried about); a symlink to a seed (the
`bin/simple` shape); an absent path, which must not crash the classifier.

Before/after proof — with only the content probe short-circuited (`if false &&
...`) and nothing else changed:

```
selftest FAIL: deployed-seed-outside-compiler_rust expected=seed got=hosted
selftest FAIL: symlink-to-seed expected=seed got=hosted
FAIL — 5 selftest fixture(s) checked, 2 failed          rc=1
```

and with the fix in place:

```
PASS — 5 selftest fixture(s) checked, 0 failed          rc=0
```

### Scope / not fixed here

`is_rust_seed_simple()` is **copy-pasted into 15+ sibling gate scripts**
(`check-wasm-hello-gui-package-evidence.shs`,
`check-electron-simple-web-layout-bitmap-evidence.shs`,
`check-gui-wasm-cli-artifact.shs`, `check-engine2d-gpu-offload-evidence.shs`,
`check-responsive-showcase-evidence.shs`,
`check-metal-engine2d-framebuffer-readback-evidence.shs`,
`check-macos-gui-live-window-evidence.shs`,
`check-tauri-ios-mobile-renderer-evidence.shs`, and more — enumerate with
`grep -rn is_rust_seed_simple scripts/`). **Every one of them is still
path-only and therefore still admits the deployed seed.** Only the file this row
names was changed, because concurrent lanes own the others. The real remedy is to
hoist the classifier into `scripts/lib/simple-compiler-select.shs` (already
sourced by all of them) and delete the copies; that is a separate, larger change
and is left open. **Status: this script fixed; family-wide duplication OPEN.**
