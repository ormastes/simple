# `scripts/check/` mass fail-open: self-hosted claims measured against the Rust seed

- **Status:** OPEN
- **Date:** 2026-07-28
- **Severity:** High — green output from these checks is cited as evidence in plans and reports
- **Found by:** follow-up to `doc/08_tracking/todo/blocked_p1_audit_2026-07-28.md` §3 item C1
- **Fixed so far:** `scripts/check/check-f64-call-abi.shs` and
  `scripts/check/check-stage4-selfhost-parse-memory-multifile.shs`

## The pattern

```sh
SIMPLE="${SIMPLE_BIN:-bin/simple}"      # or SIMPLE_BINARY, PURE_SIMPLE_BIN, ...
```

The script's comments and printed output claim it verifies the **self-hosted /
pure-Simple** compiler, but it resolves through `bin/simple` and never verifies
the binary's identity. `bin/simple` currently resolves to the **Rust bootstrap
seed** (`bin/release/x86_64-unknown-linux-gnu/simple`), which self-identifies on
stderr via `src/compiler_rust/driver/src/seed_warning.rs`:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
```

There is no deployed pure-Simple binary right now, so every such script measures
the seed and prints a green result about the self-hosted compiler. For
`check-f64-call-abi.shs` this was tautological: the seed's f64 codegen is already
fixed and covered by cargo tests, so it was green by construction.

A second, compounding fail-open is common: an "I could not test this" condition
(missing executable, missing tool, empty output, `|| true`) exits 0.

## Scale

Across the 420 entries in `scripts/check/`:

| Metric | Count |
|---|---|
| `.shs` using `SIMPLE_BIN` / `SIMPLE_BINARY` | 142 |
| referencing `bin/simple` | 131 |
| claiming self-hosted / pure-Simple | 92 |
| actually grepping for the seed banner | 9 |
| **self-host claimers with NO identity check** | **~70** |

## Confirmed fail-open (claims self-hosted, no identity check, can exit 0 untested)

All paths relative to `scripts/check/`:

| File | Resolution | Fail-open evidence |
|---|---|---|
| `check-sspec-count-truthful.shs` | `BIN="${SIMPLE_BIN:-bin/simple}"` | `out=$("$BIN" test ... 2>&1 \|\| true)` |
| `check-gui-vulkan-window.shs` | `SIMPLE_BIN="${SIMPLE_BIN:-bin/simple}"` | `fail "error=missing_executable"; exit 0` |
| `check-wm-daemon-health-recovery-evidence.shs` | `GUI_BIN="${SIMPLE_BIN:-bin/simple}"` | comment "Re-run on the pure-Simple self-hosted binary once available"; probe `\|\| true` then `exit 0` |
| `check-web-baremetal-size-audit.shs` | `SIMPLE_BINARY="${SIMPLE_BINARY:-bin/simple}"` | `[ ! -x ] \|\| SKIP_NATIVE_BUILDS=1` silently skips all native builds |
| `native-smoke-matrix.shs` | `SIMPLE_BINARY="${SIMPLE_BINARY:-bin/simple}"` | error text says "set to a deployed pure-Simple compiler" but never checks; XFAIL bucket absorbs failures |
| `check-stage4-selfhost-parse-memory.shs` | `${STAGE4_PARSE_MEM_BINARY:-bin/simple}` | name claims "selfhost"; only `-x` test |
| `check-rocm-engine2d-font-readback.shs` | `${PURE_SIMPLE_BIN:-bin/simple}` | var named PURE; sha256-hashes the binary but never checks identity |
| `check-cross-app-glyph-consistency.shs` | `${SIMPLE_BIN:-bin/simple}` | `grep ... \|\| true` |
| `check-browser-interaction.shs` | `${SIMPLE_BIN:-bin/simple}` | `grep ... \|\| true` |
| `check-nvme-rv32-minimal-live.shs` | `${NVME_RV32_SIMPLE_BIN:-bin/simple}` | message says "self-hosted"; never verifies |
| `check-tauri-android-webview-proof.shs` | `${SIMPLE_BIN:-$ROOT_DIR/bin/simple}` | `test -f` only (not even `-x`) |
| `check-simple-2d-renderdoc-backend-equivalence.shs` | default `bin/simple` | `exit 0` at L29 |
| `check-engine2d-nomirror-fast-render-evidence.shs` | default `bin/simple` | `exit 0` at L79 |
| `check-widget-showcase-4k-200fps.shs` | autodetect | labels `bin/*` as `repo-bin` vs `self-hosted-release` — label only, no verification; `exit 0` at L15, L470 |
| `check-native-seed-parity.shs` | `${SIMPLE_BINARY:-bin/release/simple}` | compares seed-vs-native using the **same** binary for both sides |

Roughly 50 more GUI / electron / tauri / wm `*-evidence.shs` share the identical
pattern and are not individually enumerated here.

## Scripts that already do it right (use as the reference implementation)

`check-ui-cli-live-transport.shs:79`, `check-ui-cli-final-review.shs:88`
(`fail "recorded runtime identifies as Rust seed"`),
`check-bootstrap-essential-tools-smoke.shs:41`,
`check-hosted-wm-capture-evidence.shs:214`,
`check-phase2-low-memory-source-reclaim.shs:429`,
`build-macos-full-cli-gui-provenance.shs:136`,
`build-simpleos-arm64-desktop-engine2d-attested.shs:88`,
`cert/redeploy_gate/candidate_frontend_admission.shs:123`,
`lib/macos-gpu-trusted-build-admission.shs:329`,
`lib/simpleos-arm64-guest-source-fingerprint.shs:46`.

Outside `scripts/check/`: `scripts/os/build_fsexec_prod_ring3.shs:49` and
`scripts/os/socket_echo_loopback_gate.shs:132`
(`fail "refusing Rust bootstrap seed: $COMPILER"`),
`build_clang_disk.shs:70`, `simpleos-native-build.shs:92`.

Note: `check-bootstrap-portability.shs:84` and
`check-simpleos-qemu-host-gpu-2d.shs:1564` only *emit* the banner from a stub —
they are fixtures, not verifiers.

## CI gap

`.github/workflows/` has **zero** `SIMPLE_BIN` gating.
`build-binaries.yml:200` runs `./bin/simple_stage2 --version` but only prints it
(`--help || true`, `-c "print 42" || echo "Note: ..."`).

## Required fix shape

Per script, following `scripts/check/check-f64-call-abi.shs` as the template:

1. Resolve the target explicitly and print the `readlink -f` real path.
2. Capture `--version` with `2>&1` and reject the seed **before** any
   measurement: `case "$V" in *"bootstrap seed only"*|*"Rust-built Simple binary"*)`.
3. Every "could not test" outcome exits non-zero (that script uses exit 2 for
   untestable, exit 1 for a real regression, exit 0 only for a verified result).
4. Never treat empty output, a missing tool, or a swallowed `|| true` as a pass.

This is worth extracting into a shared helper (e.g.
`scripts/check/lib/require-self-hosted.shs`) rather than repeating ~70 times.
The fixes are **not** mechanically identical — the scripts differ in variable
name, in what they claim, and in where they exit 0 — so each needs review.

## Related fail-open defects found the same day

- `doc/08_tracking/bug/lint_does_not_detect_syntax_errors_2026-07-28.md` —
  `bin/simple lint` reports "all files clean" on files that do not parse.
- `doc/08_tracking/todo/workspace_root_guard_is_vacuous_in_ci_2026-07-28.md` —
  workspace root guard is vacuous in CI.

---

# Progress update — 2026-07-28 (second pass)

## Shared guard extracted

`scripts/check/lib/require-self-hosted.shs` (source it; do not exec it).
Semantics copied from `check-f64-call-abi.shs` so the two cannot drift.

| Function | Contract |
|---|---|
| `require_self_hosted TARGET [LABEL]` | resolves TARGET, prints `readlink -f` real path, captures `--version 2>&1`, rejects the seed banner; sets `SELF_HOSTED_BIN` / `SELF_HOSTED_REAL` / `SELF_HOSTED_VERSION`; exits 2 on anything unverified |
| `binary_is_seed PATH` | `0` = is the seed, `1` = is not, `2` = identity unverifiable |
| `require_distinct_binaries A B` | exit 2 if both sides are the same real file |
| `resolve_binary` / `real_path` / `require_tool` | small primitives |
| `check_untestable MSG` / `check_fail MSG` | exit 2 / exit 1 |

Exit contract everywhere: **0** = property actually measured on a verified
target, **1** = measured and wrong, **2** = UNTESTABLE (never 0).

## Fixed this pass

- **`check-native-seed-parity.shs` — the check that could not fail.** Both
  sides ran through one `$SIMPLE_BINARY` (`run` vs `native-build`), so a
  seed/native divergence was undetectable by construction, even though the
  header and the per-case reclassification notes all reason about a genuine
  Rust oracle. It now resolves **two** binaries: `$SIMPLE_BINARY` must be
  self-hosted (seed banner ⇒ exit 2) and `$SEED_BINARY` must actually *be* a
  seed (no banner ⇒ exit 2), and `require_distinct_binaries` backstops both.
  `run_seed()` now invokes `$SEED_BINARY`. The two identity requirements are
  mutually exclusive, so "same binary on both sides" is now unreachable.
  With no self-hosted binary deployed today it exits **2 (untestable)** rather
  than printing PASS.
- **`check-widget-showcase-4k-200fps.shs`** — `SIMPLE_BIN_SOURCE` was assigned
  `self-hosted-release` purely from the path pattern `bin/release/*`, which is
  exactly where the deployed **seed** lives, and the `rust-seed-forbidden` gate
  only matched `src/compiler_rust/*`. Added a real `--version` probe; reuses the
  script's existing `exit 1` + `rust-seed-simple-binary-forbidden` vocabulary,
  plus a new `simple-binary-identity-unverifiable` reason. Skipped under
  `PLAN_ONLY=1` (which measures nothing by design).
- **`check-rocm-engine2d-font-readback.shs`** — **the audit entry for this file
  was wrong.** It does *not* fail open: `simple_binary_is_valid` (from
  `cert/redeploy_gate/candidate_frontend_admission.shs`, sourced at L59) already
  rejects the seed banner. The real defect was diagnostic: the seed surfaced as
  the catch-all `pure-simple-admission-failed`. Now reports
  `rust-bootstrap-seed-not-self-hosted`.

## The `is_rust_seed_simple()` family — 42 scripts converted

43 scripts in `scripts/check/` define a local `is_rust_seed_simple()`. All 8
textual variants tested **only** the path pattern `src/compiler_rust/*`. The
deployed seed at `bin/release/<triple>/simple` matches none of them, so the
predicate answered "not a seed" for the seed and every self-hosted claim in
those scripts was asserted against it.

The function body was replaced in the 42 unguarded ones with a real identity
probe (path pattern **or** `--version` banner, `timeout`-guarded). Callers were
not touched — they already branch on this predicate and already fail on it.
Fail-closed details:

- executable but `--version` fails / is empty ⇒ **treated as seed** (forbidden);
- not executable / empty path ⇒ returns "not seed" so the caller's own
  pre-existing `missing` branch reports it (that branch also fails);
- `check-hosted-wm-capture-evidence.shs` (the 43rd) was left alone — it already
  checks the banner separately.

## Remaining: 29 scripts, NOT mechanical

Left deliberately unconverted; each needs individual review.

| Script | What makes it non-mechanical |
|---|---|
| `cert/cert-gate.shs`, `cert/fuzz-diff.shs`, `cert/soundness-diff.shs`, `cert/stress-suite.shs`, `cert/redeploy_gate/redeploy_gate.shs` | certification drivers with their own multi-binary admission pipeline; adding a second guard risks double-gating an already-gated flow |
| `check-freebsd-bootstrap-qemu.shs` | resolves binaries *inside a QEMU guest over SSH*; the guard runs on the host and cannot probe the guest binary |
| `native-smoke-matrix.shs`, `check-web-baremetal-size-audit.shs` | an XFAIL/skip bucket absorbs failures; needs a decision on which buckets become exit 2 |
| `check-sspec-count-truthful.shs`, `check-cross-app-glyph-consistency.shs`, `check-browser-interaction.shs` | swallow status with `\|\| true` at the measurement site, not the resolution site — two separate fixes |
| `check-gui-vulkan-window.shs`, `check-wm-daemon-health-recovery-evidence.shs`, `check-engine2d-nomirror-fast-render-evidence.shs`, `check-simple-2d-renderdoc-backend-equivalence.shs` | explicit `exit 0` on the missing-executable path; changing it flips the meaning of the whole script for callers |
| `check-stage4-selfhost-parse-memory{,-multifile}.shs`, `check-nvme-rv32-minimal-live.shs`, `check-tauri-android-webview-proof.shs` | bespoke env var names and no standard `ROOT_DIR` idiom |
| `check-native-consecutive-zero-arg-receiver.shs`, `check-native-immutable-fn-receiver.shs`, `check-cpu-hotloop-idiom.shs`, `check-seed-extern-registry.shs`, `check-test-runner-rss-batch.shs`, `check-hda-qemu.shs`, `check-gtk-gui-size-speed-baseline.shs`, `check-linux-hosted-wm-live-window-evidence.shs`, `check-simpleos-wm-fullscreen-evidence.shs`, `check-wm-production-fullscreen-evidence.shs`, `produce-aetheric-host-web-gui-evidence.shs` | require `SIMPLE_BIN` to be set with no default; the fail-open is subtler (what the *caller* passes), so the guard belongs at the call sites too |

Note `check-seed-extern-registry.shs` legitimately targets the seed — it must
**not** get a self-hosted guard.

## CI — confirmed running a self-hosted check against the seed

`.github/workflows/rust-bootstrap-multiplatform.yml:310-320`, step
**"Run Rust-seed custom enum identity parity"**:

```yaml
seed="src/compiler_rust/target/bootstrap/simple"
SIMPLE_BINARY="$seed" ... sh scripts/check/check-native-seed-parity.shs
```

CI explicitly pointed the seed-vs-native parity harness at **the seed**, so both
sides were the same binary and the step was green by construction. This is the
CI instance of exactly the defect above.

**This step will now exit 2 and turn that job red.** That is the correct
fail-closed outcome, but the resolution is a judgement call and was NOT made
here:

1. delete the step (it never compared two compilers), or
2. keep the seed's own interpret-vs-native-build coverage under an honest name
   (e.g. `check-native-backend-selfconsistency.shs`) taking a single binary and
   claiming only self-consistency.

The `SIMPLE_BINARY="$stage3"` invocations (L392, L406, L418, L431) are fine and
become genuinely meaningful — stage3 is self-hosted and the seed oracle is
present in that job.

Still open: `.github/workflows/` has no `SIMPLE_BIN` gating for the ~50 GUI
evidence scripts; whether CI ever runs them with a seed was not established
(only `check-gui-hardening-open-gates.shs` is invoked from a workflow).

## Recovery update — 2026-08-16

`check-sspec-count-truthful.shs` is no longer part of the remaining fail-open
set. It now sources the canonical `require-self-hosted.shs` guard and admits the
selected runner before executing a spec. The runner invocation preserves its
exit status; any nonzero result fails the check instead of being converted to a
successful count comparison. Missing summary output and declared/reported count
mismatches remain failures.

Focused shell syntax and source-contract checks passed. No Simple test command
was run: pushed state has no admitted current-source Stage 4 CLI, and the
tracked `release/x86_64-unknown-linux-gnu/simple` is the known stale artifact
with SHA-256 `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`.
It is not acceptable test evidence for this criterion.
