# `scripts/check/` mass fail-open: self-hosted claims measured against the Rust seed

- **Status:** OPEN
- **Date:** 2026-07-28
- **Severity:** High — green output from these checks is cited as evidence in plans and reports
- **Found by:** follow-up to `doc/08_tracking/todo/blocked_p1_audit_2026-07-28.md` §3 item C1
- **Fixed so far:** `scripts/check/check-f64-call-abi.shs` only

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
| `check-stage4-selfhost-parse-memory-multifile.shs` | `${STAGE4_PARSE_MEM_MULTI_BINARY:-bin/simple}` | same |
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
