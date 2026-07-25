# Sanitizer Matrix Plan (C4)

Status: **planning**, independent of the stage4 wall (the wall is a seed-cranelift
codegen defect on the ANY-erased enum channel; sanitizers target memory/UB/race/uninit
defects in native code, an orthogonal concern). Tracked as task C4 in
`cert_roadmap.md` / `deferred_tasks_plan.md`. This doc specifies the plan; the CLI
(`scripts/check/cert/sanitizer-matrix.shs`) is **not implemented** by this plan.

## Scope

- **Rust seed:** `src/compiler_rust/**`, **excluding** `src/compiler_rust/vendor/**`
  (owned-code scope per `CLAUDE.md`). The seed is bootstrap-only tooling, never the
  shipped product, but it is a development-tool-integrity target: a memory-unsafe seed
  can silently corrupt the very bootstrap it produces.
- **C runtime:** `src/runtime/**`, **excluding** vendored `src/runtime/miniaudio.h`,
  `src/runtime/stb_image.h`, `src/runtime/stb_truetype.h`.
- Out of scope: the pure-Simple compiler/stdlib itself (no native UB surface to sanitize;
  covered instead by the optimization-soundness differential, C2) and all vendor trees.

## Per-sanitizer build matrix

| Sanitizer | Seed (Rust) flags | Runtime (C) flags | Isolated build dir |
|---|---|---|---|
| ASan (address) | `RUSTFLAGS="-Zsanitizer=address" cargo +nightly build` | `CFLAGS="-fsanitize=address -g -O1"` | `CARGO_TARGET_DIR=target/san-asan`; `build/runtime-san-asan` |
| TSan (thread) | `RUSTFLAGS="-Zsanitizer=thread" cargo +nightly build` | `CFLAGS="-fsanitize=thread -g -O1"` | `CARGO_TARGET_DIR=target/san-tsan`; `build/runtime-san-tsan` |
| MSan (memory/uninit) | `RUSTFLAGS="-Zsanitizer=memory" cargo +nightly build -Zbuild-std --target x86_64-unknown-linux-gnu` (MSan requires an instrumented std, hence `-Zbuild-std`) | `CFLAGS="-fsanitize=memory -fsanitize-memory-track-origins -g -O1"` | `CARGO_TARGET_DIR=target/san-msan`; `build/runtime-san-msan` |
| UBSan-equivalent | seed: `RUSTFLAGS="-C overflow-checks=on -C debug-assertions=on"` (Rust has no direct UBSan; overflow-checks + debug-assertions is the closest native equivalent for the seed) | `CFLAGS="-fsanitize=undefined -g -O1"` | `CARGO_TARGET_DIR=target/san-ubsan`; `build/runtime-san-ubsan` |

Each sanitizer gets its own isolated `CARGO_TARGET_DIR`/runtime build dir so runs are
parallelizable and a crash under one sanitizer never invalidates another's build cache.
Nightly Rust is required for `-Zsanitizer=*`/`-Zbuild-std`; pinned via the existing
bootstrap nightly-toolchain selection in `.claude/rules/bootstrap.md`.

## Suite selection per sanitizer

| Sanitizer | Suite | Mode |
|---|---|---|
| ASan | full `cargo test` (seed unit + integration) + runtime FFI specs | full (nightly cron) |
| TSan | seed concurrency-relevant unit tests + runtime FFI specs touching threads/actors | full (nightly cron) — TSan runs are slow, time-boxed |
| MSan | seed unit tests only (MSan + FFI-boundary C calls produces false positives without instrumenting the whole call graph) | smoke (weekly full) |
| UBSan-equiv | full `cargo test` + full runtime FFI specs | full (nightly cron) |

- **Smoke** = a fixed fast subset (bootstrap self-check + top-N most-exercised runtime FFI
  specs), run nightly, target < 15 min per sanitizer.
- **Full** = entire applicable suite per sanitizer above, run weekly (or on-demand before
  a redeploy), no fixed time box beyond the existing `BUILD_TIMEOUT`-style pattern used by
  `check-lean-proofs.shs`.

## Triage / waiver process

1. Any sanitizer finding is filed the same day it is observed (no batching).
2. **2-business-day SLA** to triage: classify as (a) real defect → fix, (b) false
   positive / known sanitizer limitation (e.g. MSan + uninstrumented libc FFI) → waiver,
   or (c) needs more investigation → stays open, re-triaged next business day.
3. Waivers are recorded in a ledger at `doc/08_tracking/cert/sanitizer_waivers.md`, one
   row per waiver: finding id/hash, sanitizer, file:line, justification, date granted,
   **expiry date (waiver_date + 90 days)**, owner.
4. **No blanket suppressions** (e.g. no repo-wide `.asanignore` covering a whole
   directory) — every waiver is scoped to a specific finding signature (stack hash or
   `file:line` + call context), never a path-level or sanitizer-level opt-out.
5. On expiry (90 days), the waiver is automatically stale: the next sanitizer run must
   either re-triage (fixed → remove row; still valid → renew with a new justification
   and new 90-day expiry) or the run is treated as a regression (fails the gate).

## CLI interface (spec only — not implemented here)

`scripts/check/cert/sanitizer-matrix.shs`:

```
sanitizer-matrix.shs --san <address|thread|memory|undefined|all>
                     --target <seed|runtime|all>
                     [--smoke | --full]           # default: --smoke
                     [--waivers-file <path>]        # default: doc/08_tracking/cert/sanitizer_waivers.md
                     [--report <path>]              # default: build/cert/sanitizer_report.md (gitignored)
```

- `--san all --target all --smoke` is the nightly-cron invocation.
- `--san all --target all --full` is the weekly-cron invocation.
- `--report` output format mirrors `check-req-traceability.shs`'s report style
  (Markdown, PASS/FAIL per sanitizer×target cell, waived findings listed separately from
  open findings so a waived-but-still-firing finding doesn't silently disappear).
- Exit code: nonzero if any unwaived finding exists under the selected `--san`/`--target`,
  matching the exit-code convention of `check-lean-proofs.shs` and
  `check-req-traceability.shs` (0 = clean, nonzero = action needed).

## Cron trigger

| Schedule | Invocation | Purpose |
|---|---|---|
| Nightly | `sanitizer-matrix.shs --san all --target all --smoke` | fast regression signal |
| Weekly | `sanitizer-matrix.shs --san all --target all --full` | full-suite sweep, catches slow-to-trigger races/leaks |

Both entries append to `cert_roadmap.md`'s deferred-task status row (C4) and gate into
`/cert_grade --gap`, per the existing execution-wiring convention in
`deferred_tasks_plan.md` § Execution wiring. Cron wiring itself (crontab entries or CI
schedule config) is out of scope for this plan — it is listed here as the trigger
contract the eventual script must satisfy, not a delivered mechanism.

## Acceptance criteria for C4 as a whole

- Clean (0 unwaived findings) under each of the four sanitizer configurations for both
  targets, OR every finding triaged with a fix or a live (non-expired), narrowly-scoped
  waiver in the ledger.
- No blanket suppressions ever introduced to reach "clean."
